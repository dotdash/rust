//! Trivial copy propagation pass.
//!
//! This uses def-use analysis to remove values that have exactly one def and one use, which must
//! be an assignment.
//!
//! To give an example, we look for patterns that look like:
//!
//!     DEST = SRC
//!     ...
//!     USE(DEST)
//!
//! where `DEST` and `SRC` are both locals of some form. We replace that with:
//!
//!     NOP
//!     ...
//!     USE(SRC)
//!
//! The assignment `DEST = SRC` must be (a) the only mutation of `DEST` and (b) the only
//! (non-mutating) use of `SRC`. These restrictions are conservative and may be relaxed in the
//! future.

#![allow(dead_code)]
#![allow(unreachable_code)]
#![allow(unused_variables)]

use rustc::mir::{Constant, Local, LocalKind, Location, Place, Mir, Operand, Rvalue, StatementKind};
use rustc::mir::visit::MutVisitor;
use rustc::ty::TyCtxt;
use transform::{MirPass, MirSource};
use util::def_use::DefUseAnalysis;

pub struct CopyPropagation;

impl MirPass for CopyPropagation {
    fn run_pass<'a, 'tcx>(&self,
                          tcx: TyCtxt<'a, 'tcx, 'tcx>,
                          _source: MirSource,
                          mir: &mut Mir<'tcx>) {
        // We only run when the MIR optimization level is > 1.
        // This avoids a slow pass, and messing up debug info.
        if tcx.sess.opts.debugging_opts.mir_opt_level < 1 {
            return;
        }

        let mut def_use_analysis = DefUseAnalysis::new(mir);
        def_use_analysis.analyze(mir);
        loop {
            let mut changed = false;
            for dest_local in mir.local_decls.indices() {
                debug!("Considering destination local: {:?}", dest_local);

                let action;
                let location;
                {
                    // The destination must have exactly one def.
                    let dest_use_info = def_use_analysis.local_info(dest_local);
                    let dest_def_count = dest_use_info.def_count_not_including_drop();
                    if dest_def_count == 0 {
                        debug!("  Can't copy-propagate local: dest {:?} undefined",
                               dest_local);
                        continue
                    }
                    if dest_def_count > 1 {
                        debug!("  Can't copy-propagate local: dest {:?} defined {} times",
                               dest_local,
                               dest_use_info.def_count());
                        continue
                    }
                    if dest_use_info.use_count() == 0 {
                        debug!("  Can't copy-propagate local: dest {:?} unused",
                               dest_local);
                        continue
                    }
                    // Conservatively gives up if the dest is an argument,
                    // because there may be uses of the original argument value.
                    if mir.local_kind(dest_local) == LocalKind::Arg {
                        debug!("  Can't copy-propagate local: dest {:?} (argument)",
                            dest_local);
                        continue;
                    }
                    let dest_place_def = dest_use_info.defs_not_including_drop().next().unwrap();
                    location = dest_place_def.location;

                    let basic_block = &mir[location.block];
                    let statement_index = location.statement_index;
                    let statement = match basic_block.statements.get(statement_index) {
                        Some(statement) => statement,
                        None => {
                            debug!("  Can't copy-propagate local: used in terminator");
                            continue
                        }
                    };

                    // That use of the source must be an assignment.
                    match statement.kind {
                        StatementKind::Assign(Place::Local(local), box Rvalue::Use(ref operand)) if
                                local == dest_local => {
                            let maybe_action = match *operand {
                                Operand::Copy(ref src_place) |
                                Operand::Move(ref src_place) => {
                                    Action::local_copy(&mir, &mut def_use_analysis, src_place)
                                }
                                Operand::Constant(ref src_constant) => {
                                    Action::constant(src_constant)
                                }
                            };
                            match maybe_action {
                                Some(this_action) => action = this_action,
                                None => continue,
                            }
                        }
                        _ => {
                            debug!("  Can't copy-propagate local: source use is not an \
                                    assignment");
                            continue
                        }
                    }
                }

                changed = action.perform(mir, &mut def_use_analysis, dest_local, location) || changed;
            }
            if !changed {
                break
            }
        }
    }
}

enum Action<'tcx> {
    PropagateLocalCopy(Local),
    PropagateConstant(Constant<'tcx>),
}

impl<'tcx> Action<'tcx> {
    fn local_copy(mir: &Mir<'tcx>, def_use_analysis: &mut DefUseAnalysis, src_place: &Place<'tcx>)
                  -> Option<Action<'tcx>> {
        // The source must be a local.
        let src_local = if let Place::Local(local) = *src_place {
            local
        } else {
            debug!("  Can't copy-propagate local: source is not a local");
            return None;
        };

        // We're trying to copy propagate a local.
        // There must be exactly one use of the source used in a statement (not in a terminator).
        let src_use_info = def_use_analysis.local_info(src_local);
        let src_use_count = src_use_info.use_count();
        if src_use_count == 0 {
            debug!("  Can't copy-propagate local: no uses");
            return None
        }
        if src_use_count != 1 {
            debug!("  Can't copy-propagate local: {} uses", src_use_info.use_count());
            return None
        }

        // Verify that the source doesn't change in between. This is done conservatively for now,
        // by ensuring that the source has exactly one mutation. The goal is to prevent things
        // like:
        //
        //     DEST = SRC;
        //     SRC = X;
        //     USE(DEST);
        //
        // From being misoptimized into:
        //
        //     SRC = X;
        //     USE(SRC);
        let src_def_count = src_use_info.def_count_not_including_drop();
        // allow function arguments to be propagated
        let is_arg = mir.local_kind(src_local) == LocalKind::Arg;
        if (is_arg && src_def_count != 0) || (!is_arg && src_def_count != 1) {
            debug!(
                "  Can't copy-propagate local: {} defs of src{}",
                src_def_count,
                if is_arg { " (argument)" } else { "" },
            );
            return None
        }

        Some(Action::PropagateLocalCopy(src_local))
    }

    fn constant(src_constant: &Constant<'tcx>) -> Option<Action<'tcx>> {
        Some(Action::PropagateConstant((*src_constant).clone()))
    }

    fn perform(self,
               mir: &mut Mir<'tcx>,
               def_use_analysis: &mut DefUseAnalysis<'tcx>,
               dest_local: Local,
               location: Location)
               -> bool {
        match self {
            Action::PropagateLocalCopy(src_local) => {
                // Eliminate the destination and the assignment.
                //
                // First, remove all markers.
                //
                // FIXME(pcwalton): Don't do this. Merge live ranges instead.
                debug!("  Replacing all uses of {:?} with {:?} (local)",
                       dest_local,
                       src_local);
                for place_use in &def_use_analysis.local_info(dest_local).defs_and_uses {
                    if place_use.context.is_storage_marker() {
                        mir.make_statement_nop(place_use.location)
                    }
                }
                for place_use in &def_use_analysis.local_info(src_local).defs_and_uses {
                    if place_use.context.is_storage_marker() {
                        mir.make_statement_nop(place_use.location)
                    }
                }

                // Replace all uses of the destination local with the source local.
                def_use_analysis.replace_all_defs_and_uses_with(dest_local, mir, src_local);

                // Finally, zap the now-useless assignment instruction.
                debug!("  Deleting assignment");
                mir.make_statement_nop(location);

                false
            }
            Action::PropagateConstant(src_constant) => {
                // First, remove all markers.
                //
                // FIXME(pcwalton): Don't do this. Merge live ranges instead.
                debug!("  Replacing all uses of {:?} with {:?} (constant)",
                       dest_local,
                       src_constant);
                let dest_local_info = def_use_analysis.local_info(dest_local);
                for place_use in &dest_local_info.defs_and_uses {
                    if place_use.context.is_storage_marker() {
                        mir.make_statement_nop(place_use.location)
                    }
                }

                // Replace all uses of the destination local with the constant.
                let mut visitor = ConstantPropagationVisitor::new(dest_local,
                                                                  src_constant);
                for dest_place_use in &dest_local_info.defs_and_uses {
                    visitor.visit_location(mir, dest_place_use.location)
                }

                // Zap the assignment instruction if we eliminated all the uses. We won't have been
                // able to do that if the destination was used in a projection, because projections
                // must have places on their LHS.
                let use_count = dest_local_info.use_count();
                if visitor.uses_replaced == use_count {
                    debug!("  {} of {} use(s) replaced; deleting assignment",
                           visitor.uses_replaced,
                           use_count);
                    mir.make_statement_nop(location);
                    true
                } else if visitor.uses_replaced == 0 {
                    debug!("  No uses replaced; not deleting assignment");
                    false
                } else {
                    debug!("  {} of {} use(s) replaced; not deleting assignment",
                           visitor.uses_replaced,
                           use_count);
                    true
                }
            }
        }
    }
}

struct ConstantPropagationVisitor<'tcx> {
    dest_local: Local,
    constant: Constant<'tcx>,
    uses_replaced: usize,
}

impl<'tcx> ConstantPropagationVisitor<'tcx> {
    fn new(dest_local: Local, constant: Constant<'tcx>)
           -> ConstantPropagationVisitor<'tcx> {
        ConstantPropagationVisitor {
            dest_local,
            constant,
            uses_replaced: 0,
        }
    }
}

impl<'tcx> MutVisitor<'tcx> for ConstantPropagationVisitor<'tcx> {
    fn visit_operand(&mut self, operand: &mut Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);

        match *operand {
            Operand::Copy(Place::Local(local)) |
            Operand::Move(Place::Local(local)) if local == self.dest_local => {}
            _ => return,
        }

        *operand = Operand::Constant(box self.constant.clone());
        self.uses_replaced += 1
    }
}
