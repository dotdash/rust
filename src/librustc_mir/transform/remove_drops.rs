// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use pretty;
use rustc::ty::TyCtxt;
use rustc::mir::repr::*;
use rustc::mir::transform::{MirPass, MirSource, Pass};

use super::predecessor_map::*;

pub struct RemoveDrops;

impl<'tcx> MirPass<'tcx> for RemoveDrops {
    fn run_pass<'a>(&mut self, tcx: TyCtxt<'a, 'tcx, 'tcx>, src: MirSource, mir: &mut Mir<'tcx>) {
        loop {
        let mut changed = false;
        let predecessor_map = build_predecessor_map(mir);
        for cur_bb in mir.all_basic_blocks() {
            // Temporarily take ownership of the terminator we're modifying to keep borrowck happy
            debug!("Visiting block: {:?}", cur_bb);
            let replacement = match mir.basic_block_data(cur_bb).terminator().kind {
                TerminatorKind::Drop { value: ref droppee, target, .. } => {
                    let mut replacement = Some(TerminatorKind::Goto { target: target });
                    let mut worklist = Vec::with_capacity(4);
                    let mut seen = Vec::with_capacity(8);
                    worklist.push(cur_bb);
                    'work: while let Some(bb) = worklist.pop() {
                        debug!("Looking at block: {:?}", bb);
                        if seen.contains(&bb) {
                            debug!("Already saw block: {:?}", bb);
                            continue;
                        }
                        seen.push(bb);
                        let data = mir.basic_block_data(bb);
                        match data.terminator().kind {
                            TerminatorKind::Resume |
                            TerminatorKind::Goto { .. } |
                            TerminatorKind::If { .. } |
                            TerminatorKind::Switch { .. } |
                            TerminatorKind::SwitchInt { .. } |
                            TerminatorKind::Return => {
                                // Nothing to do
                            }
                            TerminatorKind::Drop { ref value, .. } => {
                                if value == droppee && cur_bb != bb {
                                    continue;
                                }
                            }
                            TerminatorKind::Call { ref args, ref destination, .. } => {
                                if let Some(ref destination) = *destination {
                                    if destination.0 == *droppee {
                                        replacement = None;
                                        break 'work;
                                    }
                                }

                                for arg in args {
                                    if let Operand::Consume(ref c) = *arg {
                                        if c == droppee {
                                            debug!("Found {:?}", arg);
                                            continue 'work;
                                        }
                                    }
                                }
                            }
                        }
                        for statement in data.statements.iter().rev() {
                            match statement.kind {
                                StatementKind::Assign(ref lvalue, ref rvalue) => {
                                    if lvalue == droppee {
                                        debug!("Assignment to droppee in {:?}", statement);
                                        replacement = None;
                                        break 'work;
                                    }
                                    match *rvalue {
                                        Rvalue::Ref(..) |
                                        Rvalue::Len(..) |
                                        Rvalue::Box(..) |
                                        Rvalue::Slice { .. } => {}
                                        Rvalue::Cast(_, ref oper, _) |
                                        Rvalue::UnaryOp(_, ref oper) |
                                        Rvalue::Repeat(ref oper, _) |
                                        Rvalue::Use(ref oper) => {
                                            if let Operand::Consume(ref c) = *oper {
                                                if c == droppee {
                                                    debug!("Use in {:?}", rvalue);
                                                    continue 'work;
                                                }
                                            }
                                        }
                                        Rvalue::BinaryOp(_, ref oper1, ref oper2) => {
                                            if let Operand::Consume(ref c) = *oper1 {
                                                if c == droppee {
                                                    debug!("Use in {:?}", rvalue);
                                                    continue 'work;
                                                }
                                            }
                                            if let Operand::Consume(ref c) = *oper2 {
                                                if c == droppee {
                                                    debug!("Use in {:?}", rvalue);
                                                    continue 'work;
                                                }
                                            }
                                        }
                                        Rvalue::Aggregate(_, ref opers) => {
                                            for oper in opers {
                                                if let Operand::Consume(ref c) = *oper {
                                                    if c == droppee {
                                                        debug!("Use in {:?}", rvalue);
                                                        continue 'work;
                                                    }
                                                }
                                            }
                                        }
                                        Rvalue::InlineAsm { ref outputs, ref inputs, .. } => {
                                            for output in outputs {
                                                if output == droppee {
                                                    debug!("Assignment to droppee in {:?}", rvalue);
                                                    replacement = None;
                                                    break 'work;
                                                }
                                            }
                                            for input in inputs {
                                                if let Operand::Consume(ref c) = *input {
                                                    if c == droppee {
                                                        debug!("Use in {:?}", rvalue);
                                                        continue 'work;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        let predecessors = predecessor_map.predecessors(bb);
                        if predecessors.is_empty() {
                            debug!("Reached function start");
                            continue 'work;
                        }

                        worklist.extend(predecessors);
                    }
                    replacement
                },
                _ => None
            };
            debug!("Setting terminator in block: {:?}", cur_bb);
            if let Some(replacement) = replacement {
                changed = true;
                mir.basic_block_data_mut(cur_bb).terminator_mut().kind = replacement;
            }
        }
        if !changed {
            break;
        }
        }
        pretty::dump_mir(tcx, "remove_drops", &0, src, mir, None);
    }
}

impl Pass for RemoveDrops {}
