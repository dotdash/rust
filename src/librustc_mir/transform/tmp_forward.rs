// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use pretty::dump_mir;
use rustc::ty::TyCtxt;
use rustc::mir::repr::*;
use rustc::mir::transform::{MirPass, MirSource, Pass};
use rustc::mir::visit::{LvalueContext, MutVisitor, Visitor};
use rustc_data_structures::bitvec::BitVector;

pub struct TmpForward;

struct TempCollector {
    uses: Vec<u32>,
}

impl<'tcx> Visitor<'tcx> for TempCollector {
    fn visit_lvalue(&mut self, lvalue: &Lvalue<'tcx>, context: LvalueContext) {
        self.super_lvalue(lvalue, context);
        if let &Lvalue::Temp(idx) = lvalue {
            self.uses[idx as usize] += 1;
        }
    }

    fn visit_terminator_kind(&mut self, block: BasicBlock, kind: &TerminatorKind<'tcx>) {
        // Being dropped shouldn't increment the usage count
        match *kind {
            TerminatorKind::Drop { target, unwind, .. } => {
                self.visit_branch(block, target);
                unwind.map(|t| self.visit_branch(block, t));
            }
            _ => self.super_terminator_kind(block, kind)
        }
    }
}

struct Promoter {
    uses: Vec<u32>,
    dead: BitVector,
}

impl<'tcx> MutVisitor<'tcx> for Promoter {
    fn visit_basic_block_data(&mut self, _: BasicBlock, data: &mut BasicBlockData<'tcx>) {
        loop {
            let mut dropped = 0;
            let mut replacement = None;
            for i in 0..data.statements.len() {
                if let Some((idx, rvalue)) = replacement {
                    let StatementKind::Assign(_, ref mut r) = data.statements[i].kind;
                    if let Rvalue::Use(op) = rvalue {
                        for op2 in r.operands_mut() {
                            if let Operand::Consume(Lvalue::Temp(idx2)) = *op2 {
                                if idx == idx2 {
                                    *op2 = op;
                                    dropped += 1;
                                    self.dead.insert(idx as usize);
                                    break;
                                }
                            }
                        }
                    } else if let Rvalue::Use(Operand::Consume(Lvalue::Temp(idx2))) = *r {
                        if idx == idx2 {
                            *r = rvalue;
                            dropped += 1;
                            self.dead.insert(idx as usize);
                        }
                    }
                }

                replacement = None;
                if let StatementKind::Assign(Lvalue::Temp(idx), ref r) = data.statements[i].kind {
                    if self.uses[idx as usize] == 2 {
                        replacement = Some((idx, r.clone()));
                    }
                }

                if dropped > 0 {
                    data.statements.swap(i, i - dropped);
                }
            }

            if let Some((idx, Rvalue::Use(oper))) = replacement {
                match data.terminator_mut().kind {
                    TerminatorKind::If { cond: ref mut oper2, .. } |
                        TerminatorKind::Call { func: ref mut oper2, .. } => {
                            if let Operand::Consume(Lvalue::Temp(idx2)) = *oper2 {
                                if idx == idx2 {
                                    *oper2 = oper;
                                    dropped += 1;
                                    self.dead.insert(idx as usize);
                                }
                            }
                        }
                    _ => {}
                }
            }
            let len = data.statements.len() - dropped;
            data.statements.truncate(len);
            if dropped == 0 {
                break;
            }
        }

    }
}

struct Updater {
    dead: BitVector,
    replacements: Vec<usize>,
}

impl<'tcx> MutVisitor<'tcx> for Updater {
    fn visit_lvalue(&mut self, lvalue: &mut Lvalue<'tcx>, context: LvalueContext) {
        self.super_lvalue(lvalue, context);
        if let &mut Lvalue::Temp(ref mut idx) = lvalue {
            *idx = self.replacements[*idx as usize] as u32;
        }
    }

    fn visit_terminator_kind(&mut self, block: BasicBlock, kind: &mut TerminatorKind<'tcx>) {
        // Being dropped shouldn't increment the usage count
        if let TerminatorKind::Drop { value: Lvalue::Temp(idx), target, .. } = *kind {
            if self.dead.contains(idx as usize) {
                *kind = TerminatorKind::Goto { target: target };
            }
        }
        self.super_terminator_kind(block, kind)
    }
}

impl<'tcx> MirPass<'tcx> for TmpForward {
    fn run_pass<'a>(&mut self, tcx: TyCtxt<'a, 'tcx, 'tcx>, src: MirSource, mir: &mut Mir<'tcx>) {
        let mut collector = TempCollector {
            uses: vec![0; mir.temp_decls.len()],
        };
        collector.visit_mir(mir);

        let mut p = Promoter {
            uses: collector.uses,
            dead: BitVector::new(mir.temp_decls.len()),
        };
        p.visit_mir(mir);

        let mut replacements: Vec<_> = (0..mir.temp_decls.len()).collect();
        let mut used_temps = 0;

        for alive_index in 0..mir.temp_decls.len() {
            if p.dead.contains(alive_index) {
                continue;
            }

            replacements[alive_index] = used_temps;
            if alive_index != used_temps {
                // Swap the next alive block data with the current available slot. Since alive_index is
                // non-decreasing this is a valid operation.
                mir.temp_decls.swap(alive_index, used_temps);
            }
            used_temps += 1;
        }

        Updater { dead: p.dead, replacements: replacements }.visit_mir(mir);
        mir.temp_decls.truncate(used_temps);

        dump_mir(tcx, "tmp_elim", &0, src, mir, None);
    }
}

impl Pass for TmpForward {}
