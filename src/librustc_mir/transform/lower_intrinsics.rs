use rustc_target::spec::abi::Abi;
use rustc::ty::{self, TyCtxt};
use rustc::mir::*;
use crate::transform::{MirPass, MirSource};

pub struct LowerIntrinsics;

impl MirPass for LowerIntrinsics {
    fn run_pass<'a, 'tcx>(&self,
                          tcx: TyCtxt<'a, 'tcx, 'tcx>,
                          src: MirSource<'tcx>,
                          mir: &mut Mir<'tcx>) {
        debug!("LowerIntrinsics - simplifying {:?}", mir);

        let param_env = tcx.param_env(src.def_id());

        let (bbs, local_decls) = mir.basic_blocks_and_local_decls_mut();
        for bb in bbs.indices() {
            let bb = &mut bbs[bb];
            if let Some(terminator) = &mut bb.terminator {
                if let TerminatorKind::Call { func: ref oper, ref args, destination: ref dest , .. } = terminator.kind {
                    if let Operand::Constant(ref func) = *oper {
                        if let ty::FnDef(def_id, substs) = func.ty.sty {
                            let abi = tcx.fn_sig(def_id).abi();
                            let name = tcx.item_name(def_id);
                            if abi == Abi::RustIntrinsic {
                                match &*name.as_str() {
                                    "discriminant_value" => {
                                        match &args[0] {
                                            Operand::Copy(src) | Operand::Move(src) => {
                                                let (dest, target) = dest.as_ref().unwrap();
                                                let discr = Rvalue::Discriminant(src.clone().deref());
                                                let tmp = local_decls.push(LocalDecl {
                                                    mutability: Mutability::Mut,
                                                    ty: discr.ty(local_decls, tcx),
                                                    user_ty: UserTypeProjections::none(),
                                                    name: None,
                                                    source_info: terminator.source_info,
                                                    visibility_scope: terminator.source_info.scope,
                                                    internal: true,
                                                    is_user_variable: None,
                                                    is_block_tail: None,
                                                });
                                                let tmp = Place::Base(PlaceBase::Local(tmp));
                                                bb.statements.push(Statement {
                                                    source_info: terminator.source_info,
                                                    kind: StatementKind::Assign(tmp.clone(), box discr),
                                                });
                                                bb.statements.push(Statement {
                                                    source_info: terminator.source_info,
                                                    kind: StatementKind::Assign(dest.clone(), box Rvalue::Cast(CastKind::Misc, Operand::Move(tmp), dest.ty(local_decls, tcx).ty)),
                                                });
                                                terminator.kind = TerminatorKind::Goto { target: *target };
                                            }
                                            _ => ()
                                        }
                                    }
                                    "size_of" => {
                                        let ty = substs.type_at(0);
                                        if let Ok(layout) = tcx.layout_of(param_env.and(ty)) {
                                            let (dest, target) = dest.clone().unwrap();
                                            replace_layout_intrinsic(tcx, bb, target, dest, layout.size.bytes());
                                        }
                                    }
                                    "size_of_val" => {
                                        match &args[0] {
                                            Operand::Copy(src) | Operand::Move(src) => {
                                                let ty = src.clone().deref().ty(local_decls, tcx).ty;
                                                if let Some(size) = tcx.layout_of(param_env.and(ty)).ok().map(|layout| layout.size.bytes()) {
                                                    let (dest, target) = dest.clone().unwrap();
                                                    replace_layout_intrinsic(tcx, bb, target, dest, size);
                                                }
                                            }
                                            _ => (),
                                        };
                                    }
                                    "forget" => {
                                        let (_, target) = dest.as_ref().unwrap();
                                        terminator.kind = TerminatorKind::Goto { target: *target };
                                    }
                                    "offset" => {
                                        let (dest, target) = dest.clone().unwrap();
                                        bb.statements.push(Statement {
                                            source_info: terminator.source_info,
                                            kind: StatementKind::Assign(dest, box Rvalue::BinaryOp(BinOp::Offset, args[0].clone(), args[1].clone())),
                                        });
                                        terminator.kind = TerminatorKind::Goto { target: target };
                                    }
                                    "unreachable" => {
                                        terminator.kind = TerminatorKind::Unreachable;
                                    }
                                    _ => ()
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

fn replace_layout_intrinsic<'tcx>(tcx: TyCtxt<'_, 'tcx, 'tcx>, bb: &mut BasicBlockData<'tcx>, target: BasicBlock, dest: Place<'tcx>, value: u64) {
    if let Some(terminator) = &mut bb.terminator {
        bb.statements.push(Statement {
            source_info: terminator.source_info,
            kind: StatementKind::Assign(dest, box Rvalue::Use(Operand::Constant(box Constant {
                span: terminator.source_info.span,
                ty: tcx.types.usize,
                literal: ty::Const::from_usize(tcx, value),
                user_ty: None,
            }))),
        });
        terminator.kind = TerminatorKind::Goto { target: target };
    }
}
