use crate::transform::{MirPass, MirSource};
use rustc::mir::*;
use rustc::ty::{self, TyCtxt};
use rustc_target::spec::abi::Abi;

pub struct LowerIntrinsics;

impl<'tcx> MirPass<'tcx> for LowerIntrinsics {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, src: MirSource<'tcx>, body: &mut BodyCache<'tcx>) {
        debug!("LowerIntrinsics - simplifying {:?}", body);

        let param_env = tcx.param_env(src.def_id());

        let (bbs, local_decls) = body.basic_blocks_and_local_decls_mut();
        for bb in bbs.indices() {
            let bb = &mut bbs[bb];
            if let Some(terminator) = &mut bb.terminator {
                if let TerminatorKind::Call {
                    func: Operand::Constant(func),
                    args,
                    destination: dest,
                    ..
                } = &terminator.kind
                {
                    if let ty::FnDef(def_id, substs) = func.literal.ty.kind {
                        let abi = tcx.fn_sig(def_id).abi();
                        let name = tcx.item_name(def_id);
                        if abi == Abi::RustIntrinsic {
                            match &*name.as_str() {
                                "discriminant_value" => match &args[0] {
                                    Operand::Copy(src) | Operand::Move(src) => {
                                        let (dest, target) = dest.as_ref().unwrap();
                                        let discr = Rvalue::Discriminant(tcx.mk_place_deref(src.clone()));
                                        let tmp = local_decls.push(LocalDecl {
                                            mutability: Mutability::Mut,
                                            ty: discr.ty(local_decls, tcx),
                                            user_ty: UserTypeProjections::none(),
                                            source_info: terminator.source_info,
                                            internal: true,
                                            local_info: LocalInfo::Other,
                                            is_block_tail: None,
                                        });
                                        bb.statements.push(Statement {
                                            source_info: terminator.source_info,
                                            kind: StatementKind::StorageLive(tmp),
                                        });
                                        bb.statements.push(Statement {
                                            source_info: terminator.source_info,
                                            kind: StatementKind::Assign(box (Place::from(tmp), discr)),
                                        });
                                        bb.statements.push(Statement {
                                            source_info: terminator.source_info,
                                            kind: StatementKind::Assign(box (
                                                dest.clone(),
                                                Rvalue::Cast(
                                                    CastKind::Misc,
                                                    Operand::Move(Place::from(tmp)),
                                                    dest.ty(local_decls, tcx).ty,
                                                ),
                                            )),
                                        });
                                        bb.statements.push(Statement {
                                            source_info: terminator.source_info,
                                            kind: StatementKind::StorageDead(tmp),
                                        });
                                        terminator.kind = TerminatorKind::Goto { target: *target };
                                    }
                                    _ => (),
                                },
                                "size_of" => {
                                    let ty = substs.type_at(0);
                                    if let Ok(layout) = tcx.layout_of(param_env.and(ty)) {
                                        let (dest, target) = dest.clone().unwrap();
                                        replace_layout_intrinsic(
                                            tcx,
                                            bb,
                                            target,
                                            dest,
                                            layout.size.bytes(),
                                        );
                                    }
                                }
                                "size_of_val" => {
                                    let ty = match &args[0] {
                                        Operand::Copy(src) |
                                        Operand::Move(src) => src.ty(local_decls, tcx).ty,
                                        Operand::Constant(c) => c.literal.ty,
                                    };
                                    if let Some(size) = tcx
                                        .layout_of(param_env.and(ty))
                                            .ok()
                                            .map(|layout| layout.size.bytes())
                                    {
                                        let (dest, target) = dest.clone().unwrap();
                                        replace_layout_intrinsic(
                                            tcx, bb, target, dest, size,
                                        );
                                    }
                                }
                                "forget" => {
                                    let (_, target) = dest.as_ref().unwrap();
                                    terminator.kind = TerminatorKind::Goto { target: *target };
                                }
                                "offset" => {
                                    let (dest, target) = dest.clone().unwrap();
                                    bb.statements.push(Statement {
                                        source_info: terminator.source_info,
                                        kind: StatementKind::Assign(box (
                                            dest,
                                            Rvalue::BinaryOp(
                                                BinOp::Offset,
                                                args[0].clone(),
                                                args[1].clone(),
                                            ),
                                        )),
                                    });
                                    terminator.kind = TerminatorKind::Goto { target };
                                }
                                "unreachable" => {
                                    terminator.kind = TerminatorKind::Unreachable;
                                }
                                _ => (),
                            }
                        }
                    }
                }
            }
        }
    }
}

fn replace_layout_intrinsic<'tcx>(
    tcx: TyCtxt<'tcx>,
    bb: &mut BasicBlockData<'tcx>,
    target: BasicBlock,
    dest: Place<'tcx>,
    value: u64,
) {
    if let Some(terminator) = &mut bb.terminator {
        bb.statements.push(Statement {
            source_info: terminator.source_info,
            kind: StatementKind::Assign(box (
                dest,
                Rvalue::Use(Operand::Constant(box Constant {
                    span: terminator.source_info.span,
                    literal: ty::Const::from_usize(tcx, value),
                    user_ty: None,
                })),
            )),
        });
        terminator.kind = TerminatorKind::Goto { target };
    }
}
