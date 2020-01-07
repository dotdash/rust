use crate::deriving::generic::ty::*;
use crate::deriving::generic::*;
use crate::deriving::{path_local, path_std};

use rustc_expand::base::{Annotatable, ExtCtxt};
use rustc_span::symbol::sym;
use rustc_span::Span;
use syntax::ast::{BinOpKind, Expr, Ident, MetaItem};
use syntax::attr;
use syntax::ptr::P;

pub fn expand_deriving_partial_eq(
    cx: &mut ExtCtxt<'_>,
    span: Span,
    mitem: &MetaItem,
    item: &Annotatable,
    push: &mut dyn FnMut(Annotatable),
) {
    // structures are equal if all fields are equal, and non equal, if
    // any fields are not equal or if the enum variants are different
    fn cs_op(
        cx: &mut ExtCtxt<'_>,
        span: Span,
        substr: &Substructure<'_>,
        op: BinOpKind,
        combiner: BinOpKind,
        base: bool,
    ) -> P<Expr> {
        let op = |cx: &mut ExtCtxt<'_>, span: Span, self_f: P<Expr>, other_fs: &[P<Expr>]| {
            let other_f = match other_fs {
                [o_f] => o_f,
                _ => cx.span_bug(span, "not exactly 2 arguments in `derive(PartialEq)`"),
            };

            cx.expr_binary(span, op, self_f, other_f.clone())
        };

        cs_fold1(
            true, // use foldl
            |cx, span, subexpr, self_f, other_fs| {
                let eq = op(cx, span, self_f, other_fs);
                cx.expr_binary(span, combiner, subexpr, eq)
            },
            |cx, args| {
                match args {
                    Some((span, self_f, other_fs)) => {
                        // Special-case the base case to generate cleaner code.
                        op(cx, span, self_f, other_fs)
                    }
                    None => cx.expr_bool(span, base),
                }
            },
            Box::new(|cx, span, (_, vis), _| {
                op(cx, span, cx.expr_ident(span, vis[0]), &[cx.expr_ident(span, vis[1])])
            }),
            cx,
            span,
            substr,
        )
    }

    fn cs_eq(cx: &mut ExtCtxt<'_>, span: Span, substr: &Substructure<'_>) -> P<Expr> {
        cs_op(cx, span, substr, BinOpKind::Eq, BinOpKind::And, true)
    }
    fn cs_ne(cx: &mut ExtCtxt<'_>, span: Span, substr: &Substructure<'_>) -> P<Expr> {
        cs_op(cx, span, substr, BinOpKind::Ne, BinOpKind::Or, false)
    }

    macro_rules! md {
        ($name:expr, $f:ident, $always_inline:expr) => {{
            let inline = if $always_inline {
                let always = attr::mk_nested_word_item(Ident::new(sym::always, span));
                attr::mk_list_item(Ident::new(sym::inline, span), vec![always])
            } else {
                cx.meta_word(span, sym::inline)
            };
            let attrs = vec![cx.attribute(inline)];
            MethodDef {
                name: $name,
                generics: LifetimeBounds::empty(),
                explicit_self: borrowed_explicit_self(),
                args: vec![(borrowed_self(), "other")],
                ret_ty: Literal(path_local!(bool)),
                attributes: attrs,
                is_unsafe: false,
                unify_fieldless_variants: true,
                collapse_all: $always_inline,
                combine_substructure: combine_substructure(Box::new(|a, b, c| $f(a, b, c))),
            }
        }};
    }

    super::inject_impl_of_structural_trait(
        cx,
        span,
        item,
        path_std!(cx, marker::StructuralPartialEq),
        push,
    );

    // avoid defining `ne` if we can
    // c-like enums, enums without any fields and structs without fields
    // can safely define only `eq`.
    let is_without_fields = is_type_without_fields(item);
    let mut methods = vec![md!("eq", cs_eq, is_without_fields)];
    if !is_without_fields {
        methods.push(md!("ne", cs_ne, is_without_fields));
    }

    let trait_def = TraitDef {
        span,
        attributes: Vec::new(),
        path: path_std!(cx, cmp::PartialEq),
        additional_bounds: Vec::new(),
        generics: LifetimeBounds::empty(),
        is_unsafe: false,
        supports_unions: false,
        methods,
        associated_types: Vec::new(),
    };
    trait_def.expand(cx, mitem, item, push)
}
