//! Lint rules only work if you have first run:
//!
//!     rustup component add rustc-dev
//!
//! Lint rules are [deprecated](https://github.com/rust-lang/rust/pull/64675), but that's somewhat
//! OK because it's still useful in the short term, they still work, and once
//! they stop working we can investigate a clippy-like driver to run them for
//! us.
//!
//! Because they are deprecated and not hugely used, documentation is a bit hard
//! to find. I've used:
//!
//! * Examples in Servo: <https://github.com/servo/servo/blob/9fd668488e0986a36fe55f7fd023588993674ae6/components/script_plugins/lib.rs>
//! * Lint docs: <https://doc.rust-lang.org/1.1.0/rustc/lint/index.html>
//! * Plugin test: <https://github.com/rust-lang/rust/blob/95e0a2c50d063bd7eb79aa55d16cd5fee715c280/src/test/ui-fulldeps/auxiliary/lint-group-plugin-test.rs>
//! * Compiler plugins: <https://doc.rust-lang.org/1.3.0/book/compiler-plugins.html>
//! * More compiler plugins: <https://doc.rust-lang.org/unstable-book/language-features/plugin.html>
//! * The source of Clippy: <https://github.com/rust-lang/rust-clippy>

#![feature(plugin_registrar)]
#![feature(rustc_private)]
#![feature(box_syntax)]

// The rustc pieces we rely on.
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_infer;
extern crate rustc_lint;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_trait_selection;
extern crate rustc_typeck;
#[macro_use]
extern crate rustc_session;

#[macro_use]
mod clippy;

// We deliberately _don't_ use gazebo in gazebo_lint since
// we don't want gazebo_lint to recompile very often (since it's not the
// critical path) and we expect to change gazebo regularly, but gazebo_lint
// rarely.

use rustc_driver::plugin::Registry;
use rustc_hir::{
    def::{DefKind, Res},
    def_id::DefId,
    Expr, ExprKind, GenericArgs, Item, ItemKind, Path, PathSegment, QPath, Ty, UseKind,
};
use rustc_lint::{LateContext, LateLintPass, Lint, LintContext, LintId};
use rustc_middle::ty::TyKind;
use rustc_span::{Span, Symbol};

// We'd really like to do declare_tool_lint, but Rust has a check that
// the "tool" must be exactly rustc or clippy, so we can't.

declare_lint!(
    GAZEBO_USE_MAP,
    Warn,
    "The iter/collect can be replaced with `map`, with `use gazebo::prelude::*`"
);

declare_lint!(
    GAZEBO_USE_TRY_MAP,
    Warn,
    "The iter/map/collect can be replaced with `try_map`, with `use gazebo::prelude::*`"
);

declare_lint!(
    GAZEBO_USE_INTO_MAP,
    Warn,
    "The into_iter/map/collect can be replaced with `into_map`, with `use gazebo::prelude::*`"
);

declare_lint!(
    GAZEBO_USE_INTO_TRY_MAP,
    Warn,
    "The into_iter/map/collect can be replaced with `into_try_map`, with `use gazebo::prelude::*`"
);

declare_lint!(
    GAZEBO_USE_SLICE_CLONED,
    Warn,
    "The iter/cloned/collect can be replaced with `cloned`, with `use gazebo::prelude::*`"
);

declare_lint!(
    GAZEBO_USE_SLICE_DUPED,
    Warn,
    "The iter/duped/collect can be replaced with `duped`, with `use gazebo::prelude::*`"
);

declare_lint!(GAZEBO_USE_DUPE, Warn, "Use `dupe()`");

declare_lint!(GAZEBO_USE_DUPED, Warn, "Use `duped()`");

declare_lint!(
    GAZEBO_DUPE_ON_COPY,
    Warn,
    "using `dupe` on a `Copy` type. Try removing the call `dupe()`."
);

declare_lint!(
    ANYHOW_AVOID_BAIL_AND_ENSURE,
    Warn,
    "Do not use `anyhow::bail!` and `anyhow::ensure!`. Prefer explicit `return` of Error types"
);

declare_lint!(USE_BOX, Warn, "Use `box` syntax instead of `Box::new`");

declare_lint!(
    GAZEBO_IMPL_DUPE,
    Warn,
    "impl `Dupe` on types that impl `Clone` where possible, e.g. `struct Foo(SomethingDupe)`"
);

declare_lint!(
    ANYHOW_QUALIFY,
    Warn,
    "avoid importing `anyhow::Result` and `anyhow::Error`. Reference `anyhow` Error and Result \
    types by the qualified `anyhow::Result` and `anyhow::Error` types directly."
);

declare_lint!(
    ANYHOW_RESULT_TWO_ARGUMENTS,
    Warn,
    "use `Result` when there are two type arguments, instead of `anyhow::Result`."
);

declare_lint_pass!(
    Pass => [
        GAZEBO_USE_MAP,
        GAZEBO_USE_TRY_MAP,
        GAZEBO_USE_INTO_MAP,
        GAZEBO_USE_INTO_TRY_MAP,
        GAZEBO_USE_SLICE_CLONED,
        GAZEBO_USE_SLICE_DUPED,
        ANYHOW_AVOID_BAIL_AND_ENSURE,
        USE_BOX,
        GAZEBO_USE_DUPE,
        GAZEBO_IMPL_DUPE,
        ANYHOW_QUALIFY,
        GAZEBO_DUPE_ON_COPY,
        ANYHOW_RESULT_TWO_ARGUMENTS,
    ]
);

fn emit_lint(cx: &LateContext, lint: &'static Lint, span: Span) {
    cx.lint(lint, |l| l.build(lint.desc).set_span(span).emit());
}

/// Look for `x.iter().map(f).collect()`
/// Where the type of `x` is a slice, and the type of the result is a `Vec`.
fn check_use_map(cx: &LateContext, expr: &Expr) {
    let (root, method_names, _arg_lists, _method_spans) = clippy::method_calls(expr, 3);
    if method_names == [sym!(collect), sym!(map), sym!(iter)]
        && clippy::match_ty_path(
            cx,
            cx.typeck_results().expr_ty(expr),
            &["alloc", "vec", "Vec"],
            &[],
        )
        && cx.typeck_results().expr_ty_adjusted(root).is_slice()
    {
        emit_lint(cx, GAZEBO_USE_MAP, expr.span);
    }
}

/// Look for `x.iter().map(f).collect::<Result<_, _>>()`
/// Where the type of `x` is a slice, and the type of the result is a `Result<Vec<_>>`.
fn check_use_try_map(cx: &LateContext, expr: &Expr) {
    let (root, method_names, _arg_lists, _method_spans) = clippy::method_calls(expr, 3);
    if method_names == [sym!(collect), sym!(map), sym!(iter)] {
        let expr_ty = cx.typeck_results().expr_ty(expr);

        if clippy::match_ty_path(
            cx,
            expr_ty,
            &["core", "result", "Result"],
            &[&["alloc", "vec", "Vec"]],
        ) && cx.typeck_results().expr_ty_adjusted(root).is_slice()
        {
            emit_lint(cx, GAZEBO_USE_TRY_MAP, expr.span);
        }
    }
}

/// Look for `x.into_iter().map(f).collect()`
/// Where the type of `x` is a `Vec`, and the type of the result is a `Vec`.
fn check_use_into_map(cx: &LateContext, expr: &Expr) {
    let (root, method_names, _arg_lists, _method_spans) = clippy::method_calls(expr, 3);
    if method_names == [sym!(collect), sym!(map), sym!(into_iter)]
        && clippy::match_ty_path(
            cx,
            cx.typeck_results().expr_ty(expr),
            &["alloc", "vec", "Vec"],
            &[],
        )
        && clippy::match_ty_path(
            cx,
            cx.typeck_results().expr_ty(root),
            &["alloc", "vec", "Vec"],
            &[],
        )
    {
        emit_lint(cx, GAZEBO_USE_INTO_MAP, expr.span);
    }
}

/// Look for `x.into_iter().map(f).collect::<Result<_, _>>()`
/// Where the type of `x` is a slice, and the type of the result is a `Result<Vec<_>>`.
fn check_use_into_try_map(cx: &LateContext, expr: &Expr) {
    let (root, method_names, _arg_lists, _method_spans) = clippy::method_calls(expr, 3);
    if method_names == [sym!(collect), sym!(map), sym!(into_iter)]
        && clippy::match_ty_path(
            cx,
            cx.typeck_results().expr_ty(expr),
            &["core", "result", "Result"],
            &[&["alloc", "vec", "Vec"]],
        )
        && clippy::match_ty_path(
            cx,
            cx.typeck_results().expr_ty(root),
            &["alloc", "vec", "Vec"],
            &[],
        )
    {
        emit_lint(cx, GAZEBO_USE_INTO_TRY_MAP, expr.span);
    }
}

/// Look for `x.iter().<clone_kind>().collect()`
/// Where the type of `x` is a slice, and the type of the result is a `Vec<_>`.
fn check_use_slice_cloned_kind(
    cx: &LateContext,
    expr: &Expr,
    clone_kind: Symbol,
    lint_kind: &'static Lint,
) {
    let (root, method_names, _arg_lists, _method_spans) = clippy::method_calls(expr, 3);
    if method_names == [sym!(collect), clone_kind, sym!(iter)]
        && clippy::match_ty_path(
            cx,
            cx.typeck_results().expr_ty(expr),
            &["alloc", "vec", "Vec"],
            &[],
        )
        && cx.typeck_results().expr_ty_adjusted(root).is_slice()
    {
        emit_lint(cx, lint_kind, expr.span);
    }
}

/// Look for `x.clone()`
/// Where the type of `x` implements `Dupe`.
fn check_use_dupe(cx: &LateContext, expr: &Expr) {
    if let ExprKind::MethodCall(method_call, method_span, args, _) = expr.kind {
        if args.len() == 1 && method_call.ident.name == sym!(clone) {
            if let Some(dupe_trait) = clippy::get_trait_def_id(cx, &["gazebo", "dupe", "Dupe"]) {
                let mut cloned_type = cx.typeck_results().expr_ty(&args[0]).peel_refs();
                loop {
                    if clippy::implements_trait(cx, cloned_type, dupe_trait, &[]) {
                        emit_lint(cx, GAZEBO_USE_DUPE, method_span);
                    }

                    // Note that Dupe can work on references, that is calling `clone` on `&Foo`
                    // could also be a valid `dupe` call. So, try de-referencing the type once and
                    // check for `Dupe` on `Foo` as well.
                    if let TyKind::Ref(_, inner_ty, _) = cloned_type.kind() {
                        cloned_type = inner_ty;
                    } else {
                        break;
                    }
                }
            }
        }
    }
}

/// Look for `x.cloned()`
/// Where the type of the `::Item` of `x` implements `Dupe`.
fn check_use_duped(cx: &LateContext, expr: &Expr) {
    if let ExprKind::MethodCall(method_call, method_span, args, _) = expr.kind {
        if args.len() == 1 && method_call.ident.name == sym!(cloned) {
            if let Some(iterator_trait) =
                clippy::get_trait_def_id(cx, &["gazebo", "ext", "iter", "IterDuped"])
            {
                let mut cloned_type = cx.typeck_results().expr_ty(&args[0]);
                loop {
                    if clippy::implements_trait(cx, cloned_type, iterator_trait, &[]) {
                        emit_lint(cx, GAZEBO_USE_DUPED, method_span);
                    }

                    // Note that Dupe can work on references, that is calling `clone` on `&Foo`
                    // could also be a valid `dupe` call. So, try de-referencing the type once and
                    // check for `Dupe` on `Foo` as well.
                    if let TyKind::Ref(_, inner_ty, _) = cloned_type.kind() {
                        cloned_type = inner_ty;
                    } else {
                        break;
                    }
                }
            }
        }
    }
}

/// Look for `x.dupe()`
/// Where the type of `x` implements `Copy`.
fn check_dupe_on_copy(cx: &LateContext, expr: &Expr) {
    if let ExprKind::MethodCall(method_call, method_span, args, _) = expr.kind {
        if args.len() == 1 && method_call.ident.name == sym!(dupe) {
            if let Some(dupe_trait) = clippy::get_trait_def_id(cx, &["gazebo", "dupe", "Dupe"]) {
                if let Some(copy_marker) = clippy::get_trait_def_id(cx, &["std", "marker", "Copy"])
                {
                    let mut duped_type = cx.typeck_results().expr_ty(&args[0]).peel_refs();
                    loop {
                        // Note that we could be calling `dupe` on a `&Foo`. All `&` types are
                        // `Copy`, so we actually need to make sure the current type we are looking
                        // at is `Dupe` as well so we correctly determine a `Foo` that is both
                        // `Dupe` and `Copy`, rather than a false positive because all `&`s are
                        // `Copy`.
                        if clippy::implements_trait(cx, duped_type, copy_marker, &[])
                            && clippy::implements_trait(cx, duped_type, dupe_trait, &[])
                        {
                            emit_lint(cx, GAZEBO_DUPE_ON_COPY, method_span);
                        }

                        // Note that Dupe can work on references, that is calling `dupe` on `&Foo`
                        // could also be a valid `dupe` call. So, try de-referencing the type once
                        // and check for `Copy` on `Foo` as well.
                        if let TyKind::Ref(_, inner_ty, _) = duped_type.kind() {
                            duped_type = inner_ty;
                        } else {
                            break;
                        }
                    }
                }
            }
        }
    }
}

/// Look for `Box::new`.
fn check_use_box(cx: &LateContext, expr: &Expr) {
    if let ExprKind::Call(call, args) = expr.kind {
        if args.len() == 1 {
            if let ExprKind::Path(qpath) = &call.kind {
                let res = cx.qpath_res(qpath, call.hir_id);
                if let Some(def_id) = res.opt_def_id() {
                    if clippy::match_def_path(cx, def_id, &["alloc", "boxed", "Box", "new"]) {
                        emit_lint(cx, USE_BOX, expr.span);
                    }
                }
            }
        }
    }
}

/// Look for traits implementing `Clone` but not `Dupe`, where `Dupe` is reasonable
/// A type is reasonably `Dupe` if either of:
///
/// 1. All the variants have at most one field, which is itself `Dupe`.
/// 2. The type implements `Copy`.
fn check_impl_dupe(cx: &LateContext, item: &Item) {
    fn is_cheap<'tcx>(
        cx: &LateContext<'tcx>,
        self_tys: rustc_middle::ty::Ty<'tcx>,
        dupe_trait: DefId,
    ) -> bool {
        match self_tys.kind() {
            TyKind::Adt(self_adt, sub) => {
                for variant in self_adt.variants.iter() {
                    let mut fields = variant.fields.iter();
                    if let Some(field) = fields.next() {
                        if fields.next().is_some() {
                            // only adt's of one field at most one field can be assumed dupe
                            // we don't want to mark a struct of 100 Arc's as dupe.
                            return false;
                        }
                        let field_ty = field.ty(cx.tcx, sub);

                        if !clippy::implements_trait(cx, field_ty, dupe_trait, sub) {
                            // the field isn't dupe, so the whole adt isn't
                            return false;
                        }
                    }
                    // empty fields => unit, which is dupe
                }

                // if we survived the loop, we can be dupe.
                true
            }
            _ => false,
        }
    }

    fn is_copy<'tcx>(cx: &LateContext<'tcx>, self_tys: rustc_middle::ty::Ty<'tcx>) -> bool {
        if let Some(copy_trait) = clippy::get_trait_def_id(cx, &["core", "marker", "Copy"]) {
            clippy::implements_trait(cx, self_tys, copy_trait, &[])
        } else {
            false
        }
    }

    if let Some(dupe_trait) = clippy::get_trait_def_id(cx, &["gazebo", "dupe", "Dupe"]) {
        if let Some(self_tys) =
            clippy::is_implementation_of_trait(cx, item, &["core", "clone", "Clone"])
        {
            if clippy::implements_trait(cx, self_tys, dupe_trait, &[]) {
                // already dupe
                return;
            }

            if is_copy(cx, self_tys) || is_cheap(cx, self_tys, dupe_trait) {
                emit_lint(cx, GAZEBO_IMPL_DUPE, item.span);
            }
        }
    }
}

/// Look for `anyhow::bail!` or `anyhow::ensure!`, both of which get expanded to `crate::private::Err`.
fn check_use_bail_and_ensure(cx: &LateContext, expr: &Expr) {
    // it's hard to check pre-expanded macros as we have no information on what the tokens actually
    // refer to. i.e. we can detect `anyhow::bail` and `bail` (with `use anyhow::`) only as pure
    // ast tokens. We cannot properly resolve them to make sure those are actually the anyhow
    // macros of interest.
    // Luckily, anyhow macros all expand to using `anyhow::private::Err`, so we can use the post
    // macro expansion and detect for that.
    if let ExprKind::Call(call, _) = expr.kind {
        if let ExprKind::Path(QPath::Resolved(_, path)) = &call.kind {
            if path.segments.len() == 3 {
                // the path here should be `anyhow::private::Err` if its a macro.
                // check for a length of 3.
                if clippy::path_to_res(cx, &["anyhow", "private", "Err"])
                    == clippy::path_to_res(cx, &["core", "result", "Result", "Err"])
                    && path.segments[1].res == clippy::path_to_res(cx, &["anyhow", "private"])
                    && path.segments[2].ident.as_str() == "Err"
                {
                    emit_lint(cx, ANYHOW_AVOID_BAIL_AND_ENSURE, expr.span);
                }
            }
        }
    }
}

/// Look for use `anyhow::Result` or use `anyhow::Error`.
fn check_qualify_anyhow(cx: &LateContext, item: &Item) {
    if let ItemKind::Use(path, kind) = &item.kind {
        match kind {
            UseKind::Glob => {
                if let Some(anyhow_path) = clippy::path_to_res(cx, &["anyhow"]) {
                    if anyhow_path == path.res {
                        emit_lint(cx, ANYHOW_QUALIFY, item.span)
                    }
                }
            }
            UseKind::Single => {
                if let Some(anyhow_path) = clippy::path_to_res(cx, &["anyhow", "Result"]) {
                    if anyhow_path == path.res {
                        emit_lint(cx, ANYHOW_QUALIFY, item.span)
                    }
                }
                if let Some(anyhow_path) = clippy::path_to_res(cx, &["anyhow", "Error"]) {
                    if anyhow_path == path.res {
                        emit_lint(cx, ANYHOW_QUALIFY, item.span)
                    }
                }
            }
            _ => {}
        };
    }
}

/// Look for `anyhow::Result<_, _>`.
fn check_anyhow_two_arguments(cx: &LateContext, ty: &Ty) {
    if let rustc_hir::TyKind::Path(QPath::Resolved(
        _,
        Path {
            res: Res::Def(DefKind::TyAlias, result),
            segments:
                [_, PathSegment {
                    args: Some(GenericArgs { args: [_, _], .. }),
                    ..
                }],
            ..
        },
    )) = &ty.kind
    {
        if clippy::match_def_path(cx, *result, &["anyhow", "Result"]) {
            emit_lint(cx, ANYHOW_RESULT_TWO_ARGUMENTS, ty.span);
        }
    }
}

impl<'tcx> LateLintPass<'tcx> for Pass {
    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx Expr<'_>) {
        check_use_map(cx, expr);
        check_use_try_map(cx, expr);
        check_use_into_map(cx, expr);
        check_use_into_try_map(cx, expr);
        check_use_slice_cloned_kind(cx, expr, sym!(cloned), GAZEBO_USE_SLICE_CLONED);
        check_use_slice_cloned_kind(cx, expr, sym!(duped), GAZEBO_USE_SLICE_DUPED);
        check_use_dupe(cx, expr);
        check_use_duped(cx, expr);
        check_dupe_on_copy(cx, expr);
        check_use_box(cx, expr);
        check_use_bail_and_ensure(cx, expr);
    }

    fn check_item_post(&mut self, cx: &LateContext<'tcx>, item: &'tcx Item<'tcx>) {
        check_impl_dupe(cx, item);
        check_qualify_anyhow(cx, item);
    }

    fn check_ty(&mut self, cx: &LateContext<'tcx>, item: &'tcx Ty<'tcx>) {
        check_anyhow_two_arguments(cx, item);
    }
}

#[allow(deprecated)]
#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    let lints = [
        GAZEBO_USE_MAP,
        GAZEBO_USE_TRY_MAP,
        GAZEBO_USE_INTO_MAP,
        GAZEBO_USE_INTO_TRY_MAP,
        GAZEBO_USE_SLICE_CLONED,
        GAZEBO_USE_SLICE_DUPED,
        ANYHOW_AVOID_BAIL_AND_ENSURE,
        USE_BOX,
        GAZEBO_USE_DUPE,
        GAZEBO_USE_DUPED,
        GAZEBO_IMPL_DUPE,
        ANYHOW_QUALIFY,
        GAZEBO_DUPE_ON_COPY,
        ANYHOW_RESULT_TWO_ARGUMENTS,
    ];

    reg.lint_store.register_lints(&lints);
    reg.lint_store.register_late_pass(|| box Pass);
    reg.lint_store.register_group(
        true,
        "gazebo",
        None,
        lints.iter().map(|x| LintId::of(x)).collect(),
    );
}