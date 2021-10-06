/*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under both the MIT license found in the
 * LICENSE-MIT file in the root directory of this source tree and the Apache
 * License, Version 2.0 found in the LICENSE-APACHE file in the root directory
 * of this source tree.
 */

// Utilities copied from Clippy on 15 May 2020 with minimal modification
// https://github.com/rust-lang/rust-clippy/blob/master/clippy_lints/src/utils/mod.rs

use std::mem;

use rustc_hir::{
    self, def,
    def::{DefKind, Res},
    def_id::{DefId, CRATE_DEF_INDEX},
    Expr, ExprKind, Impl, Item, ItemKind,
};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_lint::LateContext;
use rustc_middle::{
    traits,
    ty::{subst::GenericArg, Ty, TyKind, TyS},
};
use rustc_span::{self, symbol::Symbol, Span};
use rustc_trait_selection::traits::{
    predicate_for_trait_def, query::evaluate_obligation::InferCtxtExt,
};
use rustc_typeck::hir_ty_to_ty;
use smallvec::SmallVec;

macro_rules! sym {
    ($tt:tt) => {
        rustc_span::symbol::Symbol::intern(stringify!($tt))
    };
}

/// Returns the method names and argument list of nested method call expressions
/// that make up `expr`. method/span lists are sorted with the most recent call
/// first.
pub fn method_calls<'tcx>(
    expr: &'tcx Expr<'tcx>,
    max_depth: usize,
) -> (
    &'tcx Expr<'tcx>,
    Vec<Symbol>,
    Vec<&'tcx [Expr<'tcx>]>,
    Vec<Span>,
) {
    let mut method_names = Vec::with_capacity(max_depth);
    let mut arg_lists = Vec::with_capacity(max_depth);
    let mut spans = Vec::with_capacity(max_depth);

    let mut current = expr;
    for _ in 0..max_depth {
        if let ExprKind::MethodCall(path, span, args, _) = &current.kind {
            method_names.push(path.ident.name);
            arg_lists.push(&**args);
            spans.push(*span);
            current = &args[0];
            if current.span.from_expansion() {
                break;
            }
        } else {
            break;
        }
    }

    // MODIFIED: To return current as well
    (current, method_names, arg_lists, spans)
}

/// Gets the definition associated to a path.
pub fn path_to_res(cx: &LateContext, path: &[&str]) -> Option<def::Res> {
    let crates = cx.tcx.crates(());
    let krate = crates
        .iter()
        .find(|&&krate| cx.tcx.crate_name(krate).as_str() == path[0]);
    if let Some(krate) = krate {
        let krate = DefId {
            krate: *krate,
            index: CRATE_DEF_INDEX,
        };
        if path.len() == 1 {
            // just get the crate
            return Some(Res::Def(DefKind::Mod, krate));
        }

        let mut items = cx.tcx.item_children(krate);
        let mut path_it = path.iter().skip(1).peekable();

        loop {
            let segment = match path_it.next() {
                Some(segment) => segment,
                None => return None,
            };

            let result = SmallVec::<[_; 8]>::new();
            for item in mem::replace(&mut items, cx.tcx.arena.alloc_slice(&result)).iter() {
                if item.ident.name.as_str() == *segment {
                    if path_it.peek().is_none() {
                        return Some(item.res);
                    }

                    items = cx.tcx.item_children(item.res.def_id());
                    break;
                }
            }
        }
    } else {
        None
    }
}

/// Checks whether a type implements a trait.
/// See also `get_trait_def_id`.
pub fn implements_trait<'tcx>(
    cx: &LateContext<'tcx>,
    ty: Ty<'tcx>,
    trait_id: DefId,
    ty_params: &[GenericArg<'tcx>],
) -> bool {
    let ty = cx.tcx.erase_regions(ty);
    let obligation = predicate_for_trait_def(
        cx.tcx,
        cx.param_env,
        traits::ObligationCause::dummy(),
        trait_id,
        0,
        ty,
        ty_params,
    );
    cx.tcx
        .infer_ctxt()
        .enter(|infcx| infcx.predicate_must_hold_modulo_regions(&obligation))
}

/// Checks whether this is the implementation of a specific trait, if so, return the type the trait
/// is being implemented for
pub fn is_implementation_of_trait<'tcx>(
    cx: &LateContext<'tcx>,
    item: &Item,
    trait_path: &[&str],
) -> Option<Ty<'tcx>> {
    if let ItemKind::Impl(Impl {
        of_trait: Some(trait_ty),
        self_ty,
        ..
    }) = &item.kind
    {
        if let Some(trait_def) = trait_ty.trait_def_id() {
            if match_def_path(cx, trait_def, trait_path) {
                return Some(hir_ty_to_ty(cx.tcx, self_ty));
            }
        }
    }
    None
}

/// Convenience function to get the `DefId` of a trait by path.
/// It could be a trait or trait alias.
pub fn get_trait_def_id(cx: &LateContext, path: &[&str]) -> Option<DefId> {
    let res = match path_to_res(cx, path) {
        Some(res) => res,
        None => return None,
    };

    match res {
        Res::Def(DefKind::Trait | DefKind::TraitAlias, trait_id) => Some(trait_id),
        Res::Err => unreachable!("this trait resolution is impossible: {:?}", &path),
        _ => None,
    }
}

pub fn match_def_path(cx: &LateContext, did: DefId, syms: &[&str]) -> bool {
    // We have to convert `syms` to `&[Symbol]` here because rustc's
    // `match_def_path` accepts only that. We should probably move to Symbols in
    // Clippy as well.
    let syms = syms
        .iter()
        .map(|p| Symbol::intern(p))
        .collect::<Vec<Symbol>>();
    cx.match_def_path(did, &syms)
}

/// Matches the given `ty` with generics to the given types and generic types
pub fn match_ty_path(
    cx: &LateContext,
    ty: &TyS,
    ty_path: &[&str],
    generic_tys: &[&[&str]],
) -> bool {
    if let TyKind::Adt(ty, subst) = ty.kind() {
        if match_def_path(cx, ty.did, ty_path) {
            let mut i = 0;
            while i < generic_tys.len() {
                if let Some(ty_param) = subst.type_at(i).ty_adt_def() {
                    if !match_def_path(cx, ty_param.did, generic_tys[i]) {
                        return false;
                    } else {
                        i += 1;
                        continue;
                    }
                }
                return false;
            }

            return true;
        }
    }

    false
}
