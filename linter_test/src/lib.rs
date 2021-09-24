/*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under both the MIT license found in the
 * LICENSE-MIT file in the root directory of this source tree and the Apache
 * License, Version 2.0 found in the LICENSE-APACHE file in the root directory
 * of this source tree.
 */

//! Test library for gazebo_lint, which unfortunately needs to be checked by eye
//! Enable it by uncommenting linter_test in the root Cargo.toml
//! The prefix of the file should have no warnings.
//! The suffix after the line should have a hint per interesting line.

#![feature(plugin)]
#![allow(deprecated)]
#![plugin(gazebo_lint)]
#![allow(unused)] // Unused because these are gazebo_lint test cases with no actual use

use gazebo::prelude::*;
use std::{collections::HashSet, sync::Arc};

/////////////////////////////////////////////////////////////////////
// UTILITY TYPES

#[derive(Clone, Dupe)]
struct Foo {}

#[derive(Clone, Dupe)]
struct Wrapper<T>(T);

/////////////////////////////////////////////////////////////////////
// HINTS THAT SHOULD NOT FIRE

pub fn test_map_no() {
    // Returning a non-Vec type
    let _ = ["test"]
        .iter()
        .map(|x| Some(&x[1..]))
        .collect::<Option<Vec<_>>>();

    // Starting from a non-slice type
    let mut x = HashSet::new();
    x.insert("test");
    let _ = x.iter().map(|x| Some(&x[1..])).collect::<Vec<_>>();

    // We can ignore the hint
    #[allow(gazebo_use_map)]
    let _ = ["test"].iter().map(|x| &x[1..]).collect::<Vec<_>>();
}

pub fn test_try_map_no() {
    // Returning a non-Vec type
    let _ = ["test"]
        .iter()
        .map(|x| Ok::<_, ()>(Some(&x[1..])))
        .collect::<Result<Option<Vec<_>>, _>>();

    // Starting from a non-slice type
    let mut x = HashSet::new();
    x.insert("test");
    let _ = x
        .iter()
        .map(|x| Ok::<_, ()>(&x[1..]))
        .collect::<Result<Vec<_>, _>>();

    // We can ignore the hint
    #[allow(gazebo_use_try_map)]
    let _ = ["test"]
        .iter()
        .map(|x| Ok::<_, ()>(&x[1..]))
        .collect::<Result<Vec<_>, ()>>();
}

pub fn test_map_into_no() {
    // Doesn't work for slices
    let x: &[&str] = &["test"];
    let _ = x.into_iter().map(|x| &x[1..]).collect::<Vec<_>>();

    // We can ignore the hint
    #[allow(gazebo_use_into_map)]
    let _ = vec!["test"]
        .into_iter()
        .map(|x| &x[1..])
        .collect::<Vec<_>>();
}

pub fn test_map_into_try_no() {
    // Doesn't work for slices
    let x: &[&str] = &["test"];
    let _ = x
        .into_iter()
        .map(|x| Ok::<_, ()>(&x[1..]))
        .collect::<Result<Vec<_>, _>>();

    // We can ignore the hint
    #[allow(gazebo_use_into_try_map)]
    let _ = vec!["test"]
        .into_iter()
        .map(|x| Ok::<_, ()>(&x[1..]))
        .collect::<Result<Vec<_>, _>>();
}

pub fn test_use_slice_cloned_no() {
    let _ = vec!["test".to_owned()]
        .iter()
        .cloned()
        .collect::<HashSet<_>>();
    let _ = ["test".to_owned()]
        .iter()
        .filter(|x| true)
        .cloned()
        .collect::<Vec<_>>();

    #[allow(gazebo_use_slice_cloned)]
    let _ = vec!["test".to_owned()].iter().cloned().collect::<Vec<_>>();
}

pub fn test_use_slice_duped() {
    #[derive(Clone, Dupe, PartialEq, Eq, Hash)]
    struct X;
    let _ = vec![X].iter().duped().collect::<HashSet<_>>();
    let _ = [X].iter().filter(|x| true).duped().collect::<Vec<_>>();

    #[allow(gazebo_use_slice_duped)]
    let _ = vec![X].iter().duped().collect::<Vec<_>>();
}

pub fn test_dupe_no() {
    // String is not Dupe
    let _ = "test".to_owned().clone();
    // Wrapper is Dupe only if the inner is Dupe
    let _ = Wrapper("test".to_owned()).clone();
    // We can ignore the hint
    #[allow(gazebo_use_dupe)]
    let _ = Arc::new("test").clone();
}

pub fn test_duped_no() {
    // String is not Dupe
    let _ = ["a".to_owned(), "b".to_owned()].iter().cloned();
    #[allow(gazebo_use_duped)]
    let _ = [1, 2].iter().cloned();
}

pub fn test_box_no() {
    #[allow(use_box)]
    let _ = Box::new("test");
}

pub fn dupe_on_copy_no() {
    #[derive(Dupe, Clone, Copy)]
    struct DupeAndCopy;

    #[allow(gazebo_dupe_on_copy)]
    let x = DupeAndCopy.dupe();

    let x_ref = &x;

    #[allow(gazebo_dupe_on_copy)]
    let _ = x_ref.dupe();

    #[derive(Dupe, Clone)]
    struct DupeNotCopy;

    let x = DupeNotCopy.dupe();
    let x_ref = &x;
    let _ = x_ref.dupe();

    let x_refref = &x_ref;
    let _ = x_refref.dupe();
}

trait CloneAndDupe: Clone + Dupe {}

mod impl_dupe {
    use super::*;

    #[allow(gazebo_impl_dupe)]
    #[derive(Clone)]
    struct Foo(usize);

    #[allow(gazebo_impl_dupe)]
    #[derive(Clone)]
    struct Bar {
        x: usize,
    }

    #[allow(gazebo_impl_dupe)]
    #[derive(Clone)]
    enum Enums {
        A(usize),
        B { x: usize },
    }

    #[derive(Clone)]
    struct ManyArgs(usize, usize);

    #[derive(Clone)]
    struct ManyArgsNamed {
        x: usize,
        y: usize,
    }

    struct NoClone;

    #[derive(Clone, Dupe)]
    struct AlreadyDupe;

    #[derive(Clone)]
    struct Generic<T>(T);

    #[derive(Clone_, Dupe_)]
    struct GenericAlreadyDupe<T>(Arc<T>);
}

mod no_warn {
    use anyhow;
}

fn no_bail() -> anyhow::Result<()> {
    return Err(anyhow::anyhow!("foo"));
}

fn direct_result() -> Result<(), ()> {
    Ok(())
}

/////////////////////////////////////////////////////////////////////
// HINTS THAT SHOULD FIRE
//
pub fn test_map_yes() {
    let v = vec!["test"];
    let _ = v.iter().map(|x| &x[1..]).collect::<Vec<_>>();
    let _ = vec!["test"].iter().map(|x| &x[1..]).collect::<Vec<_>>();
    let _ = ["test"].iter().map(|x| &x[1..]).collect::<Vec<_>>();
}

pub fn test_try_map_yes() {
    let v = vec!["test"];
    let _ = v
        .iter()
        .map(|x| Ok::<_, ()>(&x[1..]))
        .collect::<Result<Vec<_>, ()>>();
    let _ = vec!["test"]
        .iter()
        .map(|x| Ok::<_, ()>(&x[1..]))
        .collect::<Result<Vec<_>, ()>>();
    let _ = ["test"]
        .iter()
        .map(|x| Ok::<_, ()>(&x[1..]))
        .collect::<Result<Vec<_>, ()>>();
}

pub fn test_map_into() {
    let v = vec!["test"];
    let _ = v.into_iter().map(|x| &x[1..]).collect::<Vec<_>>();
    let _ = vec!["test"]
        .into_iter()
        .map(|x| &x[1..])
        .collect::<Vec<_>>();
}

pub fn test_map_into_try() {
    let v = vec!["test"];
    let _ = v
        .into_iter()
        .map(|x| Ok::<_, ()>(&x[1..]))
        .collect::<Result<Vec<_>, _>>();
    let _ = vec!["test"]
        .into_iter()
        .map(|x| Ok::<_, ()>(&x[1..]))
        .collect::<Result<Vec<_>, _>>();
}

pub fn test_use_slice_cloned_yes() {
    let v = vec!["test".to_owned()];
    let _ = v.iter().cloned().collect::<Vec<_>>();
    let _ = vec!["test".to_owned()].iter().cloned().collect::<Vec<_>>();
    let _ = ["test".to_owned()].iter().cloned().collect::<Vec<_>>();
}

pub fn test_use_slice_duped_yes() {
    #[derive(Clone, Dupe)]
    struct X;
    let v = vec![X];
    let _ = v.iter().duped().collect::<Vec<_>>();
    let _ = vec![X].iter().duped().collect::<Vec<_>>();
    let _ = [X].iter().duped().collect::<Vec<_>>();
}

pub fn test_dupe() {
    let _ = Arc::new("test").clone();
    let foo = Foo {}.clone();

    let foo_ref = &foo;
    let _ = foo_ref.clone();

    let _ = vec![Foo {}].map(|x| x.clone());
}

pub fn test_duped() {
    let _ = [1, 2].iter().cloned();

    let _ = vec![1, 2].iter().cloned();
    let _: Vec<i32> = vec![1, 2].iter().map(|a| a).cloned().collect();
}

pub fn dupe_on_copy() {
    #[derive(Dupe, Clone, Copy)]
    struct DupeAndCopy;

    let x = DupeAndCopy.dupe();
    let x_ref = &x;

    let _ = x_ref.dupe();
}

pub fn test_box() {
    let _ = Box::new(1);
    let _ = vec![Box::new(1)];
    let f = |x| Box::new(x);
    let _ = f(Box::new(1));
}

mod impl_dupe_warm {
    use super::*;

    #[derive(Clone)]
    struct Unit;

    #[derive(Clone)]
    struct UnitStruct {}

    #[derive(Clone)]
    struct Foo(usize);

    #[derive(Clone)]
    struct Bar {
        x: usize,
    }

    #[derive(Clone)]
    enum Enums {
        A(usize),
        B { x: usize },
        C,
    }

    #[derive(Clone)]
    struct Generic<T: Dupe>(T);

    #[derive(Clone)]
    struct GenericCloneAndDupe<T: CloneAndDupe>(T);

    #[derive(Clone, Copy)]
    struct ManyFields {
        a: i32,
        b: i32,
    }
}

mod should_warn {
    use anyhow::{Error, Result, *};
}

fn uses_bail() -> anyhow::Result<()> {
    anyhow::bail!("foo");
}

fn uses_bail2() -> anyhow::Result<()> {
    use anyhow::bail;
    bail!("foo");
}

fn uses_ensure() -> anyhow::Result<()> {
    anyhow::ensure!(true, "foo");
    Ok(())
}

fn use_direct_result() -> anyhow::Result<(), ()> {
    Ok(())
}
