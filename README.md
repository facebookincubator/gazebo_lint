# Gazebo Lint - a linter for patterns relating to the Gazebo Library

The linter provides various helpful hints relating to additions from the [Gazebo Library](https://github.com/facebookincubator/gazebo).

For example, `Gazebo` added [`Dupe`](https://docs.rs/gazebo/0.4.0/src/gazebo/dupe.rs.html). This linter will provide hints to use `dupe` instead of `clone`. e.g. when doing `Arc::new(x).clone()`.
Other available hints are to "Use map" when doing `xs.iter().map(f).collect()` if the types line up, and reminders to derive `Dupe` when appropriate.

## Using Gazebo Lint

Gazebo lint can lint any program by adding the following to `lib.rs`:

```rust
#![feature(plugin)]
#![allow(deprecated)]
#![plugin(linter)]
```

Unfortunately the `plugin` feature is deprecated, so while useful, it is likely that `linter` will stop working at some point in the future.
We will look to update the linter to use the proper alternatives if applicable when that becomes an issue.

## Making a release
1. Check the [GitHub Actions](https://github.com/facebookincubator/gazebo_lint/actions) are green.
2. Update `CHANGELOG.md` with the changes since the last release. [This link](https://github.com/facebookincubator/gazebo_lint/compare/v0.1.0...main) can help (update to compare against the last release).
3. Update the version numbers of the two `Cargo.toml` files. Bump them by 0.0.1 if there are no incompatible changes, or 0.1.0 if there are.
4. Run `cargo publish --dry-run --allow-dirty`, then without the `--dry-run` in `gazebo_lint` directory.
5. Create a [GitHub release](https://github.com/facebookincubator/gazebo_lint/releases/new) with `v0.X.Y`, using the `gazebo_lint` version as the name.


## License

Gazebo Linter is both MIT and Apache License, Version 2.0 licensed, as found in the [LICENSE-MIT](LICENSE-MIT) and [LICENSE-APACHE](LICENSE-APACHE) files.
