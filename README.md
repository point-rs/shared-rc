This crate [is unsound](https://github.com/point-rs/shared-rc/issues/3) and there's no good way to make it sound without removing the benefits it purported to provide.
Use [yoke](https://crates.io/crates/yoke) instead.

<!--

[<img alt="github" src="https://img.shields.io/badge/github-point--rs/shared--rc-4078c0?style=for-the-badge&logo=github" height="20">](https://github.com/point-rs/shared-rc)
[<img alt="lib.rs" src="https://img.shields.io/crates/v/shared-rc.svg?label=lib.rs&style=for-the-badge&color=335a30&logo=rust" height="20">](https://lib.rs/crates/shared-rc)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-shared--rc-353535?style=for-the-badge&logo=docs.rs" height="20">](https://docs.rs/shared-rc)

Reference-counted fat pointers that contain both an owning std `Rc` (or `Arc`)
and a pointer to a field owned by that `Rc`. This is a "self-referential" type
in the vein of [ouroboros](https://lib.rs/ouroboros) or [yoke](https://lib.rs/yoke).

By specializing just for the reference-counted pointers, this crate provides a
potentially simpler API compared to that of ouroboros, yoke, or any other crate
for general self-referential types.

You're *probably* better off using yoke, though.
-->
