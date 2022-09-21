[<img alt="github" src="https://img.shields.io/badge/github-point--rs/shared--rc-4078c0?style=for-the-badge&logo=github" height="20">](https://github.com/point-rs/shared-rc)
[<img alt="crates.io" src="https://img.shields.io/crates/v/shared-rc.svg?style=for-the-badge&color=335a30&logo=rust" height="20">](https://crates.io/crates/shared-rc)
[<img alt="lib.rs" src="https://img.shields.io/crates/v/shared-rc.svg?label=lib.rs&style=for-the-badge&color=282a36&logo=rust" height="20">](https://lib.rs/crates/shared-rc)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-shared--rc-353535?style=for-the-badge&logo=docs.rs" height="20">](https://docs.rs/syn)
<!--
[<img alt="build status" src="https://img.shields.io/github/workflow/status/point-rs/shared-rc/CI/main?style=for-the-badge" height="20">](https://github.com/point-rs/shared-rc/actions?query=branch%3Amain)
-->

Reference-counted fat pointers that contain both an owning std `Rc` (or `Arc`)
and a pointer to a field owned by that `Rc`. This is a "self-referential" type
in the vein of [ouroboros](https://lib.rs/ouroboros) or [yoke](https://lib.rs/yoke).

By specializing just for the reference-counted pointers, this crate provides a
much simpler API compared to that of ouroboros, yoke, or any other crate for
general self-referential types.
