# Changelog

Every release of the Rocq library `rocq-linlog` (logical path `Linlog`),
newest first. The form is that of
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the
versions follow [Semantic Versioning](https://semver.org/).

## [Unreleased]

### Changed

- The library has a repository of its own,
  [`linlog-prover/rocq-linlog`](https://github.com/linlog-prover/rocq-linlog),
  started with the tree as it stood under `rocq/` of
  [linlog](https://github.com/linlog-prover/linlog) on 2026-11-02, at
  linlog's commit `31f36a5d`: the library (`theories/`), its tests and
  certificates (`tests/`), the bridges to NanoYalla and Yalla
  (`bridges/`), the opam file and the flake's checks. Its history up to
  then is linlog's, whose changelog lists what the library gained under
  "Unreleased": the one-sided calculus with Mix, weakening and cut as
  parameters, the two-sided intuitionistic calculus and its affine
  variant, the proof terms, their checkers and soundness theorems, the
  reduction of Mix, the refutations, the first-order development and the
  bridges. linlog's flake takes this repository as a pinned input and
  compiles the certificates its exporter writes against it.
- The opam file's `homepage`, `bug-reports` and `dev-repo` name this
  repository, and it builds from the repository's root.
