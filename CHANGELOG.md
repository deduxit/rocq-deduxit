# Changelog

Every release of the Rocq library `rocq-linlog` (logical path `Linlog`),
newest first. The form is that of
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the
versions follow [Semantic Versioning](https://semver.org/). The library's
version is linlog's: a certificate that linlog writes for `--kernel
linlog` compiles against the library of the same version.

## [0.2.0] - 2026-11-02

The library's first release, beside linlog 0.2.0, whose certificates
for `--kernel linlog` it checks. Its history up to 2026-11-02 is that
of linlog's repository, under `rocq/`, where linlog 0.1.0's tree held
only a first draft of the opam file; nothing of it was published before.

### Added

- The one-sided sequent calculus of linear logic (`Formulas.v`,
  `Calculus.v`), with Mix, weakening and cut as parameters of `rules`
  (`classical` has none of them), and the two-sided calculus of
  intuitionistic linear logic and its affine variant
  (`Intuitionistic.v`), with weakening and cut as parameters of
  `irules`.
- linlog's proof terms as datatypes (`Proofs.v`, the two-sided `iproof`),
  their checkers as functions (`Check.v`, `IntuitionisticCheck.v`), and
  for every calculus the theorem that a term the checker accepts proves
  its sequent (`Soundness.v`: `soundness`, `soundness_classical`,
  `soundness_mix`, `soundness_affine`; `soundness_ill`).
- Certificates that a sequent is not derivable (`Refutations.v`): the
  classical reading, an atom's balance and the count equation, each
  from a Boolean test, one-sided and two-sided.
- The reduction of Mix to `?(⊥⊗⊥)` (`Mix.v`).
- A first-order development beside the propositional one: terms with de
  Bruijn indices and eigenvariables (`Terms.v`), both calculi with the
  quantifier rules and the eigenvariable condition
  (`FirstOrderFormulas.v`, `FirstOrderCalculus.v`,
  `FirstOrderIntuitionistic.v`), the first-order proof terms, their
  checkers and the same theorems in every mode.
- The bridges, outside the package: the one-sided classical calculus
  proved equivalent to NanoYalla's `nanoll.v` and the two-sided one to
  Yalla's `nanoill.v`.
- Tested with Rocq 9.0, 9.1, 9.2 and 9.3 and their standard libraries:
  the library builds, the certificates under `tests/` compile and every
  theorem's assumptions are closed under the global context, for each.
- The documentation, `rocq doc`'s pages of every module, built by the
  flake (`nix build .#doc`) and published on the repository's Pages
  site by the release workflow.

### Changed

- The library has a repository of its own,
  [`linlog-prover/rocq-linlog`](https://github.com/linlog-prover/rocq-linlog),
  started with the tree as it stood under `rocq/` of
  [linlog](https://github.com/linlog-prover/linlog) on 2026-11-02, at
  linlog's commit `31f36a5d`: the library (`theories/`), its tests and
  certificates (`tests/`), the bridges to NanoYalla and Yalla
  (`bridges/`), the opam file and the flake's checks. linlog's flake
  takes this repository as a pinned input and compiles the certificates
  its exporter writes against it.

[0.2.0]: https://github.com/linlog-prover/rocq-linlog/releases/tag/v0.2.0
