# Changelog

Every release of the Rocq library `rocq-deduxit` (logical root
`Deduxit`), named `rocq-linlog` (logical path `Linlog`) up to 0.2.0,
newest first. The form is that of
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the
versions follow [Semantic Versioning](https://semver.org/). The library's
version is deduxit's: a certificate that deduxit writes for `--kernel
deduxit` (linlog for `--kernel linlog` up to 0.2.0) compiles against the
library of the same version.

## [0.3.0] - unreleased

The library renamed `rocq-deduxit`, under the logical root `Deduxit`,
and certificates of non-derivability where copies add literals, beside
deduxit 0.3.0 (linlog renamed), whose certificates for `--kernel
deduxit` it checks.

### Changed

- **Breaking:** the package is `rocq-deduxit`, the repository
  `github.com/deduxit/rocq-deduxit` and the documentation
  `https://deduxit.github.io/rocq-deduxit/`. The library has one logical
  root, `Deduxit`, with a namespace per calculus, and every module of
  0.2.0 is now under `Deduxit.Linear`: `From Linlog Require Import
  Soundness.` becomes `From Deduxit.Linear Require Import Soundness.`,
  and `Linlog.Calculus.ll` is `Deduxit.Linear.Calculus.ll`. No module,
  definition or theorem changed its own name; the files moved from
  `theories/` to `theories/Linear/`, and the package installs into
  `user-contrib/Deduxit/Linear`. The tests and the bridges to NanoYalla
  and Yalla, which are not installed, take the paths
  `Deduxit.Linear.Tests` and `Deduxit.Linear.Bridges`.
- `_RocqProject` maps `theories` with `-Q` instead of `-R`, as Rocq
  loads an installed library, so the build sees the paths a user sees.

### Added

- Weighted counts (`Weights.v`): an integer weight per atom, and atoms
  declared dead, whose literal of a sign `p` names contributes nothing a
  sum can cancel and whose other literal absorbs. Without weakening and
  without cut, Mix allowed, every derivable sequent can contribute zero
  to the weighted count or absorb, copies of `?` formulas included
  (`weighted_balance`), so weights that the test `overweight` accepts by
  computation refute a sequent (`weighted_refutation`, and two-sided
  `iweighted_refutation`). With the weight `1` on one atom this is the
  one-sided count, where every literal of the atom below an exponential
  has one sign; with a Farkas certificate of a Horn program's state
  equation and the atoms no firing reaches declared dead in the bodies'
  sign, it is the state equation's refutation.
- The same with weakening (`affine_balance`, `overweight_affine`,
  `affine_refutation`, `iaffine_refutation`) for sequents whose
  formulas have outputs as a Horn program's do (`outputs`, `shaped`):
  a derivation then drops only formulas without an output.
- The weighted count of first-order sequents without weakening
  (`FirstOrderWeights.v`), each literal weighed by its predicate or, for
  a predicate whose literals are all closed, by the literal; and the
  embedding of the first-order two-sided calculus in the one-sided one
  (`FirstOrderWeights.ill_ll`).
- `weight_of`, the weight a table gives an atom, for certificates.

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
