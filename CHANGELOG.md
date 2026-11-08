# Changelog

Every release of the Rocq library `rocq-linlog` (logical path `Linlog`),
newest first. The form is that of
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the
versions follow [Semantic Versioning](https://semver.org/). The library's
version is linlog's: a certificate that linlog writes for `--kernel
linlog` compiles against the library of the same version.

## [0.3.0] - unreleased

Certificates of non-derivability where copies add literals, beside
linlog 0.3.0, whose certificates for `--kernel linlog` it checks.

### Added

- Weighted counts (`Weights.v`): an integer weight per atom, and atoms
  declared dead, whose positive literal contributes nothing a sum can
  cancel and whose negative literal absorbs. Without weakening and
  without cut, Mix allowed, every derivable sequent can contribute zero
  to the weighted count or absorb, copies of `?` formulas included
  (`weighted_balance`), so weights that the test `overweight` accepts by
  computation refute a sequent (`weighted_refutation`, and two-sided
  `iweighted_refutation`). With the weight `1` on one atom this is the
  one-sided count, where every literal of the atom below an exponential
  has one sign; with a Farkas certificate of a Horn program's state
  equation and the atoms no firing reaches declared dead, it is the
  state equation's refutation.
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
