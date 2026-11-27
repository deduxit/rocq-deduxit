# Changelog

Every release of the Rocq library `rocq-deduxit` (logical root
`Deduxit`), named `rocq-linlog` (logical path `Linlog`) up to 0.2.0,
newest first. The form is that of
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the
versions follow [Semantic Versioning](https://semver.org/). The library
is released beside deduxit, under deduxit's version number, when it
changes: a certificate that deduxit writes for `--kernel deduxit`
(linlog for `--kernel linlog` up to 0.2.0) compiles against the library
of the same version, or of the latest before it when the library did
not change. There is no 0.5.0: deduxit 0.5.0's certificates compile
against 0.4.0. There is no 0.7.0: deduxit 0.7.0's compile against 0.6.0.

## [Unreleased]

### Added

- The certificates' interface: every name deduxit's certificates use,
  listed in README ("The certificates' interface") and compiled, one
  file per certificate prelude, by `tests/Interface/`. A change that
  breaks it is a breaking change of the library, and this changelog
  says so.
- The flake's check compiles README's Rocq examples, and builds the
  library with every default warning an error (but one of Rocq 9.2
  whose remedy 9.0 and 9.1 lack) and with `Default Goal Selector "!"`.
- CI installs the package from its opam file on each Rocq the bounds
  admit, as the release does before it publishes.

- `Deduxit.Linear.Multiset` (the checkers' multiset operations and
  their permutation lemmas, for any type with a Boolean equality),
  `Deduxit.Linear.TwoSided` (the cut's conclusion of the two-sided
  checkers, its lemmas and their proofs' tactics),
  `Deduxit.Linear.FirstOrderFacts` (`dual_dual`, `dual_subst`,
  `occurs_dual` of first-order formulas), `Deduxit.Base.Lists` (`mem`,
  `existsb_false`, `forallb_perm`, `existsb_perm`) and
  `TermsCheck.tsubst_closed`.

### Changed

- README, the opam description, `CITATION.cff` and the Nix package's
  description name the suites in the order ordinary logic, linear logic,
  modal logic, and the opam description names modal logic too.
- What the checkers share is proved once, in the modules above. Every
  name the library had keeps its statement: `Check.remove_one`,
  `IntuitionisticCheck.pick`, `KripkeCheck.mem`, `Soundness.diff_count`,
  … are now instances of the shared ones. `cbn` computes them on a
  closed term as before; on an open one it may show the shared function
  (`Multiset.diff …`) where it showed the checker's name. The propositional
  two-sided checker's pass is written with `let*`, as the first-order
  one is.
- No file declares an abbreviation with `Notation` (deprecated from
  Rocq 9.2): each is written out where it was used, so the library
  compiles on 9.2 and 9.3 without that deprecation's warnings. No
  statement changes.
- Every proof names what it introduces, so none depends on the names
  Rocq generates, and the flake's check builds the library with
  `-mangle-names`. The cut case of the first-order two-sided soundness
  is a lemma of its own, `FirstOrderIntuitionisticCheck.iderive_sound_cut`,
  where it was picked by its goal's number. No statement changes.
- The opam file bounds `rocq-stdlib` above too, below 9.3.
- A release uploads its source archive and gives that archive's URL and
  SHA-512 for the opam file, in place of GitHub's generated archive of
  the tag, whose checksum is not stable.

## [0.8.0] - 2026-11-23

First-order intuitionistic, minimal and classical logic, beside deduxit
0.8.0, whose certificates of first-order countermodels it checks: finite
structures in classical logic and finite Kripke models with growing
domains in intuitionistic and minimal logic.

### Added

- First-order intuitionistic, minimal and classical logic, under
  `Deduxit.Intuitionistic`: the formulas over the terms of
  `Deduxit.Linear.Terms` (`FirstOrderFormulas.v`) and the calculi `lj`
  (LJ and LM, with the record `rules` of the propositional calculus) and
  `lk` (LK), each with the quantifier rules of deduxit's checker
  (`FirstOrderCalculus.v`).
- Kripke models with growing domains (`FirstOrderKripke.v`): forcing,
  `persistence`, `kripke_soundness` of LJ and LM, and
  `kripke_countermodel`; the infinite chain, which refutes
  `¬¬∀x. (p(x) ∨ ¬p(x))` (`chain_excluded_middle`) and the
  double-negation shift `(∀x. ¬¬p(x)) → ¬¬(∀x. p(x))`
  (`chain_double_negation_shift`), where no
  finite model does.
- Finite structures and `classical_soundness` of LK
  (`FirstOrderClassical.v`).
- Finite structures and Kripke models as data (`FirstOrderCheck.v`):
  the checkers `srefutes` and `krefutes`, and `fo_classical_refutation`
  and `fo_kripke_refutation`, which turn their answer into
  `~ lk c Γ Δ` and `~ lj R Γ C`, as deduxit's certificates of
  first-order countermodels state them. The checkers stop at the first
  operand or element that decides a formula (`eval_fast`,
  `kforces_fast`, proved equal to the plain evaluators), as deduxit's
  own check does.

## [0.6.0] - 2026-11-20

Modal logic in the fifteen systems from K to S5, beside deduxit 0.6.0,
whose certificates of modal proofs and countermodels it checks.

### Added

- Modal logic, under `Deduxit.Modal`: the formulas with `□` and `◇`
  (`Formulas.v`); the five frame conditions, the fifteen systems from K
  to S5 as their sets (`System.K`, …, `System.S5`), forcing, and
  `valid C Γ Δ`, validity of a sequent in the Kripke models of a system
  (`Kripke.v`); labelled sequents and their validity `lvalid`
  (`Labelled.v`).
- The labelled sequent calculus `g3 C L Rt` (`Calculus.v`): Negri's G3K
  with the frame rule of every condition of the system, the rules of
  deduxit's calculi `G3K` to `G3S5`. `g3_sound` (`Soundness.v`): every
  sequent it derives is valid; `g3_valid` reads a derivation at one
  label as validity of the ordinary sequent.
- Labelled proofs as terms and their checker (`Check.v`): `mcheck`, and
  `modal_soundness` and `labelled_soundness`, which turn its answer
  into `valid C Γ Δ` and `lvalid C L Rt`, so a certificate states
  validity and proves it by `vm_compute`.
- Finite modal countermodels (`Countermodel.v`): `refutes` checks that
  a model's arrows meet the system's conditions and that a world forces
  the left of a sequent and nothing of its right, and
  `modal_refutation` turns its answer into `~ valid C Γ Δ`.

## [0.4.0] - 2026-11-15

Intuitionistic and minimal logic with their Kripke models, beside
deduxit 0.4.0, whose certificates for `--kernel deduxit` and of a
Kripke countermodel it checks.

### Added

- Intuitionistic and minimal logic, under `Deduxit.Intuitionistic`:
  the formulas (`⊤`, `¬A` and `A ↔ B` defined from `⊥`, `∧`, `∨` and
  `→`) and the calculus `lj R Γ C` (`Calculus.v`), G1i with shared
  contexts, ex falso (`intuitionistic`, LJ) and cut as options, so
  `minimal` (LM) has no rule for `⊥`.
- Kripke models (`Kripke.v`): `kripke_soundness`, every derivable
  sequent holds at every world of every model of its logic, with cut
  too; `kripke_countermodel`, a world that forces the hypotheses and
  not the conclusion shows a sequent underivable; and
  `classical_refutation`, its one-world case, an assignment.
- Finite models as data and their checker (`KripkeCheck.v`):
  `refutes` checks that a model is one of the logic's (a transitive
  relation, a monotone valuation, no world forcing `⊥` in LJ) and that
  a world refutes the sequent, and `kripke_refutation` turns its answer
  into `~ lj R Γ C`, so a certificate states a countermodel and proves
  it by `vm_compute`.

## [0.3.0] - 2026-11-09

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

[0.8.0]: https://github.com/deduxit/rocq-deduxit/releases/tag/v0.8.0
[0.6.0]: https://github.com/deduxit/rocq-deduxit/releases/tag/v0.6.0
[0.4.0]: https://github.com/deduxit/rocq-deduxit/releases/tag/v0.4.0
[0.3.0]: https://github.com/deduxit/rocq-deduxit/releases/tag/v0.3.0
[0.2.0]: https://github.com/linlog-prover/rocq-linlog/releases/tag/v0.2.0
