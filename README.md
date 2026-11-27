# <picture><source media="(prefers-color-scheme: dark)" srcset="https://deduxit.github.io/logo/wordmark-dark.svg"><img alt="deduxit" src="https://deduxit.github.io/logo/wordmark-light.svg" height="80"></picture> in Rocq

> **dēdūxit** [deːˈduːk.sɪt] *Latin, verb*: "it has derived", the perfect of *dēdūcō*, to lead down, derive.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23899109.svg)](https://doi.org/10.5281/zenodo.23899109)

`rocq-deduxit` is the Rocq library that checks the certificates
[deduxit](https://github.com/deduxit/deduxit) writes. deduxit proves
and refutes sequents of linear, intuitionistic, classical and modal
logic. A certificate is a Rocq file: a lemma that states that a sequent
is derivable, or that it is not, with a proof by computation. Compile it
against this library, and Rocq has checked deduxit's answer.

You can also use the library on its own: it defines the sequent
calculi of linear logic, those of intuitionistic and minimal logic
with their Kripke models, LJ, LM and LK at first order with Kripke
models with growing domains and finite structures, and the labelled
calculus of the modal
systems K to S5, as inductive types, so you can state and prove your
own theorems about derivability.

It needs Rocq 9.0, 9.1, 9.2 or 9.3 and its standard library, nothing
else. Its logical root is `Deduxit`, with a namespace per calculus:
linear logic is `Deduxit.Linear`, intuitionistic and minimal logic
`Deduxit.Intuitionistic`, modal logic `Deduxit.Modal`.

## Install

**With opam**, from the [Rocq opam archive](https://rocq-prover.org/docs/using-opam)
once the release is there, or meanwhile from its tag:

```sh
opam repo add rocq-released https://rocq-prover.org/opam/released   # once
opam install rocq-deduxit                                            # from the archive
opam pin add rocq-deduxit https://github.com/deduxit/rocq-deduxit.git#v0.8.0   # or from the tag
opam upgrade rocq-deduxit                                            # later: a newer release from the archive
opam remove rocq-deduxit                                             # and to remove it
```

A package pinned to a tag stays at that tag. `opam pin add` with the
next tag moves it; `opam unpin rocq-deduxit` before `opam install`
takes the archive's release instead.

**With Nix** (flakes enabled), the flake's default package is the
library built with nixpkgs' Rocq 9.1:

```sh
nix build github:deduxit/rocq-deduxit/v0.8.0    # result/lib/coq/9.1/user-contrib/Deduxit
```

In a flake of your own, take it as an input
(`inputs.rocq-deduxit.url = "github:deduxit/rocq-deduxit/v0.8.0"`)
and put `rocq-deduxit.packages.${system}.default` beside
`rocqPackages.rocq-core` and `rocqPackages.stdlib` in a shell's
packages; nixpkgs' Rocq setup hook puts it on the load path.

**From the source**, `make` builds it in place, with Rocq and its
standard library on the path (`nix develop` gives both), and `make
install` installs it into Rocq's `user-contrib`.

## Check a certificate

Ask deduxit for a certificate in Rocq, then compile it:

```console
$ deduxit prove --mix --format rocq --standalone --output mix.v "A, B |- A, B"
$ rocq compile mix.v                                                  # library installed
$ rocq compile -Q path/to/rocq-deduxit/theories Deduxit mix.v         # library built in place
```

Rocq prints nothing when it accepts the file. The certificate is short:

```coq
(* provable (MLL, classical with Mix, focus engine) *)
From Stdlib Require Import List String.
From Deduxit.Linear Require Import Soundness.
Import ListNotations.
Open Scope string_scope.

Lemma certificate : ll (atom := string) {| mix := true; weakening := false; cut := false |} [covar "A"; covar "B"; var "A"; var "B"].
Proof.
  apply (soundness_mix String.eqb String.eqb_spec
    (Mix (Ax "A") (Ax "B"))).
  vm_compute. reflexivity.
Qed.
```

The lemma says that the sequent `⊢ A⊥, B⊥, A, B` is derivable in linear
logic with Mix. The proof gives deduxit's proof term, `Mix (Ax "A") (Ax
"B")`, to a soundness theorem, which turns it into a derivation once
`vm_compute` has run the library's checker on it. deduxit writes such
certificates for Mix, affine and intuitionistic logic and for sequents
with quantifiers; for classical linear logic, add `--kernel deduxit`
(its default there is NanoYalla). For a sequent that is not derivable,
the lemma states `~ ll …` and the proof applies a refutation theorem
instead.

To trust a certificate, read its statement against the files it rests
on. The checker and its proof appear only in the proof, so you need
not read them:

- `Formulas.v` and `Calculus.v` for a one-sided sequent;
- `Intuitionistic.v` for a two-sided one;
- `Terms.v`, `FirstOrderFormulas.v`, `FirstOrderCalculus.v` and
  `Calculus.v` (for its `rules`) for a first-order one-sided sequent;
- `Terms.v`, `FirstOrderIntuitionistic.v` and `Intuitionistic.v` (for
  its `irules`) for a first-order two-sided one;
- `Intuitionistic/Formulas.v` and `Intuitionistic/Calculus.v` for a
  sequent of intuitionistic or minimal logic;
- `Terms.v`, `Intuitionistic/FirstOrderFormulas.v`,
  `Intuitionistic/FirstOrderCalculus.v` and `Intuitionistic/Calculus.v`
  (for its `rules`) for a first-order sequent of intuitionistic, minimal
  or classical logic;
- `Modal/Formulas.v` and `Modal/Kripke.v` for a sequent of modal logic,
  and `Modal/Labelled.v` too for a labelled one.

Every theorem rests on no axiom: `Print Assumptions` answers `Closed
under the global context`. `vm_compute` leaves a cast that the kernel
checks with its virtual machine, so a certificate trusts that machine as
well as the kernel.

## Prove with the library

`From Deduxit.Linear Require Import Soundness.` gives the one-sided
calculus `ll`, its rules, the proof terms and the checker. Prove a
sequent by its rules, or let the checker do it:

```coq
From Stdlib Require Import List String Permutation.
From Deduxit.Linear Require Import Soundness Refutations.
Import ListNotations.
Open Scope string_scope.

(* By the rules of the calculus. *)
Lemma excluded_middle : ll (atom := string) classical [parr (var "A") (covar "A")].
Proof. apply parr_r. eapply ex_r; [apply ax_r | apply perm_swap]. Qed.

(* By the checker, from a proof term. *)
Lemma excluded_middle' : ll classical [parr (var "A") (covar "A")].
Proof.
  apply (soundness_classical String.eqb String.eqb_spec
    (Par (var "A") (covar "A") (Ax "A"))).
  vm_compute. reflexivity.
Qed.

(* Not derivable: one more A than ~A. *)
Lemma no_contraction : ~ ll (atom := string) classical [covar "A"; tens (var "A") (var "A")].
Proof. apply (unbalanced_refutation String.eqb "A" _). vm_compute. reflexivity. Qed.
```

The modules of `Deduxit.Linear`:

- `Soundness`: the one-sided calculus with Mix, weakening and cut as
  options, its checker and `soundness`;
- `IntuitionisticCheck`: the two-sided calculus of intuitionistic linear
  logic and its affine variant, its checker and `soundness_ill`;
- `FirstOrderSoundness` and `FirstOrderIntuitionisticCheck`: the same
  with quantifiers. They reuse the propositional names, so import one
  development and qualify the other's names;
- `Refutations`, `Weights` and `FirstOrderWeights`: theorems that a
  sequent is not derivable, from the classical reading, an atom's
  balance, the count equation and weighted counts;
- `Mix`: a derivation with Mix becomes one of the same sequent with
  `?(⊥ ⊗ ⊥)` added, without Mix.

`From Deduxit.Intuitionistic Require Import KripkeCheck.` gives the
calculus `lj` of intuitionistic logic (LJ, `intuitionistic`) and of
minimal logic (LM, `minimal`), Kripke models, and their checker. A
finite model whose world forces the hypotheses and not the conclusion
shows a sequent underivable:

```coq
From Stdlib Require Import List String.
From Deduxit.Intuitionistic Require Import KripkeCheck.
Import ListNotations.
Open Scope string_scope.

(* Not derivable: world 0 forces neither a nor ~a, since world 1,
   later than it, forces a. *)
Lemma excluded_middle : ~ lj intuitionistic [] (vee (var "a") (neg (var "a"))).
Proof.
  apply (kripke_refutation String.eqb String.eqb_spec intuitionistic
    {| later := [[1]; []]; atoms := [[]; ["a"]]; absurd := [] |} 0).
  vm_compute. reflexivity.
Qed.
```

The modules of `Deduxit.Intuitionistic`:

- `Formulas` and `Calculus`: the formulas (`⊤`, `¬` and `↔` defined
  from `⊥`, `∧`, `∨` and `→`) and the calculus `lj`, with ex falso and
  cut as options;
- `Kripke`: Kripke models, forcing, `kripke_soundness` (every
  derivable sequent holds in every model), `kripke_countermodel`, and
  `classical_refutation` (the model with one world, an assignment);
- `KripkeCheck`: finite models as data, the checker `refutes` and
  `kripke_refutation`;
- `FirstOrderFormulas` and `FirstOrderCalculus`: first-order formulas
  over deduxit's terms, and the calculi `lj` (LJ and LM) and `lk` (LK)
  with the quantifier rules. They reuse the propositional names, so
  import one development and qualify the other's names;
- `FirstOrderKripke`: Kripke models with growing domains,
  `kripke_soundness`, `kripke_countermodel`, and the infinite chain,
  whose theorems `chain_excluded_middle` and
  `chain_double_negation_shift` refute `¬¬∀x. (p(x) ∨ ¬p(x))` and
  `(∀x. ¬¬p(x)) → ¬¬(∀x. p(x))`, which no finite model refutes;
- `FirstOrderClassical`: finite structures and `classical_soundness`
  of LK;
- `FirstOrderCheck`: finite structures and Kripke models as data, their
  checkers `srefutes` and `krefutes`, and `fo_classical_refutation` and
  `fo_kripke_refutation`. The checkers stop at the first operand or
  element that decides a formula, as deduxit's own check does.

A first-order certificate of a Kripke model reads (deduxit writes the
rules as `{| Calculus.explosion := true; Calculus.cut := true |}`, LJ
with cut, since the theorem holds for every choice):

```coq
From Stdlib Require Import List String.
From Deduxit.Intuitionistic Require Import FirstOrderCheck.
Import ListNotations.
Open Scope string_scope.

(* Not derivable: world 0 has the element 0, world 1 adds 1 and makes
   p(0) true, so no world forces ∀x. p(x), and p fails for good of no
   element of world 0. *)
Lemma not_forall :
  ~ lj Calculus.intuitionistic [neg (fall (var "p" [bound 0]))] (fex (neg (var "p" [bound 0]))).
Proof.
  apply (fo_kripke_refutation String.eqb String.eqb_spec _
    {| later := [[1]; []]; sizes := [1; 2]; tables := [[]; []];
       facts := [[]; [("p", [0])]]; absurd := [] |} 0).
  vm_compute. reflexivity.
Qed.
```

`From Deduxit.Modal Require Import Check Countermodel.` gives modal
logic: the systems from K to S5 (`System.K`, `System.S4`, …, each a set
of conditions on the frames), validity in a system's Kripke models
(`valid`), proofs in the labelled sequent calculus as terms with their
checker, and finite countermodels. A statement here is about the
models, so you need not read the calculus to trust it:

```coq
From Stdlib Require Import List String.
From Deduxit.Modal Require Import Check Countermodel.
Import ListNotations.
Open Scope string_scope.

(* Valid in S4: a proof with the labels w0, w1 and w2, which uses
   transitivity. *)
Lemma four : valid System.S4 [] [imp (box (var "p")) (box (box (var "p")))].
Proof.
  apply (modal_soundness String.eqb String.eqb_spec System.S4 "w0"
    (RImp "w0" (box (var "p")) (box (box (var "p")))
      (RBox "w0" "w1" (box (var "p"))
        (RBox "w1" "w2" (var "p")
          (Trans "w0" "w1" "w2"
            (LBox "w0" "w2" (var "p") (Ax "w2" (var "p")))))))).
  vm_compute. reflexivity.
Qed.

(* Not valid in T: world 0 sees itself and world 1, which sees world 2,
   where p is false. *)
Lemma four_needs_transitivity :
  ~ valid System.T [] [imp (box (var "p")) (box (box (var "p")))].
Proof.
  apply (modal_refutation String.eqb
    {| arrows := [[0; 1]; [1; 2]; [2]]; atoms := [["p"]; ["p"]; []] |}
    System.T 0).
  vm_compute. reflexivity.
Qed.
```

The logic is classical and the library assumes no axiom, so `valid`
speaks of the models whose forcing is stable under double negation;
with the law of excluded middle those are all models
(`excluded_middle_stable`; `Kripke.v` says more).

The modules of `Deduxit.Modal`:

- `Formulas` and `Kripke`: the formulas, the frame conditions and the
  fifteen systems, forcing, and `valid`;
- `Labelled`: labelled sequents, which name several worlds, and their
  validity `lvalid`;
- `Calculus`: the labelled sequent calculus `g3`, Negri's G3K with a
  frame rule per condition;
- `Soundness`: `g3_sound`, every derivable sequent is valid;
- `Check`: proof terms, the checker `mcheck`, `modal_soundness` and
  `labelled_soundness`;
- `Countermodel`: finite models as data, the test `refutes` and
  `modal_refutation`.

The documentation of every module is at
[deduxit.github.io/rocq-deduxit](https://deduxit.github.io/rocq-deduxit/)
(`nix build .#doc` builds it).

## What it covers

Every certificate deduxit 0.8.0 writes for `--kernel deduxit`, for a
countermodel and for modal logic, compiles against this library. That covers
proofs in classical, Mix, affine and
intuitionistic linear logic and its affine variant, with or without cut,
propositional and first-order. It also covers refutations by the
classical reading, an atom's balance, the count equation and weighted
counts (a count of one sign under an exponential, a Horn program's state
equation), one-sided and two-sided; weighted counts also for
first-order sequents; Kripke countermodels of intuitionistic and
minimal logic; first-order countermodels, finite structures in
classical logic and finite Kripke models with growing domains in
intuitionistic and minimal logic; and, in the modal systems K to S5,
labelled proofs and finite countermodels.

The library has no theorem for deduxit's other refutations, so deduxit
writes no certificate for them: a saturated set of the inverse method,
the basis of the Horn engine's backward search, the count equation of
a first-order sequent, and an exhaustive search.
Nor does it cover the ordered (cyclic) calculus, whose sequents keep
their order. It proves no cut elimination: balance and the counts are
stated for the calculi without cut, which are the ones deduxit refutes
in. On Rocq 9.2 and 9.3 it compiles with deprecation warnings
(`Notation` for an abbreviation, whose replacement 9.0 and 9.1 lack).

## The certificates' interface

A certificate deduxit writes uses the names below, under one of ten
preludes. They are the library's stable surface: a release that renames
or changes one breaks certificates already written, and the changelog
says so. `tests/Interface/` has a file per prelude that uses each name
at the type a certificate needs, and the flake's check compiles it.

| prelude imports | theorems | what the statement and term are written in |
|---|---|---|
| `Deduxit.Linear.Soundness` | `soundness`, `soundness_classical`, `soundness_mix`, `soundness_affine` | `ll`, `classical`, the record `{\| mix; weakening; cut \|}`, the formulas `var` to `wn`, the proof terms `Ax` to `Cut` with `Left` and `Right` |
| `Deduxit.Linear.IntuitionisticCheck` | `soundness_ill` | `ill`, `intuitionistic`, `affine`, `{\| iweakening; icut \|}`, the formulas `ivar` to `ioc`, the terms `IAx` to `ICut` |
| `Deduxit.Linear.FirstOrderSoundness`, with `Calculus` required | `soundness`, `soundness_classical`, `soundness_mix`, `soundness_affine` | `ll`, `Calculus.classical`, `{\| Calculus.mix; Calculus.weakening; Calculus.cut \|}`, `bound`, `eigen`, `tapp`, the formulas with `fall` and `fex`, the terms with `Forall` and `Exists` |
| `Deduxit.Linear.FirstOrderIntuitionisticCheck`, with `Intuitionistic` required | `soundness_ill` | `ill`, `Intuitionistic.intuitionistic`, `Intuitionistic.affine`, `{\| Intuitionistic.iweakening; Intuitionistic.icut \|}`, `bound`, `eigen`, `tapp`, the formulas with `iall` and `iex`, the terms with `IAllR`, `IExL`, `IExR`, `IAllL` |
| `Deduxit.Linear.Weights` | `classical_refutation`, `unbalanced_refutation`, `equation_refutation`, `weighted_refutation`, `affine_refutation`, and each with `i` for two-sided sequents | `weight_of` and the names of the first two rows |
| `Deduxit.Linear.FirstOrderCalculus`, `FirstOrderIntuitionistic` and `FirstOrderWeights`, with `Calculus`, `Intuitionistic` and `TermsCheck` required | `FirstOrderWeights.weighted_refutation`, `FirstOrderWeights.iweighted_refutation` | `TermsCheck.terms_eqb` and the first-order names above |
| `Deduxit.Intuitionistic.KripkeCheck` | `kripke_refutation` | `lj`, `intuitionistic`, `minimal`, the formulas `var`, `bot`, `wedge`, `vee`, `imp`, `top`, `neg`, `equiv`, the record `{\| later; atoms; absurd \|}` |
| `Deduxit.Intuitionistic.FirstOrderCheck` | `fo_classical_refutation`, `fo_kripke_refutation` | `lj`, `lk`, `{\| Calculus.explosion; Calculus.cut \|}`, `bound`, `tapp`, the formulas of the row above with `fall` and `fex`, `{\| size; functions; predicates \|}`, `{\| later; sizes; tables; facts; absurd \|}` |
| `Deduxit.Modal.Check` | `modal_soundness`, `labelled_soundness` | `valid`, `lvalid`, `lab`, `rel`, the record `{\| serial; reflexive; symmetric; transitive; euclidean \|}`, the formulas `var` to `dia`, the terms `Ax` to `Eucl` |
| `Deduxit.Modal.Countermodel` | `modal_refutation` | `valid`, the conditions' record, the formulas, `{\| arrows; atoms \|}` |

Every prelude also imports `List` and `String` of the standard library
(the refutations `ZArith`, the first-order ones `Bool`), opens
`ListNotations` and `string_scope`, and takes `String.eqb` and
`String.eqb_spec` for atoms. deduxit's messages also name
`chain_excluded_middle` and `chain_double_negation_shift` of
`Deduxit.Intuitionistic.FirstOrderKripke`.

## Upgrading from rocq-linlog

Up to 0.2.0 the library was `rocq-linlog`, with the logical path
`Linlog`, in the repository `linlog-prover/rocq-linlog`. Its modules
are the same, now under `Deduxit.Linear`: `From Linlog Require Import
Soundness.` becomes `From Deduxit.Linear Require Import Soundness.`.

## The repository

- `theories/Linear/`, `theories/Intuitionistic/` and `theories/Modal/`:
  the library, `Deduxit.Linear`, `Deduxit.Intuitionistic` and
  `Deduxit.Modal`.
- `tests/`: certificates compiled against the installed library
  (`Deduxit.Linear.Tests`, `Deduxit.Intuitionistic.Tests` for
  `tests/Intuitionistic/` and `Deduxit.Modal.Tests` for `tests/Modal/`),
  and the certificates' interface (`tests/Interface/`).
- `bridges/`: proofs that the calculi derive the same sequents as
  NanoYalla's `nanoll.v` and Yalla's `nanoill.v`
  (`Deduxit.Linear.Bridges`), compiled against the files the flake pins,
  never copied.

`nix flake check` builds the library with every Rocq it admits, each
default warning an error but two of Rocq 9.2 that 9.0 and 9.1 cannot
meet, compiles every certificate under `tests/`,
README's examples and the bridges, and requires every theorem's
assumptions to be closed under the global context. deduxit's own flake
compiles the certificates its exporter writes against this library.
`scripts/opam-install.sh` installs the package from its opam file into
a fresh opam switch per Rocq version, as an opam user would; CI runs it
for each version.

The library was part of deduxit's repository, under its first name
linlog, until it moved here; its history up to the move is that
repository's (`CHANGELOG.md`). Its definitions, proofs, tests and
documentation, like deduxit's, were written with substantial AI
assistance, by Anthropic's Claude models in Claude Code, in steps the
author planned, directed and accepted.

## Citing

Each release is archived on Zenodo. To cite the library, use the DOI
[10.5281/zenodo.23899109](https://doi.org/10.5281/zenodo.23899109),
which always resolves to the latest version, or the DOI of the version
you used, which its Zenodo record gives (0.2.0's is
[10.5281/zenodo.23899110](https://doi.org/10.5281/zenodo.23899110)).
[`CITATION.cff`](CITATION.cff) holds the entry, and GitHub's "Cite this
repository" writes it as BibTeX or APA; versions up to 0.2.0 are
titled rocq-linlog. deduxit has a DOI of its own,
[10.5281/zenodo.23448588](https://doi.org/10.5281/zenodo.23448588).

## Licence

The library is licensed under the EUPL-1.2, as deduxit is. The mark
above is deduxit's, under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/), served from
[deduxit's site](https://deduxit.github.io/logo/LICENSE.txt).
