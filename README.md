# <picture><source media="(prefers-color-scheme: dark)" srcset="https://deduxit.github.io/logo/wordmark-dark.svg"><img alt="deduxit" src="https://deduxit.github.io/logo/wordmark-light.svg" height="80"></picture> in Rocq

> **dēdūxit** [deːˈduːk.sɪt] *Latin, verb*: "it has derived", the perfect of *dēdūcō*, to lead down, derive.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23899109.svg)](https://doi.org/10.5281/zenodo.23899109)

`rocq-deduxit` is the Rocq library that checks the certificates
[deduxit](https://github.com/deduxit/deduxit) writes. deduxit proves
and refutes sequents of linear logic and other logics. A certificate is
a Rocq file: a lemma that states that a sequent is derivable, or that it
is not, with a proof by computation. Compile it against this library,
and Rocq has checked deduxit's answer.

You can also use the library on its own: it defines the sequent
calculi of linear logic as inductive types, so you can state and prove
your own theorems about derivability.

It needs Rocq 9.0, 9.1, 9.2 or 9.3 and its standard library, nothing
else. Its logical root is `Deduxit`, with a namespace per calculus;
linear logic is `Deduxit.Linear`.

## Install

**With opam**, from the [Rocq opam archive](https://rocq-prover.org/docs/using-opam)
once the release is there, or meanwhile from its tag:

```sh
opam repo add rocq-released https://rocq-prover.org/opam/released   # once
opam install rocq-deduxit                                            # from the archive
opam pin add rocq-deduxit https://github.com/deduxit/rocq-deduxit.git#v0.3.0   # or from the tag
opam upgrade rocq-deduxit                                            # later: a newer release from the archive
opam remove rocq-deduxit                                             # and to remove it
```

A package pinned to a tag stays at that tag. `opam pin add` with the
next tag moves it; `opam unpin rocq-deduxit` before `opam install`
takes the archive's release instead.

**With Nix** (flakes enabled), the flake's default package is the
library built with nixpkgs' Rocq 9.1:

```sh
nix build github:deduxit/rocq-deduxit/v0.3.0    # result/lib/coq/9.1/user-contrib/Deduxit
```

In a flake of your own, take it as an input
(`inputs.rocq-deduxit.url = "github:deduxit/rocq-deduxit/v0.3.0"`)
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
  its `irules`) for a first-order two-sided one.

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

The documentation of every module is at
[deduxit.github.io/rocq-deduxit](https://deduxit.github.io/rocq-deduxit/)
(`nix build .#doc` builds it).

## What it covers

Every certificate deduxit 0.3.0 writes for `--kernel deduxit` compiles
against this library. That covers proofs in classical, Mix, affine and
intuitionistic linear logic and its affine variant, with or without cut,
propositional and first-order. It also covers refutations by the
classical reading, an atom's balance, the count equation and weighted
counts (a count of one sign under an exponential, a Horn program's state
equation), one-sided and two-sided; weighted counts also for
first-order sequents.

The library has no theorem for deduxit's other refutations, so deduxit
writes no certificate for them: a saturated set of the inverse method,
the count equation of a first-order sequent, and an exhaustive search.
Nor does it cover the ordered (cyclic) calculus, whose sequents keep
their order. It proves no cut elimination: balance and the counts are
stated for the calculi without cut, which are the ones deduxit refutes
in. On Rocq 9.2 and 9.3 it compiles with deprecation warnings
(`Notation` for an abbreviation, whose replacement 9.0 and 9.1 lack).

## Upgrading from rocq-linlog

Up to 0.2.0 the library was `rocq-linlog`, with the logical path
`Linlog`, in the repository `linlog-prover/rocq-linlog`. Its modules
are the same, now under `Deduxit.Linear`: `From Linlog Require Import
Soundness.` becomes `From Deduxit.Linear Require Import Soundness.`.

## The repository

- `theories/Linear/`: the library, `Deduxit.Linear`.
- `tests/`: certificates compiled against the installed library
  (`Deduxit.Linear.Tests`).
- `bridges/`: proofs that the calculi derive the same sequents as
  NanoYalla's `nanoll.v` and Yalla's `nanoill.v`
  (`Deduxit.Linear.Bridges`), compiled against the files the flake pins,
  never copied.

`nix flake check` builds the library with every Rocq it admits,
compiles every certificate under `tests/` and the bridges, and requires
every theorem's assumptions to be closed under the global context.
deduxit's own flake compiles the certificates its exporter writes
against this library. `scripts/opam-install.sh` installs the package
from its opam file into a fresh opam switch per Rocq version, as an
opam user would.

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
