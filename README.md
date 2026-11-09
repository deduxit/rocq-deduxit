# <picture><source media="(prefers-color-scheme: dark)" srcset="https://deduxit.github.io/logo/wordmark-dark.svg"><img alt="deduxit" src="https://deduxit.github.io/logo/wordmark-light.svg" height="80"></picture> in Rocq

> **dēdūxit** [deːˈduːk.sɪt] *Latin, verb*: "it has derived", the perfect of *dēdūcō*, to lead down, derive.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23899109.svg)](https://doi.org/10.5281/zenodo.23899109)

`rocq-deduxit`, logical root `Deduxit`: the Rocq library of
[deduxit](https://github.com/deduxit/deduxit), a collection of logic
suites, on Rocq 9 and its standard library alone. Each calculus has a
namespace of its own under the root. Today's is `Deduxit.Linear`, linear
logic: the one-sided sequent calculus, with Mix, weakening and cut as
parameters, and the two-sided calculus of intuitionistic linear logic
and its affine variant, with cut as a parameter, as inductives;
deduxit's proof terms as datatypes, checkers as functions, and for every
mode the theorem that a term the checker accepts proves its sequent. A
certificate that deduxit writes (`deduxit prove --format rocq --kernel
deduxit`) is the sequent, the term and one computation. The invariants
every derivation keeps (the classical reading, an atom's balance, the
count equation, and weighted counts where copies add literals of one
sign or a Horn program's state equation fails) give certificates that
a sequent is not derivable. A
first-order development stands beside the propositional one: terms with
de Bruijn indices and eigenvariables, both calculi with the quantifier
rules and the eigenvariable condition, the first-order proof terms,
their checkers and the same theorems in every mode.

```coq
From Deduxit.Linear Require Import Soundness.
```

- `theories/Linear/`: the library's `Deduxit.Linear`. `Formulas.v` and
  `Calculus.v` (the one-sided calculus) and `Intuitionistic.v` (the
  two-sided one), and for first-order statements `Terms.v` with
  `FirstOrderFormulas.v` and `FirstOrderCalculus.v` or with
  `FirstOrderIntuitionistic.v`, are what a certificate's statement rests
  on; the checkers and their proofs appear in the proofs alone.
- `tests/`: certificates compiled against the installed library
  (`Deduxit.Linear.Tests`).
- `bridges/`: the calculi proved equivalent to NanoYalla's `nanoll.v`
  and Yalla's `nanoill.v` (`Deduxit.Linear.Bridges`), compiled against
  the files the repository's flake pins, never copied.

Up to 0.2.0 the library was `rocq-linlog`, with the logical path
`Linlog`, in the repository `deduxit/rocq-linlog`; its modules are the
same, under `Deduxit.Linear`, so `From Linlog Require Import Soundness.`
becomes `From Deduxit.Linear Require Import Soundness.`.

## Install

The library needs Rocq 9.0, 9.1, 9.2 or 9.3 and its standard library; it
is tested with each.

**With opam**, from the [Rocq opam archive](https://rocq-prover.org/docs/using-opam)
once the release is there, or meanwhile from its tag:

```sh
opam repo add rocq-released https://rocq-prover.org/opam/released   # once
opam install rocq-deduxit                                            # from the archive
opam pin add rocq-deduxit https://github.com/deduxit/rocq-deduxit.git#v0.3.0   # or from the tag
opam upgrade rocq-deduxit                                            # later: a newer release from the archive
opam remove rocq-deduxit                                             # and to remove it
```

A package pinned to a tag stays at that tag: `opam pin add` with the
next tag moves it, and `opam unpin rocq-deduxit` before `opam install`
takes the archive's instead.

**With Nix**, the flake's default package is the library built against
nixpkgs' Rocq 9.1 (flakes enabled):

```sh
nix build github:deduxit/rocq-deduxit/v0.3.0    # result/lib/coq/9.1/user-contrib/Deduxit
```

In a flake of your own, take it as an input
(`inputs.rocq-deduxit.url = "github:deduxit/rocq-deduxit/v0.3.0"`)
and put `rocq-deduxit.packages.${system}.default` beside
`rocqPackages.rocq-core` and `rocqPackages.stdlib` in a shell's
packages; nixpkgs' Rocq setup hook puts it on the load path.

**From the source**, `make` builds it in place with Rocq and its
standard library on the path (`nix develop` gives both) and `make
install` installs it into Rocq's `user-contrib`.

Then compile a certificate that deduxit writes:

```console
$ deduxit prove --mix --format rocq --standalone --output mix.v "A, B |- A, B"
$ rocq compile mix.v                                                  # installed
$ rocq compile -Q path/to/rocq-deduxit/theories Deduxit mix.v         # built in place
```

The documentation of every module is at
[deduxit.github.io/rocq-deduxit](https://deduxit.github.io/rocq-deduxit/)
(`nix build .#doc` builds it).

## What it covers, and what not

Every certificate deduxit 0.3.0 writes for `--kernel deduxit` compiles
against this library and rests on its theorems, whose assumptions are
closed: proofs of classical, Mix, affine and intuitionistic linear
logic and its affine variant, with or without cut, propositional and
first-order, and refutations by the classical reading, an atom's
balance, the count equation and weighted counts (a count of one sign
under an exponential, a Horn program's state equation), one-sided and
two-sided, the weighted counts of first-order sequents among them. It
has no theorem for deduxit's other refutations, so deduxit writes no
certificate for them: a saturated set of the inverse method, the count
equation of a first-order sequent, and a search that was exhaustive;
nor for the ordered (cyclic) calculus, whose sequents keep their order.
It proves no cut elimination: balance and the counts are stated for the
calculi without cut, the ones deduxit's refutations are about. On Rocq
9.2 and 9.3 it compiles with deprecation warnings (`Notation` for an
abbreviation, whose replacement 9.0 and 9.1 lack).

## Checks

`nix flake check` builds the library with every Rocq it admits,
compiles every certificate under `tests/` and the bridges, and requires
every theorem's assumptions to be closed under the global context.
deduxit's own flake takes this one as an input and compiles the
certificates its exporter writes against it.
`scripts/opam-install.sh` installs the package from its opam file into a
fresh opam switch per Rocq version, as a user of opam would.

The library was part of deduxit's repository, under its first name
linlog, until it moved here; its history up to the move is that
repository's (`CHANGELOG.md`). It is licensed under the EUPL-1.2, as
deduxit is. The mark above is deduxit's, under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/), served from
[deduxit's site](https://deduxit.github.io/logo/LICENSE.txt).

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
