# <picture><source media="(prefers-color-scheme: dark)" srcset="https://deduxit.github.io/logo/wordmark-dark.svg"><img alt="linlog" src="https://deduxit.github.io/logo/wordmark-light.svg" height="80"></picture> in Rocq

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23899109.svg)](https://doi.org/10.5281/zenodo.23899109)

`rocq-linlog`, logical path `Linlog`: the Rocq library of
[linlog](https://github.com/deduxit/deduxit), a prover of classical
and intuitionistic linear logic, on Rocq 9 and its standard library
alone. It holds the one-sided sequent calculus of linear logic, with Mix,
weakening and cut as parameters, and the two-sided calculus of
intuitionistic linear logic and its affine variant, with cut as a
parameter, as inductives;
linlog's proof terms as datatypes, checkers as functions, and for every
mode the theorem that a term the checker accepts proves its sequent. A
certificate that linlog writes (`linlog prove --format rocq --kernel
linlog`) is the sequent, the term and one computation. The invariants
every derivation keeps (the classical reading, an atom's balance, the
count equation, and weighted counts where copies add literals of one
sign or a Horn program's state equation fails) give certificates that
a sequent is not derivable. A
first-order development stands beside the propositional one: terms with
de Bruijn indices and eigenvariables, both calculi with the quantifier
rules and the eigenvariable condition, the first-order proof terms,
their checkers and the same theorems in every mode.

- `theories/`: the library. `Formulas.v` and `Calculus.v` (the one-sided
  calculus) and `Intuitionistic.v` (the two-sided one), and for
  first-order statements `Terms.v` with `FirstOrderFormulas.v` and
  `FirstOrderCalculus.v` or with `FirstOrderIntuitionistic.v`, are what a
  certificate's statement rests on; the checkers and their proofs
  appear in the proofs alone.
- `tests/`: certificates compiled against the installed library.
- `bridges/`: the calculi proved equivalent to NanoYalla's `nanoll.v`
  and Yalla's `nanoill.v`, compiled against the files the repository's
  flake pins, never copied.

## Install

The library needs Rocq 9.0, 9.1, 9.2 or 9.3 and its standard library; it
is tested with each.

**With opam**, from the [Rocq opam archive](https://rocq-prover.org/docs/using-opam)
once the release is there, or meanwhile from its tag:

```sh
opam repo add rocq-released https://rocq-prover.org/opam/released   # once
opam install rocq-linlog                                             # from the archive
opam pin add rocq-linlog https://github.com/deduxit/rocq-linlog.git#v0.2.0   # or from the tag
opam upgrade rocq-linlog                                             # later: a newer release from the archive
opam remove rocq-linlog                                              # and to remove it
```

A package pinned to a tag stays at that tag: `opam pin add` with the
next tag moves it, and `opam unpin rocq-linlog` before `opam install`
takes the archive's instead.

**With Nix**, the flake's default package is the library built against
nixpkgs' Rocq 9.1 (flakes enabled):

```sh
nix build github:deduxit/rocq-linlog/v0.2.0    # result/lib/coq/9.1/user-contrib/Linlog
```

In a flake of your own, take it as an input
(`inputs.rocq-linlog.url = "github:deduxit/rocq-linlog/v0.2.0"`)
and put `rocq-linlog.packages.${system}.default` beside
`rocqPackages.rocq-core` and `rocqPackages.stdlib` in a shell's
packages; nixpkgs' Rocq setup hook puts it on the load path.

**From the source**, `make` builds it in place with Rocq and its
standard library on the path (`nix develop` gives both) and `make
install` installs it into Rocq's `user-contrib`.

Then compile a certificate that linlog writes:

```console
$ linlog prove --mix --format rocq --standalone --output mix.v "A, B |- A, B"
$ rocq compile mix.v                                                  # installed
$ rocq compile -R path/to/rocq-linlog/theories Linlog mix.v           # built in place
```

The documentation of every module is at
[deduxit.github.io/rocq-linlog](https://deduxit.github.io/rocq-linlog/)
(`nix build .#doc` builds it).

## What it covers, and what not

Every certificate linlog 0.2.0 writes for `--kernel linlog` compiles
against this library and rests on its theorems, whose assumptions are
closed: proofs of classical, Mix, affine and intuitionistic linear
logic and its affine variant, with or without cut, propositional and
first-order, and refutations by the classical reading, an atom's
balance and the count equation, one-sided and two-sided. It has no
theorem for linlog's other refutations, so linlog writes no certificate
for them: a count of one sign under an exponential, a Petri net's state
equation, a saturated set of the inverse method, and any refutation of
a first-order sequent; nor for the ordered (cyclic) calculus, whose
sequents keep their order. It proves no cut elimination: balance and
the count equation are stated for the calculi without cut, the ones
linlog's refutations are about. On Rocq 9.2 and 9.3 it compiles with
deprecation warnings (`Notation` for an abbreviation, whose replacement
9.0 and 9.1 lack).

## Checks

`nix flake check` builds the library with every Rocq it admits,
compiles every certificate under `tests/` and the bridges, and requires
every theorem's assumptions to be closed under the global context.
linlog's own flake takes this one as an input and compiles the
certificates its exporter writes against it.
`scripts/opam-install.sh` installs the package from its opam file into a
fresh opam switch per Rocq version, as a user of opam would.

The library was part of linlog's repository until it moved here; its
history up to the move is linlog's (`CHANGELOG.md`). It is licensed
under the EUPL-1.2, as linlog is. The logo above is linlog's, under
CC BY 4.0, served from linlog's site.

## Citing

Each release is archived on Zenodo. To cite the library, use the DOI
[10.5281/zenodo.23899109](https://doi.org/10.5281/zenodo.23899109),
which always resolves to the latest version, or the DOI of the version
you used, which its Zenodo record gives (0.2.0's is
[10.5281/zenodo.23899110](https://doi.org/10.5281/zenodo.23899110)).
[`CITATION.cff`](CITATION.cff) holds the entry, and GitHub's "Cite this
repository" writes it as BibTeX or APA. linlog has a DOI of its own,
[10.5281/zenodo.23448588](https://doi.org/10.5281/zenodo.23448588).
