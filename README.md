# <picture><source media="(prefers-color-scheme: dark)" srcset="https://linlog-prover.github.io/logo/wordmark-dark.svg"><img alt="linlog" src="https://linlog-prover.github.io/logo/wordmark-light.svg" height="80"></picture> in Rocq

`rocq-linlog`, logical path `Linlog`: the Rocq library of
[linlog](https://github.com/linlog-prover/linlog), a prover of classical
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
count equation) give certificates that a sequent is not derivable. A
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

Build it with `make` (Rocq 9.0 or 9.1 and its standard library on the
path; `nix develop` gives both), or with `nix build`, and compile a
certificate with the theories on the load path:

```console
$ linlog prove --mix --format rocq --standalone --output mix.v "A, B |- A, B"
$ rocq compile -R path/to/rocq-linlog/theories Linlog mix.v
```

`nix flake check` builds the library, compiles every certificate under
`tests/` and the bridges, and requires every theorem's assumptions to be
closed under the global context. linlog's own flake takes this one as an
input and compiles the certificates its exporter writes against it.

The library was part of linlog's repository until it moved here; its
history up to the move is linlog's (`CHANGELOG.md`). It is licensed
under the EUPL-1.2, as linlog is. The logo above is linlog's, under
CC BY 4.0, served from linlog's site.
