# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

`rocq-linlog` (logical path `Linlog`) is the Rocq library of linlog,
the linear logic prover of `github.com/linlog-prover/linlog`: the
one-sided calculus of linear logic with Mix, weakening and cut as
parameters and the two-sided calculus of intuitionistic linear logic
and its affine variant as inductives, linlog's proof terms as
datatypes, checkers as functions and the theorems that a term they
accept proves its sequent, the invariants every derivation keeps (the
refutations), the reduction of Mix to `?(⊥⊗⊥)`, and a first-order
development beside the propositional one. Rocq 9.0 or 9.1 with its
standard library and nothing else. It lived under `rocq/` of linlog's
repository until 2026-11-02; its history up to then is linlog's.

- `theories/` the library, `_RocqProject` and `Makefile` its build,
  `rocq-linlog.opam` its package (the flake reads its `version:`).
- `tests/` certificates the check compiles against the installed
  library, `Assumptions.v` the theorems whose assumptions must be closed.
- `bridges/` the equivalences with NanoYalla's `nanoll.v` and Yalla's
  `nanoill.v`, compiled against the flake inputs `nanoyalla` and
  `yalla`, never copied (LGPL); not part of the package.

`.claude/rules/rocq.md` loads for any of these files and holds the
library's invariants: its trusted base, the modules, how the checker
reads linlog's Rust algorithm, the certificates, where a rule or a
calculus plugs in. Read it before changing the library, and record
there, one point per bullet, what a later session must know and cannot
see in the code.

## linlog depends on this repository

linlog's flake takes this one as the input `rocq-linlog`, pinned by its
lock to a commit of `main` (its nixpkgs following linlog's, so one
Rocq builds both), and compiles against `packages.rocq-linlog` every
certificate its exporter writes for `--kernel linlog` (its snapshots
`core/tests/snapshots/linlog/` and some the command writes). Its
constant `export::rocq::LINLOG` must equal the opam file's version, an
assertion of linlog's flake. So a change of a statement, a rule, a
record field or a proof term's constructor breaks linlog's certificates
at linlog's next lock update: change the exporter there in the same
step, and raise the version when the library is released.

## Commands

The devshell (`nix develop`, or direnv) has Rocq and its standard
library with `ROCQPATH` set.

```sh
make                                    # the library, in place
nix build                               # the package rocq-linlog, as nixpkgs builds a Rocq library
nix flake check                         # everything below
nix build .#checks.x86_64-linux.rocq-linlog    # the library, every certificate under tests/, the theorems' assumptions closed
nix build .#checks.x86_64-linux.rocq-bridges   # the bridges against the pinned nanoll.v and nanoill.v, and their assumptions
nix fmt                                 # nixfmt, taplo, shfmt, shellcheck, ruff-format (a hook runs it on each file changed with Write or Edit)
```

`nix flake check` runs `rocq-linlog`, `rocq-bridges`, `treefmt`,
`conventions` (the licence header on every source, no comment naming
the plan of linlog's sessions), `typos` (`typos.toml`), `deadnix`,
`actionlint` (the workflow) and `claude-hooks` (the guards under
`.claude/hooks`, their cases in `modules/claude-hooks.nix`). On this
machine, run it under the machine lock with few jobs: `flock -o
/tmp/linlog-machine.lock nix flake check --max-jobs 2 --cores 6`.
Every change that touches the library, a test or a bridge passes it.

## The flake

Dendritic flake-parts, as linlog's: `flake.nix` only declares inputs,
and import-tree loads every `.nix` file under `modules/` (a path
segment starting with `_` skipped) as a flake-parts module, one aspect
per file; no file is ever added to an imports list. `rocq-linlog.nix`
is the package, its check and the devshell; `rocq-bridges.nix` the
bridges' check; `conventions.nix`, `treefmt.nix`, `claude-hooks.nix`
and `systems.nix` what their names say. The inputs are pinned as
linlog pins them (the same nixpkgs channel tarball, NanoYalla and Yalla
at the same commits); a lock bump is a change of its own,
"flake.lock: Update".

## CI

`.github/workflows/ci.yml` runs `nix flake check` on every push to
`main`, every pull request, weekly and by dispatch, with nothing
installed but Nix, and pulls from the public Cachix cache
`linlog-prover`. It pushes to the cache from `main` only once the
repository has the secret `CACHIX_AUTH_TOKEN`, which is the author's
to add; until then it only downloads. Every action is pinned to a full
commit SHA with the release as a comment (the organization requires
it); Dependabot proposes the bumps (`.github/dependabot.yml`).
`permissions: contents: read`, `persist-credentials: false`.

## Version control: jj only

A jj repository, colocated with git only so that nix and the GitHub
remote `origin` (`github.com/linlog-prover/rocq-linlog`) keep working.
**Never run git, not even to read**; the `Bash(git *)` deny rule and
`.claude/hooks/block-git.py` enforce it. Commit thematically, without
being asked, with `jj commit -m`; never `jj new -m` (a hook blocks it);
`jj squash` into a described parent needs `--use-destination-message`
or `-m`. Run `jj st` right before every commit, and after creating a
file before a `nix` command that must see it (nix sees only files in
the git tree). Subjects are short, imperative and capitalised. jj
signs every commit; when the key's passphrase is no longer cached,
every jj command that writes fails: finish what needs no commit and ask
the author. Pushing is outward-facing and the author's or the planning
session's (linlog's `plan/push-main.sh --rocq REV`); the GitHub CLI asks
before every command.

## Conventions

- Every source file starts with the licence header in its comment
  syntax, `(* … *)` in Rocq and `#` in Nix, TOML, shell, Python, YAML,
  the Makefile and the opam file:
  ```
  (* linlog © Fabian Lukas Grubmüller 2026 *)
  (* Licensed under the EUPL *)
  ```
  Markdown, JSON, `.gitignore`, `LICENSE` and the lock carry none. The
  library is EUPL-1.2, as linlog is.
- Comments are short, say why or what the code cannot, and are
  self-contained: no reference to sessions, prompts or the plan that
  organised the work.
- Every proof ends in `Qed`: no `Admitted`, `admit`, `Axiom`,
  `Parameter` or `Conjecture` anywhere (the check greps for them).

## Claude Code setup

`.claude/` is checked in, as linlog's: the guards `block-git.py` and
`block-jj-new-message.py` with their shared reading of a command line
`command_line.py` (copies of linlog's; a change to one belongs in both
repositories, with its cases in `modules/claude-hooks.nix`), the
formatter hook `format.sh`, the SessionStart note `session-jj-state.sh`,
the permission rules in `settings.json` and the rules file `rocq.md`.
The hooks fail open, read the payload's `cwd`, and are plain Python or
shell; `jq` is not installed on this machine. When the repository
changes shape, amend `.claude/` and this file in the same change.
