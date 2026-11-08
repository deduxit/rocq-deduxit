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
development beside the propositional one. Rocq 9.0 to 9.3 with its
standard library and nothing else, each tested by the flake. It lived under `rocq/` of linlog's
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
nix build .#checks.x86_64-linux.rocq-linlog    # the library, every certificate under tests/, the theorems' assumptions closed (nixpkgs' default Rocq)
nix build .#checks.x86_64-linux.rocq-linlog-9_0   # the same with Rocq 9.0 (and -9_2, -9_3: every version the opam file admits)
nix build .#doc                         # rocq doc's pages of every module, result/share/doc/rocq-linlog
nix develop .#opam -c scripts/opam-install.sh 9.0.1 9.1.1 9.2.0 9.3.0   # opam lint, then the package installed from its opam file into a fresh switch per Rocq (network, about an hour)
nix build .#checks.x86_64-linux.rocq-bridges   # the bridges against the pinned nanoll.v and nanoill.v, and their assumptions
nix fmt                                 # nixfmt, taplo, shfmt, shellcheck, ruff-format (a hook runs it on each file changed with Write or Edit)
```

`nix flake check` runs `rocq-linlog` and `rocq-linlog-9_N`, `rocq-bridges`, `treefmt`,
`conventions` (the licence header on every source, no comment naming
the plan of linlog's sessions), `typos` (`typos.toml`), `deadnix`,
`actionlint` (the workflow), `claude-hooks` (the guards under
`.claude/hooks`, their cases in `modules/claude-hooks.nix`) and
`claude-worktree-hook` (the worktree hook against a throwaway colocated
repository, `modules/claude-worktree-hook-test.py`). On this
machine, run it under the machine lock with few jobs: `flock -o
/tmp/linlog-machine.lock nix flake check --max-jobs 2 --cores 6`.
Every change that touches the library, a test or a bridge passes it.

## The flake

Dendritic flake-parts, as linlog's: `flake.nix` only declares inputs,
and import-tree loads every `.nix` file under `modules/` (a path
segment starting with `_` skipped) as a flake-parts module, one aspect
per file; no file is ever added to an imports list. `rocq-linlog.nix`
is the package, its check per admitted Rocq and the devshell; `doc.nix`
the documentation; `opam.nix` the shell `scripts/opam-install.sh` runs
in; `rocq-bridges.nix` the
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
`.github/workflows/release.yml` releases a tag `vX.Y.Z`: the tag must
equal the opam file's and the citation file's version and the changelog
must have its dated section, then `nix flake check`, a GitHub release
with the changelog's section and the SHA-512 of the tag's source archive
(what the Rocq opam archive's file needs), and the documentation on
Pages, whose source the author sets to "GitHub Actions" before the
first tag. The tag, the release's date and the opam-repository pull
request are the author's.

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
the worktree hook `jj-worktree.py` (a copy of linlog's as well, its test
`modules/claude-worktree-hook-test.py`), the permission rules in
`settings.json` and the rules file `rocq.md`.
`settings.json` also sets `attribution.sessionUrl` to `false` (the
author, 2026-11-03, for privacy), so no commit gets a `Claude-Session:`
link to its claude.ai session, as in linlog. The hooks fail open, read the payload's `cwd`, and are plain Python or
shell; `jq` is not installed on this machine. When the repository
changes shape, amend `.claude/` and this file in the same change.

`jj-worktree.py` runs for `WorktreeCreate` and `WorktreeRemove` in place
of Claude Code's git worktrees (a sub-agent's `isolation: "worktree"`,
`--worktree`, a background session, a workflow agent): in this colocated
repository a git worktree under `.claude/worktrees/` is one jj does not
know, and a jj command there acts on the main workspace. It makes a jj
workspace `wt-NAME` in `../rocq-linlog-wt-NAME` on `@-` of the session's
workspace (committed work only, as git's HEAD), copies what
`.worktreeinclude` names, and on removal deletes only a workspace it made
whose `@` is empty, exiting 1 otherwise, since Claude Code's check for
uncommitted work reads git and sees nothing there. It alone fails
closed: a creation that goes wrong exits 1 and Claude Code makes no
worktree, the safe side. Claude Code keeps the workspaces of sub-agents
and workflow agents and never asks to remove them: once their commits
are taken, `.claude/hooks/jj-worktree.py prune` removes every empty one.
