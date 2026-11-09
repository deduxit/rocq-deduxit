# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

`rocq-deduxit` (logical root `Deduxit`) is the Rocq library of deduxit,
the collection of logic suites of `github.com/deduxit/deduxit` (named
linlog, the linear suite, until 0.3.0; the library was `rocq-linlog`,
logical path `Linlog`, up to 0.2.0). Each calculus has a namespace
under the root; today's, `Deduxit.Linear`, holds the
one-sided calculus of linear logic with Mix, weakening and cut as
parameters and the two-sided calculus of intuitionistic linear logic
and its affine variant as inductives, deduxit's proof terms as
datatypes, checkers as functions and the theorems that a term they
accept proves its sequent, the invariants every derivation keeps (the
refutations), the reduction of Mix to `?(⊥⊗⊥)`, and a first-order
development beside the propositional one. Rocq 9.0 to 9.3 with its
standard library and nothing else, each tested by the flake. It lived under `rocq/` of deduxit's
repository until 2026-11-02; its history up to then is that repository's.
The local directory keeps the name `rocq-linlog`.

The library's shape (the author, 2026-11-09): one logical root, a
namespace per calculus (`Deduxit.Linear` now, `Deduxit.Intuitionistic`
and `Deduxit.Modal` when those calculi come), each with its own formulas
and rules; theorems that connect calculi in a namespace of their own
(`Deduxit.Embeddings`); `Deduxit.Base` only once two calculi share a
lemma. One opam package, split into packages under the same root only
when a calculus brings a heavy dependency or a long build, or users want
one part alone, so that no path ever changes.

- `theories/` the library (`theories/Linear/` is `Deduxit.Linear`),
  `_RocqProject` and `Makefile` its build, `rocq-deduxit.opam` its
  package (the flake reads its `version:`).
- `tests/` certificates the check compiles against the installed
  library, as `Deduxit.Linear.Tests`, `Assumptions.v` the theorems
  whose assumptions must be closed, each by its full name.
- `bridges/` (`Deduxit.Linear.Bridges`) the equivalences with NanoYalla's `nanoll.v` and Yalla's
  `nanoill.v`, compiled against the flake inputs `nanoyalla` and
  `yalla`, never copied (LGPL); not part of the package.

`.claude/rules/rocq.md` loads for any of these files and holds the
library's invariants: its trusted base, the modules, how the checker
reads deduxit's Rust algorithm, the certificates, where a rule or a
calculus plugs in. Read it before changing the library, and record
there, one point per bullet, what a later session must know and cannot
see in the code.

## deduxit depends on this repository

deduxit's flake (the checkout `../linlog`) takes this one as a pinned
input, locked to a commit of `main` (its nixpkgs following deduxit's,
so one Rocq builds both), and compiles against this flake's package
every certificate its exporter writes for its kernel of this library
(its snapshots `core/tests/snapshots/deduxit/` and some the command
writes). That flake names the input `rocq-deduxit`, its checks
`rocq-deduxit` and `rocq-deduxit-library`, the kernel `--kernel
deduxit`, the preludes `From Deduxit.Linear Require …` and the constant
`export::rocq::DEDUXIT`, whose value must equal the opam file's
version, an assertion of that flake. So a
change of a statement, a rule, a record field, a proof term's
constructor or a path breaks deduxit's certificates at its next lock
update: change the exporter there in the same
step, and raise the version when the library is released.

## Commands

The devshell (`nix develop`, or direnv) has Rocq and its standard
library with `ROCQPATH` set.

```sh
make                                    # the library, in place
nix build                               # the package rocq-deduxit, as nixpkgs builds a Rocq library (result/lib/coq/9.1/user-contrib/Deduxit)
nix flake check                         # everything below
nix build .#checks.x86_64-linux.rocq-deduxit   # the library, every certificate under tests/, the theorems' assumptions closed (nixpkgs' default Rocq)
nix build .#checks.x86_64-linux.rocq-deduxit-9_0  # the same with Rocq 9.0 (and -9_2, -9_3: every version the opam file admits)
nix build .#doc                         # rocq doc's pages of every module, result/share/doc/rocq-deduxit
nix develop .#opam -c scripts/opam-install.sh 9.0.1 9.1.1 9.2.0 9.3.0   # opam lint, then the package installed from its opam file into a fresh switch per Rocq (network, about an hour)
nix build .#checks.x86_64-linux.rocq-bridges   # the bridges against the pinned nanoll.v and nanoill.v, and their assumptions
nix fmt                                 # nixfmt, taplo, shfmt, shellcheck, ruff-format (a hook runs it on each file changed with Write or Edit)
```

`nix flake check` runs `rocq-deduxit` and `rocq-deduxit-9_N`, `rocq-bridges`, `treefmt`,
`conventions` (the licence header on every source, no comment naming
the plan of deduxit's sessions), `typos` (`typos.toml`), `deadnix`,
`actionlint` (the workflow), `claude-hooks` (the guards under
`.claude/hooks`, their cases in `modules/claude-hooks.nix`) and
`claude-worktree-hook` (the worktree hook against a throwaway colocated
repository, `modules/claude-worktree-hook-test.py`). On this
machine, run it under the machine lock with few jobs: `flock -o
/tmp/linlog-machine.lock nix flake check --max-jobs 2 --cores 6`.
Every change that touches the library, a test or a bridge passes it.

## The flake

Dendritic flake-parts, as deduxit's: `flake.nix` only declares inputs,
and import-tree loads every `.nix` file under `modules/` (a path
segment starting with `_` skipped) as a flake-parts module, one aspect
per file; no file is ever added to an imports list. `rocq-deduxit.nix`
is the package, its check per admitted Rocq and the devshell; `doc.nix`
the documentation, with a page `Linlog.X.html` forwarding each of
0.2.0's deep links to `Deduxit.Linear.X.html`; `opam.nix` the shell `scripts/opam-install.sh` runs
in; `rocq-bridges.nix` the
bridges' check; `conventions.nix`, `treefmt.nix`, `claude-hooks.nix`
and `systems.nix` what their names say. The inputs are pinned as
deduxit pins them (the same nixpkgs channel tarball, NanoYalla and Yalla
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
remote `origin` (`github.com/deduxit/rocq-deduxit`, renamed from
`deduxit/rocq-linlog` on 2026-11-09; GitHub redirects the old address)
keep working.
**Never run git, not even to read**; the `Bash(git *)` deny rule and
`.claude/hooks/block-git.py` enforce it. Commit thematically, without
being asked, with `jj commit -m`; never `jj new -m` (a hook blocks it);
`jj squash` into a described parent needs `--use-destination-message`
or `-m` (in a Claude session jj's editor is `false`, so a command that
wants a description fails at once). Run `jj st` right before every commit, and after creating a
file before a `nix` command that must see it (nix sees only files in
the git tree). Subjects are short, imperative and capitalised. jj
writes commits unsigned (the machine's jj config): a global hook signs
a session's new commits right after the jj command that made them and
reports their new commit ids, and the push signs any still unsigned. A
lapsed passphrase cache stops no jj command and no commit: the hook
says which commits wait, and the first jj command after the author
unlocks, or the push, signs them; it does stop the push. Cite change
ids, or the commit ids the hook reported; never pass `--config
signing.behavior=…`. Pushing is outward-facing and the author's or the planning
session's (deduxit's `plan/push-main.sh --rocq REV`, which checks
`main@origin` by change id, since the push's signing gives commits new
ids); the GitHub CLI asks before every command.

## Conventions

- Every source file starts with the licence header in its comment
  syntax, `(* … *)` in Rocq and `#` in Nix, TOML, shell, Python, YAML,
  the Makefile and the opam file:
  ```
  (* deduxit © Fabian Lukas Grubmüller 2026 *)
  (* Licensed under the EUPL *)
  ```
  Markdown, JSON, `.gitignore`, `LICENSE` and the lock carry none. The
  library is EUPL-1.2, as deduxit is. The header names the project,
  deduxit, as deduxit's own files do, and the check looks for it.
- Every text a person reads (README, the doc comments and comments,
  the changelog, the opam description) follows
  `.claude/rules/writing.md`, a copy of deduxit's rule, the author's
  standing instruction of 2026-11-09: concise, plain language;
  self-contained; written for someone checking a certificate or proving
  with the library; free of the patterns that make text hard to read.
- Comments are short, say why or what the code cannot, and are
  self-contained: no reference to sessions, prompts or the plan that
  organised the work.
- Every proof ends in `Qed`: no `Admitted`, `admit`, `Axiom`,
  `Parameter` or `Conjecture` anywhere (the check greps for them).

## Claude Code setup

`.claude/` is checked in, as deduxit's: the guards `block-git.py` and
`block-jj-new-message.py` with their shared reading of a command line
`command_line.py` (copies of deduxit's; a change to one belongs in both
repositories, with its cases in `modules/claude-hooks.nix`), the
formatter hook `format.sh`, the SessionStart note `session-jj-state.sh`,
the worktree hook `jj-worktree.py` (a copy of deduxit's as well, its test
`modules/claude-worktree-hook-test.py`), the permission rules in
`settings.json`, the rules file `rocq.md` (loaded for the library's
files) and `writing.md` (no `paths:`, so it loads at launch, as
deduxit's does; a change to its four rules belongs in both
repositories).
`settings.json` also sets `attribution.sessionUrl` to `false` (the
author, 2026-11-03, for privacy), so no commit gets a `Claude-Session:`
link to its claude.ai session, as in deduxit. The hooks fail open, read the payload's `cwd`, and are plain Python or
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
