---
paths:
  - "theories/**"
  - "tests/**"
  - "bridges/**"
  - "_RocqProject"
  - "Makefile"
  - "rocq-deduxit.opam"
---

# The Rocq library

Loaded when a file of the library, its tests, its bridges or its build is
read or changed. `modules/rocq-deduxit.nix` builds and checks it
(CLAUDE.md). deduxit's exporter writes certificates for it as its second
kernel (in deduxit's repository, the checkout `../deduxit`,
`core/src/export/rocq/deduxit.rs` and its rules `core-export.md`), beside
the NanoYalla export, which it leaves as it was; deduxit's flake compiles
them against this library, taken as a pinned input. Paths of the form
`core/…` below are deduxit's.

- **deduxit re-exports this check.** deduxit's flake check
  `rocq-deduxit-library` is this repository's
  `checks.SYSTEM.rocq-deduxit` through its pinned input, so a commit
  whose check fails here fails deduxit's `nix flake check` once its lock
  moves to it; its own check `rocq-deduxit` compiles the exporter's
  certificates against `packages.rocq-deduxit` and requires each
  `certificate`'s assumptions closed.
- **The Rocq versions.** The opam file admits Rocq 9.0 to 9.3
  (`rocq-core {>= "9.0" & < "9.4~"}`) and `rocq-stdlib {>= "9.0" &
  < "9.3~"}`: the standard library's versions do not follow Rocq's, so
  its bound is its own (opam had 9.0.0, 9.1.0 and 9.2.0 on 2026-11-27;
  9.3 takes 9.2.0, which asks `rocq-core >= 9.1`). nixpkgs pairs 9.0 and
  9.1 with stdlib 9.0.0, so opam's other pairs (9.0 with 9.1.0, 9.1 with
  9.2.0) are tested by the opam job alone. `modules/rocq-deduxit.nix`
  checks each admitted version through nixpkgs' `rocqPackages_9_N`, and a
  new Rocq is a line of `admitted`, a raised bound and an entry of
  `.github/workflows/opam.yml`'s matrix together. On 9.2
  and 9.3 the theories compile with the deprecation of `Notation` for an
  abbreviation; its replacement `Abbreviation` exists only from 9.2, so
  it waits until 9.0 and 9.1 are dropped. `scripts/opam-install.sh`
  installs the package as opam users do, into a fresh switch per
  version, outside the flake's checks since it needs the network;
  `opam.yml` runs it on GitHub's runners for CI and the release.
- **The check's build is strict, the package is not.** `checkFor`
  builds the library with `COQEXTRAFLAGS` (`-w +default`, every warning
  Rocq gives by default an error, and `-set "Default Goal Selector=!"`),
  which `rocq makefile`'s makefile reads from the environment; the
  package keeps Rocq's defaults, since an opam user's `make` with a
  later Rocq may warn where the admitted ones do not. The selector
  cannot go into `_RocqProject`: `rocq makefile` splits an `-arg` value
  at its spaces. Two warnings of 9.2 stay plain warnings, by name, since
  what they ask for does not exist on 9.0 and 9.1:
  `notation-for-abbreviation` (the abbreviations, above) and
  `register-all` (`Terms.v`'s `term` is nested in `list`, for which 9.2
  wants `Scheme All`); each leaves the list when 9.0 and 9.1 are
  dropped, or the abbreviations are written out. Rocq ignores an
  unknown warning name in `-w` silently, so a name there is checked by
  a planted warning, not by the build.
- **The certificates' interface** is `tests/Interface/`, a file per
  prelude of deduxit's exporter (`core/src/export/rocq/mod.rs`'s
  `DEDUXIT_*_PRELUDE`), which starts with that prelude verbatim and
  uses, by `Definition`s that print nothing, every name a certificate
  writes: each constructor applied to its arguments, each record as a
  literal of all its fields (a literal missing a field is refused),
  each theorem applied as the certificate applies it, with its
  conclusion stated (`_ = true -> ll (atom := string) … l`). The list
  was taken from the `.glob` files of every certificate deduxit's tests
  and flake check write (108 on 2026-11-27) and completed with the
  constructors no certificate happened to use and the exporter's paths
  no certificate reached (the first-order `soundness_mix`, which the
  review found missing): a name the exporter writes is read from its
  code, not only from the certificates. README's section of the
  same name lists it; a new name the exporter writes joins both.
- **README's Rocq examples compile**: the check writes each ```` ```coq
  ```` block to a file of its own (two define `excluded_middle`) and
  compiles it in silence. Its `console` block runs deduxit, which this
  flake does not have, so nothing runs it.
- **Logical paths.** One root, `Deduxit`, mapped by `-Q theories
  Deduxit`: `-Q` because Rocq loads an installed library so, and every
  `Require` here names its path with `From`, which the reference
  manual encourages, so the build sees exactly the paths a user sees. A
  calculus is a directory under `theories/` and a namespace under the
  root (`theories/Linear/` is `Deduxit.Linear`); a new one is a new
  directory and its files in `_RocqProject`, and connecting theorems go
  to `Deduxit.Embeddings`, shared lemmas to `Deduxit.Base` once two
  calculi need one. The tests compile as `Deduxit.Linear.Tests` (`-Q .
  Deduxit.Linear.Tests` in the check) and the bridges as
  `Deduxit.Linear.Bridges`, in the namespace of the calculus they
  test. A test file named as a theory (`Refutations.v`, `Weights.v`)
  does not shadow it: `From Deduxit.Linear Require Refutations` takes
  the exact path `Deduxit.Linear.Refutations` before the test's
  `Deduxit.Linear.Tests.Refutations` (tried on Rocq 9.1). The package
  installs into `user-contrib/Deduxit/Linear`. `tests/Assumptions.v` and
  `bridges/Assumptions.v` name every theorem by its full path, so the
  list the check counts shows where each one lives.
- **Layout.** `_RocqProject` (`-Q theories Deduxit`, every file listed),
  `Makefile` (the reference manual's wrapper: it generates `RocqMakefile`
  from `_RocqProject` with `rocq makefile` and hands it every target, so
  `make` builds and `make install` installs under `COQLIBINSTALL`),
  `rocq-deduxit.opam` (the archive's name for the library; the flake
  reads its `version:`, which equals deduxit's `export::rocq::DEDUXIT`), `README.md` (the library's front page:
  deduxit's word mark by URL from the site,
  `https://deduxit.github.io/logo/wordmark-{light,dark}.svg`, under CC
  BY 4.0, and the dictionary line under it; no logo file is in the
  repository), `theories/` (the library, logical root `Deduxit`) and
  `tests/` (certificates the check compiles against the installed library,
  not part of it) and `bridges/` (the equivalences with NanoYalla and
  `nanoill.v`, not part of the package either, compiled by the check
  `rocq-bridges`). The build's artifacts (`.vo`, `.vos`, `.vok`, `.glob`,
  `.*.aux`, `RocqMakefile`, `RocqMakefile.conf`, `.lia.cache`) are
  ignored; `make` needs Rocq and its standard library, which `nix
  develop` (the flake's devshell) puts on the path with `ROCQPATH` set.
- **The trusted base is `Formulas.v` and `Calculus.v`** for the one-sided
  statements and **`Intuitionistic.v`** for the two-sided ones, and for
  the first-order statements **`Terms.v`, `FirstOrderFormulas.v` and
  `FirstOrderCalculus.v`** (one-sided, with `Calculus.v` for its
  `rules`) and **`Terms.v` and `FirstOrderIntuitionistic.v`** (two-sided,
  with `Intuitionistic.v` for its `irules`), nothing else; the
  first-order trusted files hold definitions alone (the equalities,
  `teigens`, `feigens`, `is_wn` are in `TermsCheck.v` and the checkers): a certificate's lemma states `ll R Γ` or `ill R Γ C` over them,
  and the checkers (`Check.v`, `IntuitionisticCheck.v`) and their proofs
  appear in the proof only. `Intuitionistic.v` holds `iformula`, `irules`
  (`intuitionistic`, `affine`) and `ill` alone: the two-sided formulas'
  equality is in `IntuitionisticCheck.v`, which the review of the
  two-sided calculus asked for so that the trusted file derives nothing. A
  change of a rule changes what every certificate means; a fresh reader
  compared the inductive with a textbook presentation of one-sided
  classical linear logic and with NanoYalla's `nanoll.v` before it was
  committed, and a change gets the same reading.
- **The modules**, the one-sided ones each exporting the one before: `Formulas` (negation
  normal form over an abstract atom type, the constructors named as in
  Yalla and NanoYalla, `dual`, `formula_eqb` and `formula_eqb_spec` under a
  reflecting atom equality, `formula_eq_dec` for the proofs); `Calculus`
  (`rules` with `mix`, `weakening` and `cut`, `classical` with none of
  them, `ll R` with exchange as one `Permutation` rule, every other rule
  on the first formula, and `cut_r` under `cut R`, `⊢ Γ, Δ` from
  `⊢ A, Γ` and `⊢ A⊥, Δ`); `Proofs` (`branch`, `proof`: one constructor per `Node` variant of
  `core/src/proofs/mod.rs`, in the variants' order, naming formulas rather
  than occurrences); `Check` (`remove_one`, `remove_all`, `take_all`,
  `diff`, `take`, instances of `Multiset`'s; `state`, `join_with`,
  `derive`, `check`); `Soundness` (`sat`, `derive_sound`, `soundness`,
  `soundness_classical`, `soundness_mix`, `soundness_affine`, and `perm`,
  the tactic that decides a permutation of formula lists by `count_occ`
  and `lia`). Beside them, importing nothing of theirs: `Intuitionistic`
  (`iformula` with the constructors of Yalla's `nanoill.v`, `ivar`,
  `ione`, `itens`, `ilmap`, `itop`, `iwith`, `izero`, `iplus`, `ioc`;
  `irules` with `iweakening` and `icut`; `ill R Γ C`, the rules of
  `nanoill.v` with exchange as one `Permutation` rule, `weakening_ilr`
  under `iweakening` and `cut_ir` under `icut`, `Γ, Δ ⊢ C` from `Γ ⊢ A`
  and `A, Δ ⊢ C`, which `nanoill.v` lacks) and `IntuitionisticCheck`
  (`iformula_eqb`, the two-sided term `iproof`, one constructor per
  two-sided rule, `pick`, `same`, `unoc`, `cut_by`, `icut_conclusion`,
  `iderive`, `icheck`, `soundness_ill`).
- **Atoms are a parameter** (`Context {atom : Type}`): the calculus
  assumes nothing of them, the checker takes `atom_eqb : atom -> atom ->
  bool`, and the theorem assumes `forall a b, reflect (a = b) (atom_eqb a
  b)`. The certificates use `string` with `String.eqb` and
  `String.eqb_spec`; a sequent without an atom names the type (`ll (atom
  := string) classical [one; bot]`). The implicit `atom` is cleared on
  the types `formula`, `proof` and `state`, so they are written applied.
- **The checker runs the Rust checker's algorithm over formulas, not
  occurrences.** Two occurrences of one formula are interchangeable in a
  multiset, so `Ax a` stands for `[covar a; var a]`, `Copy A` needs no `?`
  above it (the root requires an empty unrestricted zone), and `Quest A`
  removes every `A` from the unrestricted zone (the proof contracts the
  copies, or weakens when there is none). Everything else follows
  `core/src/proofs/oracle.rs` rule by rule: `take` with the absorbing
  flag, the four cases of `&` in `join_with` (the union of two absorbing
  zones is `gl ++ diff gr gl`), promotion needing an empty linear zone and
  resetting the flag, `Weaken` of a `?` formula in every calculus, `Cut A
  l r` taking `A` from the left premise and `dual A` from the right one
  and joining them as `Tensor` does, refused without `cut R` as `Mix` is
  without `mix R`. The
  Rust `Fault::Surplus` has no counterpart: zones are lists, and a zone
  too large fails at the root.
- **The two-sided statement has a term of its own**, not the one-sided
  term under a one-succedent condition: a one-sided formula built from
  `⊤` and `0` alone does not say which side of `⊢` it stands on (`top` is
  `⊤` on the right and `0` on the left, so `⊢ ⊤, ⊤` is `0 ⊢ ⊤` or `⊤ ⊢ 0`
  read with one goal), the one-sided `Top` names no context, and a
  formula-level checker cannot count goals without the sides; the Rust
  checker has them from the occurrences, which the Rocq term does not
  name. So `iproof` names the rule with its side, the principal formula's
  immediate subformulas as intuitionistic formulas, and the context of
  `ITopR` and of `IZeroL` (and the goal of `IZeroL`); `iderive` computes
  every node's sequent exactly, bottom-up, and a sequent has its one
  conclusion by its type. `bridges/NanoIllBridge.v` proves that `ill
  intuitionistic` derives exactly what `nanoill.v` derives; the review
  proved, in a probe kept outside the repository, that every derivation
  of `ill` has a term `icheck` accepts.
- **Cut is an optional rule in both calculi** (`cut`, `icut`), off in
  every named calculus (`classical`, `intuitionistic`, `affine`), so the
  cut-free statements and the bridges keep their meaning; a certificate
  of a proof with a cut states a record literal with `cut := true`,
  proved by the general `soundness`, or `icut := true` with
  `soundness_ill`. `ICut A l r` names the cut formula as the premise
  that proves it has it, and either premise may be that one: the
  exporter writes the premises in the derivation's order, where the
  occurrence of the cut formula's tree is a hypothesis when the cut is
  on an input subformula. `icut_conclusion` tries the first premise as
  the one that proves `A`, then the second; where both apply, both
  goals are `A` and the two conclusions are the same multiset.
- **The first-order development** stands beside the propositional one
  and changes none of its trusted files; what both checkers share is
  written once (`Multiset`, `TwoSided`, `FirstOrderFacts`, below). `Terms.v` (`term`: `bound n` a de
  Bruijn index, `eigen a` an eigenvariable named by a natural, `tapp f
  ts`; `tsubst`, `toccurs`, `tclosed`), `FirstOrderFormulas.v` (`var p
  ts`, `covar p ts`, the connectives under the propositional names,
  `fall`, `fex`; `dual`, `subst k u`, `occurs`), `FirstOrderCalculus.v`
  (`fresh a l`; `ll R` over `Calculus.rules`, `fall_r` with `fresh a
  (fall A :: l)` and `fex_r` with `tclosed t`), `FirstOrderProofs.v`
  (`proof`, `Ax p ts`, … `Cut`, `Forall A a`, `Exists A t`, the body
  `A` with its bound variable `0`), `TermsCheck.v` (`term_eqb`,
  `terms_eqb`, `term_ind'`, `teigens` and their lemmas),
  `FirstOrderCheck.v` (`formula_eqb`, `feigens`, the instances of
  `Multiset` on first-order formulas, `state` with `eigens`, `introduced`,
  `derive`, `check`), `FirstOrderSoundness.v` (`fresh_*` lemmas, `sat`
  with a context fresh for the subterm's eigenvariables, `good`,
  `derive_sound`, the four theorems), `FirstOrderIntuitionistic.v`
  (`iformula` with `iall`, `iex`; `isubst`, `ioccurs`, `ifresh`; `ill R`
  over `Intuitionistic.irules` with `all_irr`, `all_ilr`, `ex_irr`,
  `ex_ilr`) and `FirstOrderIntuitionisticCheck.v` (`iproof` with
  `IAllR`, `IExL`, `IExR`, `IAllL` after `ICut`, `iintroduced`, `iderive`
  returning `(Γ, C, eigens)`, `icheck`, `igood`, `soundness_ill`).
- **The first-order files share names with the propositional ones**
  (`formula`, `ll`, `proof`, `check`, `soundness_classical`, …) and
  `Require` `Calculus` and `Intuitionistic` without importing them, so a
  certificate imports one development (`FirstOrderSoundness` or
  `FirstOrderIntuitionisticCheck`) and writes the optional rules by
  module: `Calculus.classical`, `{| Calculus.mix := …; Calculus.weakening
  := …; Calculus.cut := … |}`, `Intuitionistic.affine`, `{|
  Intuitionistic.iweakening := …; Intuitionistic.icut := true |}`, with
  `(symbol := string)` where the propositional ones write `(atom :=
  string)`. File names must stay distinct from the propositional ones:
  `From Deduxit.Linear Require Formulas` would be ambiguous with a
  `Deduxit.Linear.FirstOrder.Formulas`. The proof constructor `Forall` shadows
  `List.Forall` in these files: write `List.Forall`.
- **The first-order checker mirrors deduxit's two passes over explicit
  formulas.** Every formula a node names is an instance with its frame's
  terms substituted (the exporter substitutes them), so no frame is
  computed: pass 1 (`introduced`) collects the eigenvariables the `∀`
  steps introduce and fails where one is introduced again *above its own
  step*, which is deduxit's `Reintroduced` as the unfolded tree can see it
  (copies of a shared node are never on one path; two steps with one
  eigenvariable in disjoint branches are accepted, sound by the
  calculus); pass 2 (`derive`) carries `eigens` to the root: an `∃`
  step adds its witness's (`teigens`), a cut its formula's (`feigens`,
  deduxit's "a cut on an instance adds its frame's"), a `∀` step removes
  its own; at the root no introduced eigenvariable may be in the set or
  in the sequent, and one no step introduces is a constant (the
  author's decision of 2026-10-30: `∀x.p(x) ⊢ ∃y.p(y)` is provable). The
  two-sided checker does the same, `∀R` and `∃L` introducing.
- **Why it is sound** (`good i s`, handed from the root to the
  leaves inside the bottom-up induction): no eigenvariable `i` holds
  (those the subterm introduces) is in the subterm's `eigens` or occurs
  in its conclusion `gamma ++ map wn theta`; `sat` quantifies only over
  absorbed contexts `Δ` fresh for `i`. The root's check gives `good`;
  each rule passes it to its premises because a premise's formula is a
  conclusion's, a subformula of one, an instance at a witness whose
  eigenvariables `eigens` holds, or the body at the step's own
  eigenvariable, which pass 1 keeps out of the premise's `i`; and a `&`
  hands its premises only formulas of its conclusion as absorbed context.
  At a `∀` step `good` is the rule's side condition, the absorbed `⊤`
  context included. `take_sat` needs the taken formula fresh where a `⊤`
  absorbs it.
- **Witnesses are closed terms** (`tclosed`, in the calculus and checked
  by `derive`), so `subst` never shifts and nothing is captured; it
  raises `k` under a binder and leaves other indices alone, right for
  locally closed formulas. On a formula with loose indices `ll` derives
  some open sequents the de Bruijn reading would not (the review's note:
  `⊢ ∃x.p(#1)⊥, p(#1)`); replacing every loose index by an unused
  eigenvariable maps any derivation to a locally closed one, so the
  closed sequents derivable are the textbook's, and deduxit never writes
  a loose index.
- **Proof-writing pitfalls met here**: `apply iff` in a hypothesis may
  take the iff backwards when both sides match (`fresh_wn_iff` looped in
  `repeat`), so the tactics use `proj1`/`proj2`; `cbn` on a goal
  `sat … (A :: g)` unfolds `++` into a raw `fix`, so the `∀` case
  `change`s its goal before applying `fall_r`; after `eapply ex_r` the
  premise's list is an evar, so give `sat` its `Δ` explicitly.
- **`sat θ Γ any`** is the invariant of the proof: `forall Δ, (any = false
  -> Δ = []) -> ll R (Γ ++ map wn θ ++ Δ)`, with `Γ` first so that a
  premise is `A :: rest` after `cbn` and a rule applies without exchange;
  `take_sat` carries a prefix for a second `take`. `soundness` holds for
  every `rules` value, so Mix and affine soundness are instances, and a
  calculus with cut takes `soundness` itself.
- **Every proof ends in `Qed`**; no `Admitted`, `admit`, `Axiom`,
  `Parameter` or `Conjecture` anywhere in the repository. The check greps for
  them and requires `Print Assumptions` of every theorem
  (`tests/Assumptions.v`, and `bridges/Assumptions.v` in `rocq-bridges`)
  to answer `Closed under the global context`, the
  only output it accepts, once per `Print Assumptions` line (the check
  counts them).
- **Certificates** (`tests/Certificates.v`, `tests/Modes.v`,
  `tests/TwoSided.v`, `tests/Cuts.v`, `tests/FirstOrder.v` and
  `tests/FirstOrderTwoSided.v` by hand, the last two with lemmas
  `check … = false` for a wrong witness, an eigenvariable escaping its
  step, one introduced again above its step, one the sequent names and
  an open witness, `tests/FromCommand.v` from the command's
  proofs; the exporter's own in deduxit's `core/tests/snapshots/deduxit/`,
  the first-order ones `first_order_*.v`; deduxit's flake check also writes
  first-order certificates with the command, one from a session's open
  witness, and requires a certificate with a wrong witness planted by
  `sed` to be refused): `apply
  (soundness_classical String.eqb String.eqb_spec term). vm_compute.
  reflexivity.`, `soundness_mix`/`soundness_affine` with the calculus
  as a record literal in the lemma, `soundness_ill … intuitionistic
  term` for the two-sided. Rocq prints nothing for one it accepts, and
  lemmas `check … = false` and `icheck … = false` pin what is rejected. The
  term of a proof with shared subproofs is the unfolded tree.
  `vm_compute` leaves a cast the kernel checks with its virtual machine,
  so the VM stands beside the kernel in what a certificate trusts;
  `reflexivity` alone avoids that at a cost in time. A certificate of an
  intuitionistic proof states classical derivability of its one-sided
  translation; the exporter writes the two-sided statement for a
  two-sided derivation instead.
- **`Refutations.v`** (in the package, importing `Calculus` and
  `Intuitionistic`): the three invariants every derivation keeps and the
  theorems `~ ll R Γ` they give, each from a Boolean test that
  `vm_compute` decides. `eval v` is the classical reading (`!`/`?`
  erased) and `ll_tautology` holds for every `R`, cut included, so
  `falsifies v Γ = true` refutes in every calculus
  (`classical_refutation`); `excess atom_eqb a` is the hull interval of
  the atom's excess, `None` under `⊤` and under an exponential that
  contains the atom (`bang` keeps `(0, 0)` alone), `balance` needs
  `weakening R = false` and `cut R = false` and holds with Mix, and
  `unbalanced` tests all three (`unbalanced_refutation`); `weights` sums
  `#⊗ − #⅋ − #1 + #⊥` and `count_equation` needs `weakening R = false`,
  `cut R = false` and `forallb mll Γ`, with `≥` under Mix
  (`fails_equation`, `equation_refutation`). The invariant of `balance` holds whatever
  `atom_eqb` is, since both literals of an axiom compare alike; the
  certificates pass `String.eqb`. These are the conditions under which
  the Rust search states its refutations and `Disproof::check` accepts
  them, so a certificate exists exactly for a refutation of those three
  kinds that check accepts; a saturated set, which the check accepts
  too, has no theorem here (`Unsupported::Saturated`). `ill_ll` embeds the two-sided calculus in `ll (lrules R)`, which keeps
  `iweakening` and `icut`
  (`one_sided G C` is `itr C :: map (dual ∘ itr) G`, `⊸` as `A⊥ ⅋ B`),
  which gives `ill_tautology` and the two-sided forms
  `iclassical_refutation`, `iunbalanced_refutation`,
  `iequation_refutation`. `excesses` and `weights` are fixpoints, not
  `fold_right`s, so that `cbn` refolds them; the proofs unfold only
  `excesses`, `excess`, `weights` and the like (`cbn [...]`), since a
  full `cbn` turns `add (Some (0, 0)) x` and `1 + x` into matches no
  lemma rewrites. Certificates of non-derivability are in
  `tests/Refutations.v`, `tests/Weights.v`, `tests/FirstOrderWeights.v` and, from the exporter, in
  `core/tests/snapshots/deduxit/`; the OneSided count (copies of one
  sign) and the state equation are `Weights.v`'s (below).
- **`Weights.v`** (in the package, exporting `Refutations`): what a
  formula can contribute to a weighted count (`out`, an inductive
  relation; `outcome` is `num z`, `dead` or `absorb`), with `otimes`
  for `⊗` (dead wins: the sides are proved apart, so one side's `⊤`
  cannot absorb the other's `0`) and `opar` for `⅋` and for formulas
  side by side (absorb wins). `?A` contributes the sum of any number of
  `A`'s contributions, `!A` zero (a promotion's context is all `?`,
  each taking none). A dead atom's literal of the sign `p` names is
  `dead`, its other literal `absorb`, so its axiom still settles; `p`
  must be a Horn program's bodies' sign, or a clause that never fires
  has an absorbing body literal and the test refuses (the review's
  witness, `tests/Weights.v`'s `negative_bodies_wrong_sign`); `p` is a
  parameter of every theorem of the file, and with weakening it also
  names the outputs' sign, which for a Horn program is the same; that makes the
  invariant hold for every weight function `y` and dead set `d`, and
  dead atoms are how a Horn program's transitions that can never fire
  drop out: their bodies hold a dead literal, so their copies contribute
  only zero. `weighted_balance`: without weakening and cut, Mix allowed,
  every derivable sequent can contribute `num 0` or `absorb`; `least`
  and `absorbs` bound every contribution (`out_bound`), so `overweight`
  (no formula may absorb, the bound of the sequent above zero, or no
  numeric contribution at all) refutes (`weighted_refutation`,
  `iweighted_refutation`). The one-sided count is the weight `1` (or
  `-1` for copies of the negative literal) on one atom and no dead atom;
  the state equation is the Farkas weights of the atoms (the ticket
  weights of clauses used once are not needed: the test sums those
  clauses' own literals, which the ticket inequality bounds) and the
  atoms outside the closure of the initial marking declared dead. Every
  refutation the Rust test states passes `overweight`: its lower bound
  is at least the Rust interval's (`0` gives `never`, at least any
  number; an exponential's row is `0` either way).
- **With weakening the count needs outputs** (`affine_balance`): a
  weakening may drop any formula, so the test keeps only formulas with
  no output droppable (`droppable`, contributing zero), where `outputs`
  counts one for a literal of the output sign `p`, `1`, `⊤` and `!A`,
  none for the other literals, `⊥`, `0`, `?A`, `⊗` one fewer than its
  sides, `⅋` the sum, additives the larger. `shaped` asks every
  subformula's count to be at least zero and every `?A` to have `A`
  with none: then every derivable sequent has at least one output, and
  one with exactly one (a Horn program's goal; `overweight_affine` asks
  `outputs_all = 1`) settles with drops of formulas without an output
  only. Mix makes two outputs, so it needs no case. A Horn program with
  bodies written negative takes `p := false`.
- **`FirstOrderWeights.v`** (in the package; it imports the outcomes and
  bounds of `Weights` by name, `Import Weights(outcome(..), …)`, since
  the first-order files share the propositional names): the same
  without weakening and without dead atoms, `value p ts` the weight of
  a literal (`table p ts` for a predicate `fixed p`, `weight p` for the
  others), `pinned` asking every literal of a fixed predicate closed so
  that no instance changes it (`subst_pinned`); `out (fall A)` is any
  instance's contribution, and `out_exists` goes by `size`, which
  substitution keeps. deduxit's counts group an atom with its predicate
  where some atom of the predicate has a bound variable and count it
  alone otherwise: the first is `weight`, the second `fixed` with the
  table. `ill_ll` here embeds the first-order two-sided calculus
  (`Refutations.lrules`), whose quantifier cases need `itr_isubst`,
  `dual_subst` and `fresh_one_sided`.
- **Balance and the count equation are cut-free.** A cut formula is no
  subformula of the conclusion, so neither invariant of the premises
  gives the conclusion's (an exponential cut formula has no interval, a
  non-multiplicative one fails `mll`); with cut the theorems need cut
  elimination, which the library does not prove. The tests compute
  `negb (cut R)`, so a refutation's statement is unchanged and holds of
  the calculi without cut, the ones the search refutes in.
- **`Mix.v`** (in the package, importing `Calculus` alone): `mix_to_ll`,
  for every `rules` value, gives `⊢ ?(⊥⊗⊥), Γ` in the calculus with
  `mix := false` and the same `weakening` and `cut` from `⊢ Γ` in the
  calculus (a cut contracts its premises' copies as `⊗` does),
  and `mix_to_classical` is its instance from Mix to `classical`. The
  statements write `wn (tens bot bot)` and the record literal rather
  than definitions of this file, so a reader checks them against
  `Calculus.v` alone. The proof carries `?(⊥⊗⊥)` up the derivation,
  turns a Mix into the `⊗` of the two premises under `⊥` and a
  dereliction, and contracts the copies of two-premise rules. Only this
  direction is proved: the converse needs cut in Yalla
  (`ll_to_mix2_cut`); with `cut := true` it is a cut against
  `⊢ !(1 ⅋ 1)`, which Mix derives, and is proved here neither with cut
  nor cut-free.
- **The bridges** (`bridges/NanoYallaBridge.v`, `bridges/NanoIllBridge.v`,
  `bridges/Assumptions.v`) import the upstream files by their logical
  paths, `From NanoYalla Require nanoll.` and `From Yalla.MicroYalla
  Require nanoill.` (the paths of their own projects), and qualify every
  name, since both define `map` and formulas. Each states, with atoms as
  `nat` (the upstream `Atom`/`IAtom`), `ll classical l <-> inhabited
  (nanoll.ll (map to_nanoyalla l))` and `ill intuitionistic G C <->
  inhabited (nanoill.ill (map to_nanoill G) (to_nanoill C))`, and the
  same over the upstream sequents with `of_…`; the translations map each
  constructor to its namesake and are proved inverse. Neither upstream
  kernel has cut, so the bridges state the named calculi, which have
  none; relating a calculus with cut would need cut elimination. The
  `cut_r` and `cut_ir` cases of `to_nanoll` and `to_nanoill_ill` are
  discharged as `mix_r`'s are, `cut classical` computing to `false`. They are part of
  what a reader checks, by reading: an equivalence would still hold for
  a translation that swaps `var` and `covar` everywhere, or the
  arguments of `aplus`, so it does not pin the translation down. The upstream files
  are LGPL: never copy them into the repository; to compile a bridge by
  hand, copy `nanoll.v` and `nanoill.v` from the inputs' store paths into
  a scratch directory and pass `-R nanoyalla NanoYalla -R microyalla
  Yalla.MicroYalla -Q bridges Deduxit.Linear.Bridges` as the check
  does. A bridge
  to another calculus (the Mix or affine ones) has no upstream kernel to
  state it against in either file.
- **`ll` is in `Prop`** ("a derivation exists"), as a textbook reads it,
  and `Permutation` is `Prop` too, while NanoYalla's and Yalla's kernels
  are in `Type`. A bridge therefore states `ll classical l <-> inhabited
  (NanoYalla.ll (map tr l))`, or proves a `Type`-valued soundness from
  `check … = true` directly (the term is data and every case analysis is
  on a Boolean or an option), never a `match` on `ll` into `Type`, which
  Rocq refuses. The bridges state the `inhabited` form.
- **Names.** `Soundness` exports `Check` and `Calculus`, so a certificate
  that imports it sees `take`, `diff`, `remove_one`, `derive`, `check`
  and the rules' constructors unqualified; a development that mixes
  libraries can `Require` without `Import` and qualify. The `let*`
  notation is `Multiset.Bind`'s, which every checker imports and none
  exports, so that it clashes with no other library's notation.
- **What the checkers share is written once**, and each file keeps its
  names as instances, with the statements they had. `Linear/Multiset.v`
  has the multiset operations over any type with a Boolean equality
  (`remove_one`, `remove_all`, `take_all`, `diff`, `take`, `same`) and
  their permutation lemmas; `Check.remove_one` is `Multiset.remove_one`
  on formulas, `IntuitionisticCheck.pick` is it on two-sided formulas,
  and `Soundness.remove_one_perm` is `Multiset.remove_one_perm`
  applied. `Linear/TwoSided.v` has the cut's conclusion (`cut_by`,
  `icut_conclusion`), its lemmas over any two-sided relation with
  exchange and cut, and the tactics of the two-sided soundness proofs
  (`equalities`, `steps`, `iperm`, each taking the equality or the
  decision as an argument; a notation cannot be passed, so the term is
  written out). `Linear/FirstOrderFacts.v` has facts of the trusted
  `FirstOrderFormulas.v` (`dual_dual`, `dual_subst`, `occurs_dual`), and
  `TermsCheck.tsubst_closed` the one of terms; `Base/Lists.v`
  (`Deduxit.Base.Lists`) has `mem` and the facts of `forallb` and
  `existsb` that the countermodel checkers of two namespaces and the
  refutations share (`kmem`, `among`, `existsb_false_in`, … are its
  instances). The soundness proofs set `Local Arguments … : simpl never`
  on the instances (`Soundness.v`, `FirstOrderSoundness.v`, the two-sided
  files): without it `cbn` unfolded `diff` to `Multiset.diff` and
  `perm`'s `rewrite diff_count` failed. The flag is local, so a user's
  `cbn` still computes `check` on a closed term (a global flag stopped
  it, the panel's witness of 87r2; `simpl nomatch` does not help, since
  the unfolding exposes a stuck fixpoint, not a match). Kept apart
  on purpose: `unoc` (sharing it needs a function for `!`, which costs
  what it saves), the weighted counts' `outs` (an inductive per file:
  one shared inductive renames its constructors), the propositional and
  first-order `wk_list` and `wn_contract` (they name `ll` and `wn`),
  and the term evaluations of the Kripke models and the finite
  structures (`teval`, `value`: a shared form needs a design), and the
  reflection proofs of the four formula equalities (`formula_eqb_spec`
  and its kin: one is in the trusted `Formulas.v`, which would then
  require a module of tactics, and the first-order ones add the terms'
  case). The tactics `perm` (`Multiset.perm`, given the decision and the
  instance of `diff_count`) and `premise` (`TwoSided.premise`, given the
  calculus, its exchange and the tactic that decides the permutation, as
  `ltac:(iperm)`) are shared.
- **Conventions.** The 9.1 reference manual (the Rocq nixpkgs ships) names
  the project file `_CoqProject` and the generated makefile `CoqMakefile`;
  the 9.3 manual names `_RocqProject` and `RocqMakefile`, which this
  library uses, both being passed by `-f` and `-o`. `From Stdlib Require`
  throughout. The licence header is two `(* … *)` lines; the conventions
  check covers `.v` files; `implicits` (of `Arguments … : clear
  implicits`) is a word of `typos.toml`.
- **`Deduxit.Intuitionistic`** (ordinary intuitionistic and minimal
  logic, `theories/Intuitionistic/`) shares nothing with
  `Deduxit.Linear` but its terms, and the lists of `Deduxit.Base`:
  `Formulas.v` (`var`, `bot`, `wedge`, `vee`, `imp`;
  `top`, `neg`, `equiv` defined, as Troelstra and Schwichtenberg do, so
  a deduxit sequent with `⊤`, `¬` or `↔` is written through them) and
  `Calculus.v` (`rules` with `explosion` and `cut`, `intuitionistic`
  and `minimal`, `lj R Γ C`) are its trusted base; `Kripke.v` and
  `KripkeCheck.v` appear in proofs only. The constructors avoid
  `conj`, `and`, `or` and `iff`, which a user importing the calculus
  would otherwise lose from the standard library. Its file names repeat
  `Deduxit.Linear`'s (`Formulas`, `Calculus`) without ambiguity, since
  every `Require` names its namespace with `From`.
- **`lj` is G1i with shared contexts**: the axiom on any formula,
  weakening and contraction, every two-premise rule sharing its context,
  one conclusion always (an empty succedent is `⊥`, so G1i's weakening
  on the right is `bot_l`, present only under `explosion`; LM is G1m).
  It is the larger calculus on purpose: a Kripke refutation of `lj`
  covers every smaller presentation (G3i, split contexts, cut-free).
  `cut_r` is optional as in the linear calculi, and Kripke soundness
  holds with it, so `kripke_refutation` is stated for every `rules`.
- **Kripke models** (`Kripke.v`): a section over any `world` type, a
  `Prop` preorder `le`, a valuation `val` and the worlds `absurd` that
  force `⊥`; `model R` asks both monotone and `absurd` empty under
  `explosion` (no exploding worlds). `forces` is the textbook
  recursion, `imp` over every later world. `classical_refutation` is
  the instance over `unit` with `eval`, `⊥` false.
- **Finite models and the checker** (`KripkeCheck.v`): worlds are
  `0 … length later - 1`; `ups w` is `w :: nth w later []`, so
  reflexivity is free and the order need not list its reflexive pairs;
  `well_formed` checks transitivity, that every later world is below
  `size`, and monotone `atoms` and `absurd`, and `absurd = []` under
  `explosion`. Read over `nat`, a number past the worlds is later only
  than itself (`ups_past`), which keeps `model` total without a subset
  type. `forced A` is the vector of worlds forcing `A`, computed bottom
  up (`O(|A|·n²)` steps with `nth`), so a certificate's cost does not
  grow with the implications' nesting as a per-world recursion would.
  The theorem needs `reflect` of the atom equality for the valuation's
  monotonicity; the certificates pass `String.eqb_spec`.
- **Its certificates**: `~ lj intuitionistic [Γ] C` (or `minimal`, or a
  record literal), proved by `apply (kripke_refutation String.eqb
  String.eqb_spec R {| later := …; atoms := …; absurd := … |} W).
  vm_compute. reflexivity.`; a sequent with no atom writes `(atom :=
  string)`. Tests in `tests/Intuitionistic/` compile as
  `Deduxit.Intuitionistic.Tests` (the check's second loop), with lemmas
  `refutes … = false` for each condition `well_formed` and `refutes`
  check.
- **First-order `Deduxit.Intuitionistic`** (`FirstOrderFormulas.v`,
  `FirstOrderCalculus.v` trusted; `FirstOrderKripke.v`,
  `FirstOrderClassical.v`, `FirstOrderCheck.v` in proofs only) takes its
  terms from `Deduxit.Linear.Terms` and `term_ind'` from `TermsCheck`,
  the one place the namespace leans on another: both are
  symbol-generic, and a copy would give deduxit's two first-order
  developments two term types. The formulas reuse the propositional
  names (`formula`, `var`, `lj`), so a certificate imports
  `FirstOrderCheck` and writes the rules as `Calculus.intuitionistic`
  or `Calculus.minimal` (`Calculus` is required, not imported).
- **`lj` and `lk` are the large calculi**: G1i and G1c with shared
  contexts, `∀L` and `∃R` replacing their principal (G3's forms are a
  contraction away) with any `tclosed` witness, eigenvariables included,
  and `∀R`, `∃L` with an eigenvariable fresh for the whole conclusion.
  `lk c` has `⊥L` always and cut when `c = true`; it has no `rules`
  record, since ex falso is no option there.
- **Kripke models with growing domains** (`FirstOrderKripke.v`, a
  section over any `world` and `element` type): `dom w` the domain, `fn
  w` and `pred w` per world, `d0` an element of every domain (the value
  of a bound variable past `ρ`, which keeps `teval` total and makes
  every domain inhabited). `model_closed` and `model_agree` ask the
  functions to stay in the domain and to keep the earlier world's
  values on its elements; persistence of terms (`teval_persist`) rests
  on both. Forcing takes `η` (eigenvariables) and `ρ` (bound variables,
  innermost first); `subst` does not shift the indices above `k`, so
  `forces_subst` holds for every `A` with `length ρ = k`, a bound
  variable past `k` being `d0` on both sides, and asks the term's value
  `e` at every later world (a function's value is the world's). The
  soundness theorem quantifies over `η` into the world's domain;
  `kripke_countermodel` takes `η := fun _ => d0`.
- **LK is sound for finite structures, computed** (`FirstOrderClassical.v`):
  truth is a `bool` with the quantifiers `forallb`/`existsb` over
  `seq 0 size`, so the induction decides each formula without excluded
  middle; `fn_closed` asks every value below `size` for every argument
  list (a finite table meets it: its entries, or `0`). No
  functional extensionality: `forallb_ext_in`, `existsb_ext_in`.
- **The finite data** (`FirstOrderCheck.v`): a table `(f, k, values)`
  by symbol and arity, `f(d₀ … dₖ₋₁)` at `index` (`d₀` most
  significant, deduxit's order), a missing table or place `0`; facts
  `(p, tuple)`. `kwell_formed` asks `sizes`, `tables` and `facts` to be
  as long as `later`, so a number past the worlds has the defaults (one
  element, no table, no fact) and the model over `nat` stays total, as
  `KripkeCheck`'s. Agreement is checked per pair of a world and a later
  one, for every table of either at the earlier world's tuples
  (`tuples`): a table only the later world has must give `0` there too.
  `kforces` recurses per world (no bottom-up vectors: the environment
  of bound variables varies), so its cost is the worlds above times the
  domain per nested `→` or `∀`. **What a certificate computes is
  `eval_fast` and `kforces_fast`** (`allb`, `anyb` and `if` in place of
  `forallb`, `existsb` and `&&`), proved equal to `eval` and `kforces`:
  under `vm_compute` the standard ones evaluate every member, and a
  model deduxit's check accepts in 30 ms (eight nested `∀` over eleven
  elements, false at the first) did not compile in 200 s. The proofs
  reason about the plain functions. Numbers are unary `nat` and a list
  literal is read recursively, so deduxit's writer refuses a model past
  4 096 elements in a domain, 8 192 entries in a list or numbers
  adding up past 2²⁰ (a table of 20 000 values of 19 999 took 7.4 GB,
  a list of 24 000 entries overflowed the stack, and Rocq warns of a
  number from 5 000 on). deduxit states its
  certificates for
  the calculi with cut (`cut := true`, `lk true`), which its own
  checker's LJ needs.
  `srefutes` needs no specification of `symbol_eqb`: nothing is
  compared but by computing.
- **The infinite chain** (`FirstOrderKripke.v`, section `Chain`): worlds
  `nat` with `le`, domain `0 … n`, a unary predicate true of `k` from
  world `k + 1`, every function `0`, no `⊥`. `chain_excluded_middle` and
  `chain_double_negation_shift` hold for every `R` and every predicate
  symbol; deduxit's manual cites them for Glivenko's failure at first
  order. Write the shift `(∀x. ¬¬p(x)) → ¬¬(∀x. p(x))`: in deduxit's
  syntax a quantifier's scope runs right, so without the brackets the
  text is another formula, classically invalid.
- **Its tests** (`tests/Intuitionistic/FirstOrder.v`): certificates in
  the writer's form (Kripke models with a growing domain, a function
  table, minimal `⊥`; structures with and without functions), the
  chain lemmas applied, and `krefutes … = false` / `srefutes … = false`
  for each condition the checks test.
- **`Deduxit.Modal`** (propositional modal logic, the systems from K
  to S5, `theories/Modal/`) shares nothing with the other namespaces
  but `Deduxit.Base.Lists`.
  A certificate states validity in Kripke models, `valid C Γ Δ` or
  `~ valid C Γ Δ`, never derivability, so its trusted base is
  `Formulas.v` (ten constructors, one per node of deduxit's modal
  arena: `var`, `top`, `bot`, `neg`, `wedge`, `vee`, `imp`, `equiv`,
  `box`, `dia`) and `Kripke.v` (`conditions`, the systems, `frame`,
  `forces`, `stable`, `valid`), with `Labelled.v` (`label := string`,
  `item` with `lab x A` and `rel x y`, `holds`, `lvalid`) for a labelled
  statement. `Calculus.v`, `Soundness.v`, `Check.v` and `Countermodel.v`
  appear in proofs only. These three trusted files hold definitions
  alone.
- **The systems are closed sets of conditions** (`Kripke.v`, `Module
  System`: `System.K`, `D`, `T`, `KB`, `KDB`, `B`, `K4`, `KD4`, `S4`,
  `K5`, `KD5`, `K45`, `KD45`, `KB5`, `S5`), the values of deduxit's
  `modal::System` constants (`core/src/modal/system.rs`, `closed`): T
  holds `serial` too, S5 all five. A generated certificate writes the
  record literal with the conditions `System::conditions()` gives, and
  the two are convertible. They are in a module so that importing the
  library does not define `K`, `T` and `B` at top level. The
  conventions check reads a `D` followed by digits in a comment as a
  plan decision's number: write the serial systems with their `K`
  there (`KD45`).
- **Forcing is stable, by hypothesis** (`stable R V`, part of `valid`
  and `lvalid`): the logic is classical and the library assumes no
  axiom, so the theorems speak of the models where `~ ~ forces w A ->
  forces w A`, as Doczkal and Smolka's models do (CPP 2012, section
  2). With excluded middle every model is one
  (`excluded_middle_stable`). The soundness proof
  shows "no placing makes the left true and the right false"
  (`g3_model`) and uses stability where a right rule must produce a
  forced formula: `wedge_r`, `imp_r`, `equiv_r`, `box_r`. Without the
  hypothesis `valid [] [vee p (neg p)]` is unprovable. Never replace it
  by an axiom or by `Classical`; a finite model meets it
  (`finite_stable`).
- **`valid` says "one of `Δ` is forced", `lvalid` "not all of `Rt`
  fail"**: at one world the disjunction of `Δ` is a formula, so
  stability gives the positive form (`lvalid_valid`,
  `forces_disjunction`); items at several worlds have no such formula,
  and stability of each does not give one of them. Under excluded
  middle the two read the same.
- **`g3` is deduxit's rule file** (`core/src/modal/calculus.rs`,
  `form`), rule for rule: a sequent is two lists of items read as sets,
  every rule asks membership (`In`) of its principal items and gives
  the premise as the conclusion with the new items consed on, the
  two-premise rules in the file's order (`imp_l`: first the premise
  with `A` on the right; `equiv_l`: first both on the left; `equiv_r`:
  first `A` left and `B` right). Both sides are lists of `item`, as
  both zones of the rule file have the sort `item`; a relational atom
  on the right is never principal. `fresh y L Rt` is the generic
  checker's condition, "`y` occurs in no member of the conclusion". A
  change of a rule there is a change of `g3`, its case of `g3_model`,
  the constructor of `proof`, the arm of `mcheck` and deduxit's
  exporter.
- **`ser` has no `x <> y`**: deduxit's checker accepted `Ser` with one
  new label for both (`w1 R w1`) up to 0.5.0, and refuses it from 0.6.0
  on, where its `fresh` asks the new name to differ from every other
  variable of the rule. `g3` keeps the wider rule, so its soundness covers
  the certificates of both. That instance does not keep validity inside one model (a
  serial frame may have no world that sees itself), so `g3_model`
  quantifies over the model inside the induction and, for this case,
  adds a world beside it that sees itself alone (`beside_R`,
  `beside_V`): the frame conditions survive (`beside_frame`), the old
  worlds force what they did (`beside_forces`), and the new world
  decides every formula, so forcing stays stable (`beside_stable`).
  A sixth frame condition must survive that addition too, or its
  systems need `x <> y` back.
- **A labelled proof holds no sequent** (`Check.v`, `proof`): `mcheck
  atom_eqb C p L Rt` starts from the sequent to prove and each
  constructor tests its principal items with `mem` (an `existsb` over
  `item_eqb`), its side conditions (`freshb`, the system's condition
  for a frame rule) and checks its premises on the lists with the new
  items consed on. `mcheck_sound` gives `g3 C L Rt`. The certificate's
  theorems are `modal_soundness atom_eqb atom_eqb_spec C x p`, with
  the root label `x` (deduxit's is `"w0"`) before the term, for
  `valid C Γ Δ` from `mcheck … (map (lab x) Γ) (map (lab x) Δ) = true`,
  and `labelled_soundness atom_eqb atom_eqb_spec C p` for `lvalid`.
  Labels are strings compared by `String.eqb`. A subterm shared by a
  `let` is checked once per use, each time against that use's sequent.
  The checker scans both lists at every node, so its cost is nodes
  times sequent length times formula size.
- **Finite modal countermodels** (`Countermodel.v`): `{| arrows := …;
  atoms := … |}`, the worlds the numbers below `length arrows`, the
  arrows the relation as written (deduxit closes nothing either, so a
  reflexive model lists its loops). The Kripke model is over `{ w |
  w < size }`, not `nat`, so that a number past the worlds is no world:
  the frame conditions are checked as written and a stray world would
  break seriality and reflexivity. Nothing compares two worlds, so no
  proof irrelevance is needed. `meets C` tests `bounded` (every arrow
  leads to a world) and each condition of `C`; `forced A` is the table
  of worlds forcing `A`, computed bottom up from its parts' tables;
  `refutes atom_eqb m C w Γ Δ` and `modal_refutation atom_eqb m C w`.
  The valuation is whatever `atom_eqb` finds in `atoms`, so the theorem
  needs no specification of `atom_eqb`.
- **Its tests** (`tests/Modal/`, compiled as `Deduxit.Modal.Tests` by
  the check's third loop): `Certificates.v` (every rule once, a
  certificate per frame rule, a labelled sequent, and `mcheck … =
  false` for a frame rule the system lacks, a label that is not new at
  `R□`, `L◇` and `Ser`, a missing edge, a missing principal formula and
  an axiom at two labels) and `Countermodels.v` (a model per system
  shape, and `refutes … = false` for each condition `meets` tests, an
  arrow or a world out of the model, and a world that forces the wrong
  side). They name their atoms by `Definition p : formula string :=
  var "p"`, never by a `Notation`: on Rocq 9.2 and 9.3 that warns, and
  a test must print nothing. `ser` is a word of `typos.toml`.
- **Where things plug in.** A new rule is a constructor of `ll`, a
  constructor of `proof`, an arm of `derive` and a case of `derive_sound`,
  nothing redone, as cut was; an optional one is also a field of `rules`
  (every record literal here and deduxit's exporter's gains it) and a
  case of every induction on `ll` (`Mix.v`, `Refutations.v`, the
  bridges). A new calculus is a `rules` value and an instance of
  `soundness`. The first-order development (above) takes a new rule
  the same way, in its own files: a constructor of its `ll` and `proof`,
  an arm of `introduced` (binary rules concatenate) and `derive` (the
  premises' `eigens` concatenated), and a case of `derive_sound` with
  its `good` obligation for each premise; the two-sided files alike. A
  new first-order calculus is a `Calculus.rules` value and an instance of
  its `soundness`.
