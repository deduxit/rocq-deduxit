(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** Certificates of non-derivability, in the form deduxit writes them:
    the lemma states that the sequent is not derivable in [ll] or
    [ill], and the proof applies a refutation theorem to an assignment
    or an atom that a test accepts by computation. The last lemmas
    check what the tests reject. *)

From Stdlib Require Import List String.
From Deduxit.Linear Require Import Refutations.
Import ListNotations.
Open Scope string_scope.

(** [⊢ A & B, A⊥] read classically is false when [A] is true and [B]
    false. *)
Lemma classical_with : ~ ll (atom := string) classical [awith (var "A") (var "B"); covar "A"].
Proof.
  apply (classical_refutation classical (fun a => existsb (String.eqb a) ["A"])).
  vm_compute. reflexivity.
Qed.

(** The classical reading refutes in every calculus, with Mix and
    weakening too. *)
Lemma classical_with_both :
  ~ ll (atom := string) {| mix := true; weakening := true; cut := false |} [wn (var "A"); bot].
Proof.
  apply (classical_refutation _ (fun a => existsb (String.eqb a) [])).
  vm_compute. reflexivity.
Qed.

(** [A ⊕ B ⊢ A]: false when [B] is true and [A] false. *)
Lemma classical_two_sided : ~ ill (atom := string) intuitionistic [iplus (ivar "A") (ivar "B")] (ivar "A").
Proof.
  apply (iclassical_refutation intuitionistic (fun a => existsb (String.eqb a) ["B"])).
  vm_compute. reflexivity.
Qed.

(** [A ⊢ A ⊗ A]: one more [A] than [A⊥]. *)
Lemma unbalanced_contraction : ~ ll (atom := string) classical [covar "A"; tens (var "A") (var "A")].
Proof.
  apply (unbalanced_refutation String.eqb "A" classical).
  vm_compute. reflexivity.
Qed.

(** With Mix, over the alternatives of a [⊕]: one or two more [A]. *)
Lemma unbalanced_hull :
  ~ ll (atom := string) {| mix := true; weakening := false; cut := false |}
    [aplus (tens (var "A") (var "A")) (tens (var "A") (tens (var "A") (var "A"))); covar "A"].
Proof.
  apply (unbalanced_refutation String.eqb "A" _).
  vm_compute. reflexivity.
Qed.

(** [A ⊢ B] two-sided. *)
Lemma unbalanced_two_sided : ~ ill (atom := string) intuitionistic [ivar "A"] (ivar "B").
Proof.
  apply (iunbalanced_refutation String.eqb "A" intuitionistic).
  vm_compute. reflexivity.
Qed.

(** [⊢ A ⅋ B, A⊥, B⊥]: three formulas where the equation asks for one. *)
Lemma equation_par : ~ ll (atom := string) classical [parr (var "A") (var "B"); covar "A"; covar "B"].
Proof.
  apply (equation_refutation classical).
  vm_compute. reflexivity.
Qed.

(** With Mix: one formula where at least three are asked for. *)
Lemma equation_mix :
  ~ ll (atom := string) {| mix := true; weakening := false; cut := false |} [tens (tens (var "A") (covar "A")) one].
Proof.
  apply (equation_refutation _).
  vm_compute. reflexivity.
Qed.

(** [A ⊸ B ⊢ A], one-sided [⊢ A, A ⊗ B⊥]: two formulas where the
    equation asks for three. *)
Lemma equation_two_sided :
  ~ ill (atom := string) intuitionistic [ilmap (ivar "A") (ivar "B")] (ivar "A").
Proof.
  apply (iequation_refutation intuitionistic).
  vm_compute. reflexivity.
Qed.

(** No assignment makes a tautology false. *)
Lemma excluded_middle_read : forall v, falsifies v [var "A"; covar "A"] = false.
Proof. intro v. unfold falsifies. cbn. destruct (v "A"); reflexivity. Qed.

(** The balance refutes nothing when the atom is balanced, when a [⊤]
    absorbs, or with weakening. *)
Lemma balanced : unbalanced String.eqb "A" classical [covar "A"; var "A"] = false.
Proof. vm_compute. reflexivity. Qed.

Lemma absorbed : unbalanced String.eqb "A" classical [var "A"; top] = false.
Proof. vm_compute. reflexivity. Qed.

Lemma weakened :
  unbalanced String.eqb "A" {| mix := false; weakening := true; cut := false |} [var "A"] = false.
Proof. vm_compute. reflexivity. Qed.

(** An axiom satisfies the equation; the test needs multiplicative
    formulas, and allows more formulas with Mix. *)
Lemma axiom_counts : fails_equation classical [covar "A"; var "A"] = false.
Proof. vm_compute. reflexivity. Qed.

Lemma additive_counts : fails_equation classical [awith (var "A") (var "A"); covar "A"; covar "A"] = false.
Proof. vm_compute. reflexivity. Qed.

Lemma mix_counts :
  fails_equation {| mix := true; weakening := false; cut := false |} [covar "A"; var "A"; covar "B"; var "B"] = false.
Proof. vm_compute. reflexivity. Qed.
