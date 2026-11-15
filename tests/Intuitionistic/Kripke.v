(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** Certificates of non-derivability in LJ and LM by Kripke models, in
    the form deduxit writes them: the lemma states that the sequent is
    not derivable, and the proof applies [kripke_refutation] to a finite
    model and a world that [refutes] accepts by computation. The last
    lemmas check what [refutes] rejects. *)

From Stdlib Require Import List String.
From Deduxit.Intuitionistic Require Import KripkeCheck.
Import ListNotations.
Open Scope string_scope.

(** Two worlds, the second later than the first and forcing [a]. *)
Definition two : finite_model string :=
  {| later := [[1]; []]; atoms := [[]; ["a"]]; absurd := [] |}.

(** [⊢ a ∨ ¬a]: the first world forces neither [a] nor [¬a]. *)
Lemma excluded_middle : ~ lj intuitionistic [] (vee (var "a") (neg (var "a"))).
Proof.
  apply (kripke_refutation String.eqb String.eqb_spec intuitionistic two 0).
  vm_compute. reflexivity.
Qed.

(** [¬¬a ⊢ a], with cut too. *)
Lemma double_negation :
  ~ lj {| explosion := true; cut := true |} [neg (neg (var "a"))] (var "a").
Proof.
  apply (kripke_refutation String.eqb String.eqb_spec _ two 0).
  vm_compute. reflexivity.
Qed.

(** Peirce's law, [⊢ ((a → b) → a) → a]. *)
Lemma peirce :
  ~ lj intuitionistic [] (imp (imp (imp (var "a") (var "b")) (var "a")) (var "a")).
Proof.
  apply (kripke_refutation String.eqb String.eqb_spec intuitionistic two 0).
  vm_compute. reflexivity.
Qed.

(** [⊢ a ↔ ¬¬a], with [⊤] beside it. *)
Lemma double_negation_equiv :
  ~ lj intuitionistic [top] (equiv (var "a") (neg (neg (var "a")))).
Proof.
  apply (kripke_refutation String.eqb String.eqb_spec intuitionistic two 0).
  vm_compute. reflexivity.
Qed.

(** [a → b ∨ c ⊢ (a → b) ∨ (a → c)]: two later worlds, one forcing [a]
    and [b], the other [a] and [c]; the order is given without its
    reflexive pairs. *)
Lemma independence :
  ~ lj intuitionistic [imp (var "a") (vee (var "b") (var "c"))]
      (vee (imp (var "a") (var "b")) (imp (var "a") (var "c"))).
Proof.
  apply (kripke_refutation String.eqb String.eqb_spec intuitionistic
           {| later := [[1; 2]; []; []]; atoms := [[]; ["a"; "b"]; ["c"; "a"]]; absurd := [] |} 0).
  vm_compute. reflexivity.
Qed.

(** [a, ¬a ⊢ b] in minimal logic: one world forcing [a] and [⊥]. *)
Definition absurd_world : finite_model string :=
  {| later := [[]]; atoms := [["a"]]; absurd := [0] |}.

Lemma minimal_explosion : ~ lj minimal [var "a"; neg (var "a")] (var "b").
Proof.
  apply (kripke_refutation String.eqb String.eqb_spec minimal absurd_world 0).
  vm_compute. reflexivity.
Qed.

(** [¬a ⊢ b] in minimal logic, by a later world that forces [a] and
    [⊥]: it forces [¬a] too. *)
Lemma minimal_later :
  ~ lj minimal [imp (var "a") bot] (var "b").
Proof.
  apply (kripke_refutation String.eqb String.eqb_spec minimal
           {| later := [[1]; []]; atoms := [[]; ["a"]]; absurd := [1] |} 0).
  vm_compute. reflexivity.
Qed.

(** The model with one world is an assignment: [a ⊢ b] is false when [a]
    is true and [b] false. *)
Lemma one_world : ~ lj intuitionistic [var "a"] (var "b").
Proof.
  apply (classical_refutation intuitionistic (fun a => String.eqb a "a")).
  vm_compute. reflexivity.
Qed.

(** A sequent with no atom names the type. *)
Lemma no_atom : ~ lj (atom := string) minimal [] bot.
Proof.
  apply (kripke_refutation String.eqb String.eqb_spec minimal
           {| later := [[]]; atoms := []; absurd := [] |} 0).
  vm_compute. reflexivity.
Qed.

(** What [refutes] rejects. *)

(** A world that forces [⊥] in LJ. *)
Lemma explosion_rejected :
  refutes String.eqb absurd_world intuitionistic 0 [var "a"; neg (var "a")] (var "b") = false.
Proof. vm_compute. reflexivity. Qed.

(** A relation that is not transitive: [0 ≤ 1 ≤ 2] without [0 ≤ 2]. *)
Lemma intransitive_rejected :
  refutes String.eqb {| later := [[1]; [2]; []]; atoms := [[]; []; ["a"]]; absurd := [] |}
    intuitionistic 0 [] (vee (var "a") (neg (var "a"))) = false.
Proof. vm_compute. reflexivity. Qed.

(** A later world that forgets an atom. *)
Lemma forgetful_rejected :
  refutes String.eqb {| later := [[1]; []]; atoms := [["a"]; []]; absurd := [] |}
    intuitionistic 1 [] (var "a") = false.
Proof. vm_compute. reflexivity. Qed.

(** A later world that forgets [⊥], in minimal logic. *)
Lemma forgetful_absurd_rejected :
  refutes String.eqb {| later := [[1]; []]; atoms := []; absurd := [0] |}
    minimal 1 [] bot = false.
Proof. vm_compute. reflexivity. Qed.

(** A later world that is no world. *)
Lemma missing_world_rejected :
  refutes String.eqb {| later := [[1]]; atoms := []; absurd := [] |}
    intuitionistic 0 [] (var "a") = false.
Proof. vm_compute. reflexivity. Qed.

(** A refuting world that is no world. *)
Lemma world_out_of_range_rejected :
  refutes String.eqb two intuitionistic 2 [] (var "a") = false.
Proof. vm_compute. reflexivity. Qed.

(** A world that forces the conclusion: the second world forces
    [a ∨ ¬a]. *)
Lemma forcing_world_rejected :
  refutes String.eqb two intuitionistic 1 [] (vee (var "a") (neg (var "a"))) = false.
Proof. vm_compute. reflexivity. Qed.

(** A world that does not force a hypothesis. *)
Lemma unforced_hypothesis_rejected :
  refutes String.eqb two intuitionistic 0 [var "a"] (var "b") = false.
Proof. vm_compute. reflexivity. Qed.
