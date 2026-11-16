(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** Certificates that a modal sequent is not valid, written by hand: a
    finite model per system, and what the test must refuse. *)

From Stdlib Require Import List String.
From Deduxit.Modal Require Import Countermodel.
Import ListNotations.
Open Scope string_scope.

Definition p : formula string := var "p".

(** K: [□p ⊢ p] fails at a world that sees none. *)
Lemma box_elimination_fails_in_K : ~ valid System.K [box p] [p].
Proof.
  apply (modal_refutation String.eqb
    {| arrows := [[]]; atoms := [[]] |} System.K 0).
  vm_compute. reflexivity.
Qed.

(** T: [⊢ □p → □□p] fails on a reflexive chain of three worlds. *)
Lemma four_fails_in_T : ~ valid System.T [] [imp (box p) (box (box p))].
Proof.
  apply (modal_refutation String.eqb
    {| arrows := [[0; 1]; [1; 2]; [2]]; atoms := [["p"]; ["p"]; []] |}
    System.T 0).
  vm_compute. reflexivity.
Qed.

(** KD45: [□p ⊢ p] fails at a world that sees only another. *)
Lemma box_elimination_fails_in_KD45 : ~ valid System.KD45 [box p] [p].
Proof.
  apply (modal_refutation String.eqb
    {| arrows := [[1]; [1]]; atoms := [[]; ["p"]] |} System.KD45 0).
  vm_compute. reflexivity.
Qed.

(** S5: [◇p ⊢ □p] fails where two worlds see each other and themselves. *)
Lemma possibility_is_not_necessity : ~ valid System.S5 [dia p] [box p].
Proof.
  apply (modal_refutation String.eqb
    {| arrows := [[0; 1]; [0; 1]]; atoms := [["p"]; []] |} System.S5 0).
  vm_compute. reflexivity.
Qed.

(** A sequent with [↔], [¬], [∧], [∨], [⊤] and [⊥]:
    [p ↔ ⊤, ¬(p ∧ ⊥) ⊢ ◇p ∨ ⊥] fails at a world that sees none. *)
Lemma every_connective :
  ~ valid System.K [equiv p top; neg (wedge p bot)] [vee (dia p) bot].
Proof.
  apply (modal_refutation String.eqb
    {| arrows := [[]]; atoms := [["p"]] |} System.K 0).
  vm_compute. reflexivity.
Qed.

(** What the test refuses. *)

(** The arrows are the relation itself: without its loops the chain is
    no model of T. *)
Lemma loops_are_listed :
  refutes String.eqb
    {| arrows := [[1]; [2]; []]; atoms := [["p"]; ["p"]; []] |}
    System.T 0 [] [imp (box p) (box (box p))] = false.
Proof. vm_compute. reflexivity. Qed.

(** A world that sees none in a serial system. *)
Lemma not_serial :
  refutes String.eqb {| arrows := [[]]; atoms := [[]] |}
    System.D 0 [box p] [p] = false.
Proof. vm_compute. reflexivity. Qed.

(** An arrow without its converse in a symmetric system. *)
Lemma not_symmetric :
  refutes String.eqb {| arrows := [[1]; []]; atoms := [["p"]; []] |}
    System.KB 0 [p] [box (dia p)] = false.
Proof. vm_compute. reflexivity. Qed.

(** Two arrows without the one they compose to in a transitive system. *)
Lemma not_transitive :
  refutes String.eqb
    {| arrows := [[1]; [2]; []]; atoms := [[]; ["p"]; []] |}
    System.K4 0 [box p] [box (box p)] = false.
Proof. vm_compute. reflexivity. Qed.

(** Two worlds seen from one that do not see each other in a euclidean
    system. *)
Lemma not_euclidean :
  refutes String.eqb
    {| arrows := [[1; 2]; []; []]; atoms := [[]; ["p"]; []] |}
    System.K5 0 [dia p] [box (dia p)] = false.
Proof. vm_compute. reflexivity. Qed.

(** An arrow to a world the model lacks. *)
Lemma arrow_out_of_the_model :
  refutes String.eqb {| arrows := [[1]]; atoms := [[]] |}
    System.K 0 [] [box p] = false.
Proof. vm_compute. reflexivity. Qed.

(** A world the model lacks. *)
Lemma world_out_of_the_model :
  refutes String.eqb {| arrows := [[]]; atoms := [[]] |}
    System.K 1 [box p] [p] = false.
Proof. vm_compute. reflexivity. Qed.

(** A world that forces a formula on the right. *)
Lemma right_forced :
  refutes String.eqb {| arrows := [[]]; atoms := [["p"]] |}
    System.K 0 [box p] [p] = false.
Proof. vm_compute. reflexivity. Qed.

(** A world that does not force a formula on the left. *)
Lemma left_not_forced :
  refutes String.eqb {| arrows := [[0]]; atoms := [[]] |}
    System.K 0 [box p] [p] = false.
Proof. vm_compute. reflexivity. Qed.
