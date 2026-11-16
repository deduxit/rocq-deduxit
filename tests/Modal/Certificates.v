(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** Certificates of valid modal sequents, written by hand: each rule of
    the labelled calculus at least once, a certificate per frame rule,
    a labelled sequent, and terms the checker must refuse. *)

From Stdlib Require Import List String.
From Deduxit.Modal Require Import Check.
Import ListNotations.
Open Scope string_scope.

Definition p : formula string := var "p".
Definition q : formula string := var "q".

(** T: [□p ⊢ p], by reflexivity. *)
Lemma box_elimination : valid System.T [box p] [p].
Proof.
  apply (modal_soundness String.eqb String.eqb_spec System.T "w0"
    (Ref "w0" (LBox "w0" "w0" p (Ax "w0" p)))).
  vm_compute. reflexivity.
Qed.

(** K: [□(p → q), □p ⊢ □q], the axiom K. The system is written as its
    record here, as a generated certificate writes it. *)
Lemma distribution :
  valid {| serial := false; reflexive := false; symmetric := false;
           transitive := false; euclidean := false |}
    [box (imp p q); box p] [box q].
Proof.
  apply (modal_soundness String.eqb String.eqb_spec System.K "w0"
    (RBox "w0" "w1" q
      (LBox "w0" "w1" (imp p q)
        (LBox "w0" "w1" p
          (LImp "w1" p q (Ax "w1" p) (Ax "w1" q)))))).
  vm_compute. reflexivity.
Qed.

(** S4: [⊢ □p → □□p], the axiom 4, by transitivity. *)
Lemma four : valid System.S4 [] [imp (box p) (box (box p))].
Proof.
  apply (modal_soundness String.eqb String.eqb_spec System.S4 "w0"
    (RImp "w0" (box p) (box (box p))
      (RBox "w0" "w1" (box p)
        (RBox "w1" "w2" p
          (Trans "w0" "w1" "w2"
            (LBox "w0" "w2" p (Ax "w2" p))))))).
  vm_compute. reflexivity.
Qed.

(** D: [□p ⊢ ◇p], by seriality. *)
Lemma consistency : valid System.D [box p] [dia p].
Proof.
  apply (modal_soundness String.eqb String.eqb_spec System.D "w0"
    (Ser "w0" "w1"
      (LBox "w0" "w1" p (RDia "w0" "w1" p (Ax "w1" p))))).
  vm_compute. reflexivity.
Qed.

(** [Ser] takes any label for the world that sees the new one, as
    deduxit's rule does: here the new label itself, in a proof that does
    not use the edge. *)
Lemma a_new_label_that_sees_itself : valid System.D [p] [p].
Proof.
  apply (modal_soundness String.eqb String.eqb_spec System.D "w0"
    (Ser "w1" "w1" (Ax "w0" p))).
  vm_compute. reflexivity.
Qed.

(** KB: [p ⊢ □◇p], the axiom B, by symmetry. *)
Lemma brouwer : valid System.KB [p] [box (dia p)].
Proof.
  apply (modal_soundness String.eqb String.eqb_spec System.KB "w0"
    (RBox "w0" "w1" (dia p)
      (Sym "w0" "w1" (RDia "w1" "w0" p (Ax "w0" p))))).
  vm_compute. reflexivity.
Qed.

(** K5: [◇p ⊢ □◇p], the axiom 5, by euclideanness. *)
Lemma five : valid System.K5 [dia p] [box (dia p)].
Proof.
  apply (modal_soundness String.eqb String.eqb_spec System.K5 "w0"
    (LDia "w0" "w1" p
      (RBox "w0" "w2" (dia p)
        (Eucl "w0" "w2" "w1" (RDia "w2" "w1" p (Ax "w1" p)))))).
  vm_compute. reflexivity.
Qed.

(** K: [¬□p ⊢ ◇¬p]. *)
Lemma duality : valid System.K [neg (box p)] [dia (neg p)].
Proof.
  apply (modal_soundness String.eqb String.eqb_spec System.K "w0"
    (LNeg "w0" (box p)
      (RBox "w0" "w1" p
        (RDia "w0" "w1" (neg p) (RNeg "w1" p (Ax "w1" p)))))).
  vm_compute. reflexivity.
Qed.

(** The logic is classical: [⊢ p ∨ ¬p]. *)
Lemma excluded_middle : valid System.K [] [vee p (neg p)].
Proof.
  apply (modal_soundness String.eqb String.eqb_spec System.K "w0"
    (ROr "w0" p (neg p) (RNeg "w0" p (Ax "w0" p)))).
  vm_compute. reflexivity.
Qed.

(** [⊢ (p ∧ q) ↔ (q ∧ p)]. *)
Lemma commutativity : valid System.K [] [equiv (wedge p q) (wedge q p)].
Proof.
  apply (modal_soundness String.eqb String.eqb_spec System.K "w0"
    (RIff "w0" (wedge p q) (wedge q p)
      (LAnd "w0" p q (RAnd "w0" q p (Ax "w0" q) (Ax "w0" p)))
      (LAnd "w0" q p (RAnd "w0" p q (Ax "w0" p) (Ax "w0" q))))).
  vm_compute. reflexivity.
Qed.

(** [p ↔ q, p ∨ q ⊢ q]. *)
Lemma equivalence : valid System.K [equiv p q; vee p q] [q].
Proof.
  apply (modal_soundness String.eqb String.eqb_spec System.K "w0"
    (LOr "w0" p q
      (LIff "w0" p q (Ax "w0" q) (Ax "w0" p))
      (Ax "w0" q))).
  vm_compute. reflexivity.
Qed.

(** [⊥ ⊢ p] and [⊢ ⊤], in a sequent that names no atom. *)
Lemma falsity : valid System.K [bot] [p].
Proof.
  apply (modal_soundness String.eqb String.eqb_spec System.K "w0" (LBot "w0")).
  vm_compute. reflexivity.
Qed.

Lemma truth : valid (atom := string) System.K [] [top].
Proof.
  apply (modal_soundness String.eqb String.eqb_spec System.K "w0" (RTop "w0")).
  vm_compute. reflexivity.
Qed.

(** A labelled sequent: [w0 : □p, w0 R w1 ⊢ w1 : p]. *)
Lemma along_an_edge :
  lvalid System.K [lab "w0" (box p); rel "w0" "w1"] [lab "w1" p].
Proof.
  apply (labelled_soundness String.eqb String.eqb_spec System.K
    (LBox "w0" "w1" p (Ax "w1" p))).
  vm_compute. reflexivity.
Qed.

(** What the checker refuses. *)

(** A frame rule the system lacks: K has no reflexivity. *)
Lemma no_reflexivity_in_K :
  mcheck String.eqb System.K
    (Ref "w0" (LBox "w0" "w0" p (Ax "w0" p)))
    [lab "w0" (box p)] [lab "w0" p] = false.
Proof. vm_compute. reflexivity. Qed.

(** [□p ⊢ □□p] in K with the label of the first [R□] used again: the
    second [w1] is not new. *)
Lemma label_not_new :
  mcheck String.eqb System.K
    (RBox "w0" "w1" (box p)
      (RBox "w1" "w1" p (LBox "w0" "w1" p (Ax "w1" p))))
    [lab "w0" (box p)] [lab "w0" (box (box p))] = false.
Proof. vm_compute. reflexivity. Qed.

(** [◇p ⊢ p] with the diamond's world taken to be the root. *)
Lemma witness_not_new :
  mcheck String.eqb System.K
    (LDia "w0" "w0" p (Ax "w0" p))
    [lab "w0" (dia p)] [lab "w0" p] = false.
Proof. vm_compute. reflexivity. Qed.

(** [□p ⊢ p] in D with the root as the world seriality gives: the label
    of [Ser] is not new. *)
Lemma serial_label_not_new :
  mcheck String.eqb System.D
    (Ser "w0" "w0" (LBox "w0" "w0" p (Ax "w0" p)))
    [lab "w0" (box p)] [lab "w0" p] = false.
Proof. vm_compute. reflexivity. Qed.

(** An edge that is not there: [□p ⊢ p] in K. *)
Lemma no_edge :
  mcheck String.eqb System.K
    (LBox "w0" "w0" p (Ax "w0" p))
    [lab "w0" (box p)] [lab "w0" p] = false.
Proof. vm_compute. reflexivity. Qed.

(** A principal formula the sequent lacks. *)
Lemma no_principal :
  mcheck String.eqb System.K
    (LAnd "w0" p q (Ax "w0" p))
    [lab "w0" p] [lab "w0" p] = false.
Proof. vm_compute. reflexivity. Qed.

(** The axiom at two labels. *)
Lemma axiom_at_two_labels :
  mcheck String.eqb System.S5
    (Ax "w0" p)
    [lab "w0" p] [lab "w1" p] = false.
Proof. vm_compute. reflexivity. Qed.
