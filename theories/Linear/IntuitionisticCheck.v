(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * Two-sided proof terms, their checker and its soundness

    A two-sided term is the proof inside a certificate deduxit writes
    for an intuitionistic proof. It has one node per rule of the
    two-sided derivation. A node's constructor names the rule and the
    side of [⊢] its principal formula is on; its arguments are the
    immediate subformulas of that formula and the terms of its premises.
    A [⊤] on the right and a [0] on the left also name the context they
    absorb, so a node and the terms of its premises determine its
    sequent. [icheck]
    computes that sequent from the leaves to the root and compares it
    with the one stated; [soundness_ill] proves that a term it accepts
    has a derivation in [ill] behind it.

    The one-sided terms of [Proofs] cannot express this statement. A
    one-sided formula built from [⊤] and [0] alone does not say which
    side of [⊢] it is on ([top] is both [⊤] on the right and [0] on the
    left), and whether a derivation has a single conclusion depends on
    those sides. Here every formula of every sequent is an
    intuitionistic formula on a known side, and a sequent has one
    conclusion by its type. *)

From Stdlib Require Import Bool List Permutation Lia.
From Deduxit.Linear Require Export Intuitionistic.
From Deduxit.Linear Require Multiset TwoSided.
Import ListNotations Multiset.Bind.

Section Formulas.

Context {atom : Type}.

Section Equality.

(** A Boolean equality on atoms; the checker compares atoms with it. *)
Variable atom_eqb : atom -> atom -> bool.

(** Structural equality of intuitionistic formulas, comparing atoms
    with [atom_eqb]. *)
Fixpoint iformula_eqb (A B : iformula atom) : bool :=
  match A, B with
  | ivar a, ivar b => atom_eqb a b
  | ione, ione => true
  | itop, itop => true
  | izero, izero => true
  | itens A1 A2, itens B1 B2 => iformula_eqb A1 B1 && iformula_eqb A2 B2
  | ilmap A1 A2, ilmap B1 B2 => iformula_eqb A1 B1 && iformula_eqb A2 B2
  | iwith A1 A2, iwith B1 B2 => iformula_eqb A1 B1 && iformula_eqb A2 B2
  | iplus A1 A2, iplus B1 B2 => iformula_eqb A1 B1 && iformula_eqb A2 B2
  | ioc A, ioc B => iformula_eqb A B
  | _, _ => false
  end.

(** [atom_eqb] decides equality. The soundness theorem assumes this. *)
Hypothesis atom_eqb_spec : forall a b, reflect (a = b) (atom_eqb a b).

Lemma iformula_eqb_spec : forall A B, reflect (A = B) (iformula_eqb A B).
Proof.
  intros A; induction A; intros B; destruct B; cbn; try (constructor; congruence).
  all: repeat match goal with
       | |- reflect _ (atom_eqb ?a ?b) => destruct (atom_eqb_spec a b)
       | |- reflect _ (iformula_eqb ?A ?B && _) =>
           match goal with IH : forall B, reflect (A = B) _ |- _ => destruct (IH B) end
       | |- reflect _ (iformula_eqb ?A ?B) =>
           match goal with IH : forall B, reflect (A = B) _ |- _ => destruct (IH B) end
       | |- reflect _ (true && _) => cbn
       | |- reflect _ (false && _) => cbn
       end.
  all: constructor; congruence.
Qed.

(** Equality of intuitionistic formulas as a decision, used in proofs;
    the checker computes with [iformula_eqb]. *)
Definition iformula_eq_dec (A B : iformula atom) : {A = B} + {A <> B} :=
  reflect_dec _ _ (iformula_eqb_spec A B).

End Equality.

End Formulas.

Section Check.

Context {atom : Type} (atom_eqb : atom -> atom -> bool).

(** A two-sided proof term. Below, [Γ ⊢ C] is the node's conclusion,
    its hypotheses read as a multiset. *)
Inductive iproof : Type :=
| IAx (a : atom)
    (** the axiom [a ⊢ a] *)
| IOneR
    (** [⊢ 1] *)
| IOneL (premise : iproof)
    (** [Γ, 1 ⊢ C] from [Γ ⊢ C] *)
| ITensR (A B : iformula atom) (left right : iproof)
    (** [Γ, Δ ⊢ A ⊗ B] from [Γ ⊢ A] and [Δ ⊢ B] *)
| ITensL (A B : iformula atom) (premise : iproof)
    (** [Γ, A ⊗ B ⊢ C] from [Γ, A, B ⊢ C] *)
| ILmapR (A B : iformula atom) (premise : iproof)
    (** [Γ ⊢ A ⊸ B] from [Γ, A ⊢ B] *)
| ILmapL (A B : iformula atom) (left right : iproof)
    (** [Γ, Δ, A ⊸ B ⊢ C] from [Γ ⊢ A] and [Δ, B ⊢ C] *)
| ITopR (context : list (iformula atom))
    (** [Γ ⊢ ⊤], with [Γ] the context *)
| IWithR (A B : iformula atom) (left right : iproof)
    (** [Γ ⊢ A & B] from [Γ ⊢ A] and [Γ ⊢ B] *)
| IWithL1 (A B : iformula atom) (premise : iproof)
    (** [Γ, A & B ⊢ C] from [Γ, A ⊢ C] *)
| IWithL2 (A B : iformula atom) (premise : iproof)
    (** [Γ, A & B ⊢ C] from [Γ, B ⊢ C] *)
| IZeroL (context : list (iformula atom)) (goal : iformula atom)
    (** [Γ, 0 ⊢ C], with [Γ] the context and [C] the goal *)
| IPlusR1 (A B : iformula atom) (premise : iproof)
    (** [Γ ⊢ A ⊕ B] from [Γ ⊢ A] *)
| IPlusR2 (A B : iformula atom) (premise : iproof)
    (** [Γ ⊢ A ⊕ B] from [Γ ⊢ B] *)
| IPlusL (A B : iformula atom) (left right : iproof)
    (** [Γ, A ⊕ B ⊢ C] from [Γ, A ⊢ C] and [Γ, B ⊢ C] *)
| IOcR (A : iformula atom) (premise : iproof)
    (** promotion, [!Γ ⊢ !A] from [!Γ ⊢ A] *)
| IDe (A : iformula atom) (premise : iproof)
    (** dereliction, [Γ, !A ⊢ C] from [Γ, A ⊢ C] *)
| IWk (A : iformula atom) (premise : iproof)
    (** weakening of a [!] hypothesis, [Γ, !A ⊢ C] from [Γ ⊢ C] *)
| ICo (A : iformula atom) (premise : iproof)
    (** contraction, [Γ, !A ⊢ C] from [Γ, !A, !A ⊢ C] *)
| IWeaken (A : iformula atom) (premise : iproof)
    (** weakening of any hypothesis, [Γ, A ⊢ C] from [Γ ⊢ C], with
        [iweakening] *)
| ICut (A : iformula atom) (left right : iproof).
    (** [Γ, Δ ⊢ C] from [Γ ⊢ A] and [Δ, A ⊢ C], with [icut]; the
        premise that proves [A] may come first or second *)

(** ** Multisets, as lists compared through [iformula_eqb]

    The operations of [Multiset], on formulas. *)

(** Removes one occurrence of [A] from [l], or fails when there is none. *)
Definition pick (A : iformula atom) (l : list (iformula atom)) : option (list (iformula atom)) :=
  Multiset.remove_one (iformula_eqb atom_eqb) A l.

(** Whether [l1] and [l2] are the same multiset. *)
Definition same (l1 l2 : list (iformula atom)) : bool :=
  Multiset.same (iformula_eqb atom_eqb) l1 l2.

(** The formulas under the [!] of a list of [!] formulas, or [None] when
    one of them is not a [!] formula. *)
Fixpoint unoc (l : list (iformula atom)) : option (list (iformula atom)) :=
  match l with
  | [] => Some []
  | ioc A :: l' => option_map (cons A) (unoc l')
  | _ :: _ => None
  end.

(** The conclusion [Γ1, Γ2 ⊢ C2] of a cut on [A] when the first premise
    [Γ1 ⊢ C1] proves [A] and the second, [Γ2 ⊢ C2], has [A] as a
    hypothesis; [None] otherwise. *)
Definition cut_by (A : iformula atom) (l1 : list (iformula atom)) (C1 : iformula atom)
    (l2 : list (iformula atom)) (C2 : iformula atom) : option (list (iformula atom) * iformula atom) :=
  TwoSided.cut_by (iformula_eqb atom_eqb) A l1 C1 l2 C2.

(** The conclusion of a cut on [A] from its premises [Γ1 ⊢ C1] and
    [Γ2 ⊢ C2], whichever of them proves [A]. *)
Definition icut_conclusion (A : iformula atom) (l1 : list (iformula atom)) (C1 : iformula atom)
    (l2 : list (iformula atom)) (C2 : iformula atom) : option (list (iformula atom) * iformula atom) :=
  TwoSided.icut_conclusion (iformula_eqb atom_eqb) A l1 C1 l2 C2.

(** ** The pass *)

(** The conclusion [Γ ⊢ C] of a term, or [None] at the first node that
    applies its rule wrongly or uses a rule that [R] does not allow. *)
Fixpoint iderive (R : irules) (p : iproof) : option (list (iformula atom) * iformula atom) :=
  match p with
  | IAx a => Some ([ivar a], ivar a)
  | IOneR => Some ([], ione)
  | IOneL q =>
      let* (l, C) := iderive R q in
      Some (ione :: l, C)
  | ITensR A B q r =>
      let* (l1, A') := iderive R q in
      let* (l2, B') := iderive R r in
      if (iformula_eqb atom_eqb) A A' && (iformula_eqb atom_eqb) B B' then Some (l1 ++ l2, itens A B) else None
  | ITensL A B q =>
      let* (l, C) := iderive R q in
      let* l' := pick A l in
      let* l'' := pick B l' in
      Some (itens A B :: l'', C)
  | ILmapR A B q =>
      let* (l, B') := iderive R q in
      if (iformula_eqb atom_eqb) B B' then
        let* l' := pick A l in
        Some (l', ilmap A B)
      else None
  | ILmapL A B q r =>
      let* (l1, A') := iderive R q in
      let* (l2, C) := iderive R r in
      if (iformula_eqb atom_eqb) A A' then
        let* l2' := pick B l2 in
        Some (ilmap A B :: l1 ++ l2', C)
      else None
  | ITopR l => Some (l, itop)
  | IWithR A B q r =>
      let* (l1, A') := iderive R q in
      let* (l2, B') := iderive R r in
      if (iformula_eqb atom_eqb) A A' && (iformula_eqb atom_eqb) B B' && same l1 l2 then Some (l1, iwith A B) else None
  | IWithL1 A B q =>
      let* (l, C) := iderive R q in
      let* l' := pick A l in
      Some (iwith A B :: l', C)
  | IWithL2 A B q =>
      let* (l, C) := iderive R q in
      let* l' := pick B l in
      Some (iwith A B :: l', C)
  | IZeroL l C => Some (izero :: l, C)
  | IPlusR1 A B q =>
      let* (l, A') := iderive R q in
      if (iformula_eqb atom_eqb) A A' then Some (l, iplus A B) else None
  | IPlusR2 A B q =>
      let* (l, B') := iderive R q in
      if (iformula_eqb atom_eqb) B B' then Some (l, iplus A B) else None
  | IPlusL A B q r =>
      let* (l1, C1) := iderive R q in
      let* (l2, C2) := iderive R r in
      let* l1' := pick A l1 in
      let* l2' := pick B l2 in
      if (iformula_eqb atom_eqb) C1 C2 && same l1' l2' then Some (iplus A B :: l1', C1) else None
  | IOcR A q =>
      let* (l, A') := iderive R q in
      let* _ := unoc l in
      if (iformula_eqb atom_eqb) A A' then Some (l, ioc A) else None
  | IDe A q =>
      let* (l, C) := iderive R q in
      let* l' := pick A l in
      Some (ioc A :: l', C)
  | IWk A q =>
      let* (l, C) := iderive R q in
      Some (ioc A :: l, C)
  | ICo A q =>
      let* (l, C) := iderive R q in
      let* l' := pick (ioc A) l in
      let* l'' := pick (ioc A) l' in
      Some (ioc A :: l'', C)
  | IWeaken A q =>
      if iweakening R then
        let* (l, C) := iderive R q in
        Some (A :: l, C)
      else None
  | ICut A q r =>
      if icut R then
        let* (l1, C1) := iderive R q in
        let* (l2, C2) := iderive R r in
        icut_conclusion A l1 C1 l2 C2
      else None
  end.

(** Whether [p] proves [hypotheses ⊢ goal] in [R]: its conclusion has
    that goal and, as a multiset, those hypotheses. *)
Definition icheck (R : irules) (p : iproof) (hypotheses : list (iformula atom)) (goal : iformula atom)
    : bool :=
  match iderive R p with
  | Some (l, C) => (iformula_eqb atom_eqb) C goal && same l hypotheses
  | None => false
  end.

End Check.

Arguments iproof atom : clear implicits.

(* The soundness proof applies the instances' lemmas, so [cbn] leaves
   the instances folded in this file; elsewhere it computes them. *)
Local Arguments pick : simpl never.
Local Arguments same : simpl never.
Local Arguments cut_by : simpl never.
Local Arguments icut_conclusion : simpl never.

Section Soundness.

Context {atom : Type} (atom_eqb : atom -> atom -> bool)
  (atom_eqb_spec : forall a b, reflect (a = b) (atom_eqb a b)).

Lemma pick_perm : forall (A : iformula atom) l l',
  pick atom_eqb A l = Some l' -> Permutation l (A :: l').
Proof. exact (Multiset.remove_one_perm _ (iformula_eqb_spec atom_eqb atom_eqb_spec)). Qed.

Lemma same_perm : forall (l1 l2 : list (iformula atom)),
  same atom_eqb l1 l2 = true -> Permutation l1 l2.
Proof. exact (Multiset.same_perm _ (iformula_eqb_spec atom_eqb atom_eqb_spec)). Qed.

Lemma unoc_map : forall (l l' : list (iformula atom)),
  unoc l = Some l' -> l = map ioc l'.
Proof.
  intros l; induction l as [| A l IH]; cbn; intros l' H.
  - injection H as <-. reflexivity.
  - destruct A; try discriminate.
    destruct (unoc l) as [l'' |]; cbn in H; [| discriminate].
    injection H as <-. cbn. f_equal. apply IH. reflexivity.
Qed.


(** The tactics of [TwoSided], on these formulas. *)
Local Ltac equalities :=
  TwoSided.equalities (iformula_eqb atom_eqb) (iformula_eqb_spec atom_eqb atom_eqb_spec).
Local Ltac steps := TwoSided.steps.
Local Ltac iperm := TwoSided.iperm (iformula_eq_dec atom_eqb atom_eqb_spec).

Variable R : irules.

(** Proves a premise from the derivation of a subterm, up to a
    permutation of its hypotheses. *)
Local Ltac premise := TwoSided.premise (@ill atom R) (@ex_ir atom R) ltac:(iperm).

(** If a cut's premises are derivable, its conclusion is. *)
Lemma cut_by_sound : forall A l1 C1 l2 C2 l C,
  icut R = true -> ill R l1 C1 -> ill R l2 C2 ->
  cut_by atom_eqb A l1 C1 l2 C2 = Some (l, C) -> ill R l C.
Proof.
  intros A l1 C1 l2 C2 l C K.
  exact (TwoSided.cut_by_sound _ (iformula_eqb_spec atom_eqb atom_eqb_spec) (ill R) (ex_ir R) (cut_ir R K) A l1 C1 l2 C2 l C).
Qed.

Lemma icut_conclusion_sound : forall A l1 C1 l2 C2 l C,
  icut R = true -> ill R l1 C1 -> ill R l2 C2 ->
  icut_conclusion atom_eqb A l1 C1 l2 C2 = Some (l, C) -> ill R l C.
Proof.
  intros A l1 C1 l2 C2 l C K.
  exact (TwoSided.icut_conclusion_sound _ (iformula_eqb_spec atom_eqb atom_eqb_spec) (ill R) (ex_ir R) (cut_ir R K)
    A l1 C1 l2 C2 l C).
Qed.

(** Every conclusion [iderive] computes is derivable. *)
Lemma iderive_sound : forall p l C,
  iderive atom_eqb R p = Some (l, C) -> ill R l C.
Proof.
  intros p; induction p; cbn; intros l C H; steps; equalities;
    repeat match goal with
    | H : Some _ = Some _ |- _ => injection H as <- <-
    | IH : forall l C, Some (?l', ?C') = Some (l, C) -> _ |- _ =>
        specialize (IH l' C' eq_refl)
    | H : pick _ _ _ = Some _ |- _ => apply pick_perm in H
    | H : same _ _ _ = true |- _ => apply same_perm in H
    | H : unoc ?l = Some _ |- _ => apply unoc_map in H; subst l
    end.
  - apply ax_ir.
  - apply one_irr.
  - apply one_ilr; premise.
  - apply tens_irr; premise.
  - apply tens_ilr; premise.
  - apply lmap_irr; premise.
  - apply lmap_ilr; premise.
  - apply top_irr.
  - apply with_irr; premise.
  - apply with_ilr1; premise.
  - apply with_ilr2; premise.
  - apply zero_ilr.
  - apply plus_irr1; premise.
  - apply plus_irr2; premise.
  - apply plus_ilr; premise.
  - apply oc_irr; premise.
  - apply de_ilr; premise.
  - apply wk_ilr; premise.
  - apply co_ilr; premise.
  - apply weakening_ilr; [assumption | premise].
  - eapply icut_conclusion_sound; [eassumption | | | eassumption]; eassumption.
Qed.

End Soundness.

(** If the checker accepts a term for a sequent, the sequent is
    derivable in the two-sided calculus [R]: intuitionistic linear
    logic or its affine variant, with or without cut. A certificate of
    a two-sided proof applies this theorem. *)
Theorem soundness_ill {atom : Type} (atom_eqb : atom -> atom -> bool)
  (atom_eqb_spec : forall a b, reflect (a = b) (atom_eqb a b)) (R : irules) :
  forall (p : iproof atom) (hypotheses : list (iformula atom)) (goal : iformula atom),
  icheck atom_eqb R p hypotheses goal = true -> ill R hypotheses goal.
Proof.
  unfold icheck; intros p Γ C H.
  destruct (iderive atom_eqb R p) as [[l C'] |] eqn:E; [| discriminate].
  apply andb_prop in H as [HC HΓ].
  destruct (iformula_eqb_spec atom_eqb atom_eqb_spec C' C); [subst | discriminate].
  eapply ex_ir; [apply (iderive_sound atom_eqb atom_eqb_spec R _ _ _ E) |].
  apply (same_perm atom_eqb atom_eqb_spec). assumption.
Qed.
