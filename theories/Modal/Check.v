(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * Labelled proofs as terms, and their checker

    A [proof] is a derivation of the labelled calculus written as a
    term: one constructor per rule, naming the rule's labels and the
    parts of its principal formula. It holds no sequent. A premise is
    its conclusion with the rule's new items added, so [mcheck] starts
    from the sequent to prove and works upwards.

    [modal_soundness] is the theorem a certificate applies: a term that
    [mcheck] accepts for [x : Γ ⊢ x : Δ] shows [valid C Γ Δ].
    [labelled_soundness] is the same for any labelled sequent and
    [lvalid]. *)

From Stdlib Require Import List String Bool.
From Deduxit.Modal Require Export Soundness.
Import ListNotations.

Section Check.

Context {atom : Type}.
Local Notation formula := (formula atom).
Local Notation item := (item atom).

Variable atom_eqb : atom -> atom -> bool.
Hypothesis atom_eqb_spec : forall a b, reflect (a = b) (atom_eqb a b).

(** Whether two formulas are the same. *)
Fixpoint formula_eqb (A B : formula) : bool :=
  match A, B with
  | var a, var b => atom_eqb a b
  | top, top => true
  | bot, bot => true
  | neg A, neg B => formula_eqb A B
  | wedge A1 A2, wedge B1 B2 => formula_eqb A1 B1 && formula_eqb A2 B2
  | vee A1 A2, vee B1 B2 => formula_eqb A1 B1 && formula_eqb A2 B2
  | imp A1 A2, imp B1 B2 => formula_eqb A1 B1 && formula_eqb A2 B2
  | equiv A1 A2, equiv B1 B2 => formula_eqb A1 B1 && formula_eqb A2 B2
  | box A, box B => formula_eqb A B
  | dia A, dia B => formula_eqb A B
  | _, _ => false
  end.

Lemma formula_eqb_eq : forall A B, formula_eqb A B = true -> A = B.
Proof.
  induction A as [a | | | A IHA | A1 IH1 A2 IH2 | A1 IH1 A2 IH2
    | A1 IH1 A2 IH2 | A1 IH1 A2 IH2 | A IHA | A IHA];
    intros [b | | | B | B1 B2 | B1 B2 | B1 B2 | B1 B2 | B | B];
    cbn [formula_eqb]; try discriminate; intro H; try reflexivity.
  - destruct (atom_eqb_spec a b) as [-> | _]; [reflexivity | discriminate H].
  - f_equal. exact (IHA B H).
  - apply andb_true_iff in H as [H1 H2].
    f_equal; [exact (IH1 B1 H1) | exact (IH2 B2 H2)].
  - apply andb_true_iff in H as [H1 H2].
    f_equal; [exact (IH1 B1 H1) | exact (IH2 B2 H2)].
  - apply andb_true_iff in H as [H1 H2].
    f_equal; [exact (IH1 B1 H1) | exact (IH2 B2 H2)].
  - apply andb_true_iff in H as [H1 H2].
    f_equal; [exact (IH1 B1 H1) | exact (IH2 B2 H2)].
  - f_equal. exact (IHA B H).
  - f_equal. exact (IHA B H).
Qed.

(** Whether two items are the same. *)
Definition item_eqb (i j : item) : bool :=
  match i, j with
  | lab x A, lab y B => String.eqb x y && formula_eqb A B
  | rel x y, rel u v => String.eqb x u && String.eqb y v
  | _, _ => false
  end.

Lemma item_eqb_eq : forall i j, item_eqb i j = true -> i = j.
Proof.
  intros [x A | x y] [u B | u v]; cbn [item_eqb]; try discriminate;
    intro H; apply andb_true_iff in H as [H1 H2].
  - apply String.eqb_eq in H1. apply formula_eqb_eq in H2. subst. reflexivity.
  - apply String.eqb_eq in H1. apply String.eqb_eq in H2. subst. reflexivity.
Qed.

(** Whether the list [l] holds the item [i]. *)
Definition mem (i : item) (l : list item) : bool := existsb (item_eqb i) l.

Lemma mem_in : forall i l, mem i l = true -> In i l.
Proof.
  intros i l H. apply existsb_exists in H as [j [Hj E]].
  apply item_eqb_eq in E. subst. exact Hj.
Qed.

(** Whether the item [i] mentions the label [y]. *)
Definition mentionsb (y : label) (i : item) : bool :=
  match i with
  | lab x _ => String.eqb x y
  | rel x z => String.eqb x y || String.eqb z y
  end.

(** Whether no item of the sequent [L ⊢ Rt] mentions the label [y]. *)
Definition freshb (y : label) (L Rt : list item) : bool :=
  forallb (fun i => negb (mentionsb y i)) (L ++ Rt).

Lemma freshb_fresh : forall y L Rt, freshb y L Rt = true -> fresh y L Rt.
Proof.
  intros y L Rt H i Hi Hm.
  pose proof (proj1 (forallb_forall _ _) H i Hi) as Hn.
  apply negb_true_iff in Hn. destruct i as [x A | x z]; cbn in Hm, Hn.
  - subst. rewrite String.eqb_refl in Hn. discriminate.
  - apply orb_false_iff in Hn as [Hx Hz].
    destruct Hm as [-> | ->];
      [rewrite String.eqb_refl in Hx | rewrite String.eqb_refl in Hz];
      discriminate.
Qed.

(** A derivation of the labelled calculus as a term. Every constructor
    is the rule of that name, [L] for left of [⊢] and [R] for right,
    and names the label [x] of its principal formula, the formula's
    parts, and after them the proofs of the rule's premises in the
    rule's order. *)
Inductive proof : Type :=
| Ax : label -> formula -> proof
    (** [x : A] on both sides *)
| LBot : label -> proof
    (** [x : ⊥] on the left *)
| RTop : label -> proof
    (** [x : ⊤] on the right *)
| LNeg : label -> formula -> proof -> proof
| RNeg : label -> formula -> proof -> proof
| LAnd : label -> formula -> formula -> proof -> proof
| RAnd : label -> formula -> formula -> proof -> proof -> proof
| LOr : label -> formula -> formula -> proof -> proof -> proof
| ROr : label -> formula -> formula -> proof -> proof
| LImp : label -> formula -> formula -> proof -> proof -> proof
| RImp : label -> formula -> formula -> proof -> proof
| LIff : label -> formula -> formula -> proof -> proof -> proof
| RIff : label -> formula -> formula -> proof -> proof -> proof
| LBox : label -> label -> formula -> proof -> proof
    (** [x : □A] along the edge [x R y] *)
| RBox : label -> label -> formula -> proof -> proof
    (** [x : □A] with the new label [y] *)
| LDia : label -> label -> formula -> proof -> proof
    (** [x : ◇A] with the new label [y] *)
| RDia : label -> label -> formula -> proof -> proof
    (** [x : ◇A] along the edge [x R y] *)
| Ref : label -> proof -> proof
    (** adds [x R x] *)
| Ser : label -> label -> proof -> proof
    (** adds [x R y] for the new label [y] *)
| Sym : label -> label -> proof -> proof
    (** adds [y R x] from [x R y] *)
| Trans : label -> label -> label -> proof -> proof
    (** adds [x R z] from [x R y] and [y R z] *)
| Eucl : label -> label -> label -> proof -> proof.
    (** adds [y R z] from [x R y] and [x R z] *)

(** Whether [p] derives the sequent [L ⊢ Rt] in the calculus of the
    system of [C]. *)
Fixpoint mcheck (C : conditions) (p : proof) (L Rt : list item) {struct p} : bool :=
  match p with
  | Ax x A => mem (lab x A) L && mem (lab x A) Rt
  | LBot x => mem (lab x bot) L
  | RTop x => mem (lab x top) Rt
  | LNeg x A p =>
      mem (lab x (neg A)) L && mcheck C p L (lab x A :: Rt)
  | RNeg x A p =>
      mem (lab x (neg A)) Rt && mcheck C p (lab x A :: L) Rt
  | LAnd x A B p =>
      mem (lab x (wedge A B)) L && mcheck C p (lab x A :: lab x B :: L) Rt
  | RAnd x A B p q =>
      mem (lab x (wedge A B)) Rt
      && mcheck C p L (lab x A :: Rt) && mcheck C q L (lab x B :: Rt)
  | LOr x A B p q =>
      mem (lab x (vee A B)) L
      && mcheck C p (lab x A :: L) Rt && mcheck C q (lab x B :: L) Rt
  | ROr x A B p =>
      mem (lab x (vee A B)) Rt && mcheck C p L (lab x A :: lab x B :: Rt)
  | LImp x A B p q =>
      mem (lab x (imp A B)) L
      && mcheck C p L (lab x A :: Rt) && mcheck C q (lab x B :: L) Rt
  | RImp x A B p =>
      mem (lab x (imp A B)) Rt && mcheck C p (lab x A :: L) (lab x B :: Rt)
  | LIff x A B p q =>
      mem (lab x (equiv A B)) L
      && mcheck C p (lab x A :: lab x B :: L) Rt
      && mcheck C q L (lab x A :: lab x B :: Rt)
  | RIff x A B p q =>
      mem (lab x (equiv A B)) Rt
      && mcheck C p (lab x A :: L) (lab x B :: Rt)
      && mcheck C q (lab x B :: L) (lab x A :: Rt)
  | LBox x y A p =>
      mem (lab x (box A)) L && mem (rel x y) L && mcheck C p (lab y A :: L) Rt
  | RBox x y A p =>
      mem (lab x (box A)) Rt && freshb y L Rt
      && mcheck C p (rel x y :: L) (lab y A :: Rt)
  | LDia x y A p =>
      mem (lab x (dia A)) L && freshb y L Rt
      && mcheck C p (rel x y :: lab y A :: L) Rt
  | RDia x y A p =>
      mem (lab x (dia A)) Rt && mem (rel x y) L && mcheck C p L (lab y A :: Rt)
  | Ref x p =>
      reflexive C && mcheck C p (rel x x :: L) Rt
  | Ser x y p =>
      serial C && freshb y L Rt && mcheck C p (rel x y :: L) Rt
  | Sym x y p =>
      symmetric C && mem (rel x y) L && mcheck C p (rel y x :: L) Rt
  | Trans x y z p =>
      transitive C && mem (rel x y) L && mem (rel y z) L
      && mcheck C p (rel x z :: L) Rt
  | Eucl x y z p =>
      euclidean C && mem (rel x y) L && mem (rel x z) L
      && mcheck C p (rel y z :: L) Rt
  end.

(** A term the checker accepts is a derivation of the calculus. *)
Theorem mcheck_sound : forall C p L Rt, mcheck C p L Rt = true -> g3 C L Rt.
Proof.
  intros C.
  induction p as [x A | x | x | x A p IH | x A p IH | x A B p IH
    | x A B p IHp q IHq | x A B p IHp q IHq | x A B p IH
    | x A B p IHp q IHq | x A B p IH | x A B p IHp q IHq | x A B p IHp q IHq
    | x y A p IH | x y A p IH | x y A p IH | x y A p IH
    | x p IH | x y p IH | x y p IH | x y z p IH | x y z p IH];
    intros L Rt H; cbn [mcheck] in H;
    repeat match goal with
    | E : _ && _ = true |- _ => apply andb_true_iff in E; destruct E
    end;
    repeat match goal with
    | E : mem _ _ = true |- _ => apply mem_in in E
    | E : freshb _ _ _ = true |- _ => apply freshb_fresh in E
    end.
  - exact (ax C x A L Rt ltac:(assumption) ltac:(assumption)).
  - apply (bot_l C x); assumption.
  - apply (top_r C x); assumption.
  - apply (neg_l C x A); auto.
  - apply (neg_r C x A); auto.
  - apply (wedge_l C x A B); auto.
  - apply (wedge_r C x A B); auto.
  - apply (vee_l C x A B); auto.
  - apply (vee_r C x A B); auto.
  - apply (imp_l C x A B); auto.
  - apply (imp_r C x A B); auto.
  - apply (equiv_l C x A B); auto.
  - apply (equiv_r C x A B); auto.
  - apply (box_l C x y A); auto.
  - apply (box_r C x y A); auto.
  - apply (dia_l C x y A); auto.
  - apply (dia_r C x y A); auto.
  - apply (ref C) with (x := x); auto.
  - apply (ser C) with (x := x) (y := y); auto.
  - apply (sym C) with (x := x) (y := y); auto.
  - apply (trans C) with (x := x) (y := y) (z := z); auto.
  - apply (eucl C) with (x := x) (y := y) (z := z); auto.
Qed.

(** A term the checker accepts for a labelled sequent shows the sequent
    valid in the system's frames. *)
Theorem labelled_soundness : forall C p (L Rt : list item),
  mcheck C p L Rt = true -> lvalid C L Rt.
Proof.
  intros C p L Rt H. exact (g3_sound C L Rt (mcheck_sound C p L Rt H)).
Qed.

(** A term the checker accepts for [x : Γ ⊢ x : Δ] shows [Γ ⊢ Δ] valid
    in the system's frames. *)
Theorem modal_soundness : forall C x p (Γ Δ : list formula),
  mcheck C p (map (lab x) Γ) (map (lab x) Δ) = true -> valid C Γ Δ.
Proof.
  intros C x p Γ Δ H. exact (g3_valid C x Γ Δ (mcheck_sound C p _ _ H)).
Qed.

End Check.

Arguments proof atom : clear implicits.
