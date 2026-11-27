(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * What the two-sided checkers share

    The propositional and the first-order checker of the two-sided
    calculus ([IntuitionisticCheck], [FirstOrderIntuitionisticCheck])
    compute a cut's conclusion alike and prove their passes sound with
    the same tactics. This module has both, for any type of formulas
    with a Boolean equality; each checker names its own instances. *)

From Stdlib Require Import Bool List Permutation Lia.
From Deduxit.Linear Require Multiset.
Import ListNotations.

Section TwoSided.

Context {F : Type} (eqb : F -> F -> bool).

(** The conclusion [Γ1, Γ2 ⊢ C2] of a cut on [A] when the first premise
    [Γ1 ⊢ C1] proves [A] and the second, [Γ2 ⊢ C2], has [A] as a
    hypothesis; [None] otherwise. *)
Definition cut_by (A : F) (l1 : list F) (C1 : F) (l2 : list F) (C2 : F)
    : option (list F * F) :=
  if eqb A C1 then
    match Multiset.remove_one eqb A l2 with
    | Some l2' => Some (l1 ++ l2', C2)
    | None => None
    end
  else None.

(** The conclusion of a cut on [A] from its premises [Γ1 ⊢ C1] and
    [Γ2 ⊢ C2], whichever of them proves [A]. When both orders apply,
    [C1] and [C2] are both [A], and the two orders give the same
    sequent. *)
Definition icut_conclusion (A : F) (l1 : list F) (C1 : F) (l2 : list F) (C2 : F)
    : option (list F * F) :=
  match cut_by A l1 C1 l2 C2 with
  | Some s => Some s
  | None => cut_by A l2 C2 l1 C1
  end.

Context (eqb_spec : forall x y, reflect (x = y) (eqb x y)).

(** The formulas of a cut's premises are those of its conclusion and the
    cut formula. *)
Lemma cut_by_in : forall A l1 C1 l2 C2 l C X,
  cut_by A l1 C1 l2 C2 = Some (l, C) ->
  In X (C1 :: l1) \/ In X (C2 :: l2) -> X = A \/ In X (C :: l).
Proof.
  unfold cut_by; intros A l1 C1 l2 C2 l C X E HX.
  destruct (eqb_spec A C1) as [-> | _]; [| discriminate].
  destruct (Multiset.remove_one eqb C1 l2) as [l2' |] eqn:P; [| discriminate].
  injection E as <- <-. apply (Multiset.remove_one_perm _ eqb_spec) in P.
  destruct HX as [[-> | HX] | [-> | HX]]; [left; reflexivity | right; right; apply in_or_app; auto
    | right; left; reflexivity |].
  apply (Permutation_in _ P) in HX as [-> | HX]; [left; reflexivity |].
  right; right; apply in_or_app; auto.
Qed.

Lemma icut_conclusion_in : forall A l1 C1 l2 C2 l C X,
  icut_conclusion A l1 C1 l2 C2 = Some (l, C) ->
  In X (C1 :: l1) \/ In X (C2 :: l2) -> X = A \/ In X (C :: l).
Proof.
  unfold icut_conclusion; intros A l1 C1 l2 C2 l C X E HX.
  destruct (cut_by A l1 C1 l2 C2) as [[l' C'] |] eqn:B.
  - injection E as <- <-. exact (cut_by_in _ _ _ _ _ _ _ _ B HX).
  - apply (cut_by_in _ _ _ _ _ _ _ _ E). tauto.
Qed.

(** The cut is sound in any two-sided calculus [ill] that has exchange
    and the cut rule. *)
Context (ill : list F -> F -> Prop)
  (ex : forall l l' C, ill l C -> Permutation l l' -> ill l' C)
  (cut : forall A l1 l2 C, ill l1 A -> ill (A :: l2) C -> ill (l1 ++ l2) C).

Lemma cut_by_sound : forall A l1 C1 l2 C2 l C,
  ill l1 C1 -> ill l2 C2 -> cut_by A l1 C1 l2 C2 = Some (l, C) -> ill l C.
Proof.
  unfold cut_by; intros A l1 C1 l2 C2 l C H1 H2 E.
  destruct (eqb_spec A C1) as [-> | _]; [| discriminate].
  destruct (Multiset.remove_one eqb C1 l2) as [l2' |] eqn:P; [| discriminate].
  injection E as <- <-. apply (Multiset.remove_one_perm _ eqb_spec) in P.
  apply (cut C1); [exact H1 | exact (ex _ _ _ H2 P)].
Qed.

Lemma icut_conclusion_sound : forall A l1 C1 l2 C2 l C,
  ill l1 C1 -> ill l2 C2 -> icut_conclusion A l1 C1 l2 C2 = Some (l, C) -> ill l C.
Proof.
  unfold icut_conclusion; intros A l1 C1 l2 C2 l C H1 H2 E.
  destruct (cut_by A l1 C1 l2 C2) as [[l' C'] |] eqn:B.
  - injection E as <- <-. exact (cut_by_sound _ _ _ _ _ _ _ H1 H2 B).
  - exact (cut_by_sound _ _ _ _ _ _ _ H2 H1 E).
Qed.

End TwoSided.

(** ** The tactics of the soundness proofs *)

(** Rewrites with the Boolean equalities of formulas a node compared,
    [eqb] the equality and [eqb_spec] its reflection lemma. *)
Ltac equalities eqb eqb_spec :=
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_prop in H; destruct H
  | H : eqb ?A ?B = true |- _ => destruct (eqb_spec A B); [subst | discriminate]
  end.

(** Unfolds a node's [match]es on its subterms' conclusions and on the
    multiset operations, and keeps what each one computed. *)
Ltac steps :=
  repeat match goal with
  | H : match ?e with _ => _ end = Some _ |- _ =>
      let E := fresh "E" in destruct e eqn:E; try discriminate
  | H : (if ?b then _ else _) = Some _ |- _ =>
      let E := fresh "E" in destruct b eqn:E; try discriminate
  end.

(** Proves a premise from the derivation of a subterm, up to a
    permutation of its hypotheses: [ill] is the calculus, [ex] its
    exchange, and [tac] decides the permutation. *)
Ltac premise ill ex tac :=
  match goal with
  | H : ill ?l ?C |- ill _ ?C => apply (ex l _ C H); tac
  end.

(** Decides a permutation of lists of formulas from the permutations in
    the context, by counting every formula's occurrences, [eq_dec]
    deciding equality. *)
Ltac iperm eq_dec :=
  apply (Permutation_count_occ eq_dec); intros ?x;
  repeat match goal with
  | H : Permutation _ _ |- _ =>
      rewrite (Permutation_count_occ eq_dec) in H; specialize (H x)
  end;
  repeat first [rewrite count_occ_app in * | progress cbn [count_occ] in *];
  repeat match goal with
  | |- context [eq_dec ?a ?b] => destruct (eq_dec a b)
  | H : context [eq_dec ?a ?b] |- _ => destruct (eq_dec a b)
  end;
  lia.
