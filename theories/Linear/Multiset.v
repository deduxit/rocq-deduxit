(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * Multisets as lists

    The checkers read a list of formulas as a multiset, compared through
    a Boolean equality. These are its operations, written once for any
    type with such an equality, and what each computes as a permutation.
    The checkers' own names ([Check.remove_one],
    [IntuitionisticCheck.pick], …) are instances of these, and their
    lemmas are these lemmas applied. *)

From Stdlib Require Import Bool List Permutation Lia.
Import ListNotations.

(** Sequencing of computations that may fail: [k] runs on the value of
    [e], and [None] is failure. A checker imports [Multiset.Bind]; the
    notation is not exported, so that it clashes with no other library's
    notation. *)
Module Bind.
Notation "'let*' x ':=' e 'in' k" :=
  (match e with Some x => k | None => None end)
  (at level 10, x pattern, e at level 100, k at level 200).
End Bind.
Import Bind.

Section Multiset.

Context {A : Type} (eqb : A -> A -> bool).

(** Removes one occurrence of [x] from [l], or fails when there is none. *)
Fixpoint remove_one (x : A) (l : list A) : option (list A) :=
  match l with
  | [] => None
  | y :: l' => if eqb x y then Some l' else option_map (cons y) (remove_one x l')
  end.

(** Removes every occurrence of [x] from [l]. *)
Definition remove_all (x : A) (l : list A) : list A :=
  filter (fun y => negb (eqb x y)) l.

(** Removes each element of [l1] from [l2]. Returns what is left of
    [l2] when [l1] is included in it as a multiset, [None] otherwise. *)
Fixpoint take_all (l1 l2 : list A) : option (list A) :=
  match l1 with
  | [] => Some l2
  | x :: l1' =>
      let* l2' := remove_one x l2 in
      take_all l1' l2'
  end.

(** [l2] less [l1]: each element of [l1] is removed from [l2] where
    [l2] has it. [l1 ++ diff l2 l1] is the multiset union of the two. *)
Fixpoint diff (l2 l1 : list A) : list A :=
  match l1 with
  | [] => l2
  | x :: l1' =>
      diff (match remove_one x l2 with Some l2' => l2' | None => l2 end) l1'
  end.

(** Consumes one copy of [x] from [l]. When [l] has none, [any] (a [⊤]
    above, in the one-sided checkers) supplies it. *)
Definition take (x : A) (l : list A) (any : bool) : option (list A) :=
  match remove_one x l with
  | Some l' => Some l'
  | None => if any then Some l else None
  end.

(** Whether [l1] and [l2] are the same multiset. *)
Fixpoint same (l1 l2 : list A) : bool :=
  match l1 with
  | [] => match l2 with [] => true | _ :: _ => false end
  | x :: l1' => match remove_one x l2 with Some l2' => same l1' l2' | None => false end
  end.

(** ** What they compute, as permutations *)

Context (eqb_spec : forall x y, reflect (x = y) (eqb x y))
  (eq_dec : forall x y : A, {x = y} + {x <> y}).

Lemma remove_one_perm : forall x l l',
  remove_one x l = Some l' -> Permutation l (x :: l').
Proof.
  intros x l; induction l as [| y l IH]; cbn; intros l' H; [discriminate |].
  destruct (eqb_spec x y) as [<- | _].
  - injection H as <-. reflexivity.
  - destruct (remove_one x l) as [l'' |] eqn:E; cbn in H; [| discriminate].
    injection H as <-. rewrite (IH l'' eq_refl). apply perm_swap.
Qed.

Lemma remove_one_absent : forall x l, remove_one x l = None -> ~ In x l.
Proof.
  intros x l; induction l as [| y l IH]; cbn; intros H HI; [exact HI |].
  destruct (eqb_spec x y) as [_ | ne]; [discriminate |].
  destruct HI as [-> | HI]; [exact (ne eq_refl) |].
  destruct (remove_one x l); [discriminate | exact (IH eq_refl HI)].
Qed.

Lemma take_all_perm : forall l1 l2 l,
  take_all l1 l2 = Some l -> Permutation l2 (l1 ++ l).
Proof.
  intros l1; induction l1 as [| x l1 IH]; cbn; intros l2 l H.
  - injection H as <-. reflexivity.
  - destruct (remove_one x l2) as [l2' |] eqn:E; [| discriminate].
    rewrite (remove_one_perm _ _ _ E). apply perm_skip, IH, H.
Qed.

Lemma remove_all_perm : forall x l,
  Permutation l (repeat x ((count_occ eq_dec) l x) ++ remove_all x l).
Proof.
  intros x l; unfold remove_all. induction l as [| y l IH]; cbn; [reflexivity |].
  destruct (eq_dec y x) as [e | ne]; destruct (eqb_spec x y) as [e' | ne'];
    try congruence; cbn.
  - subst. apply perm_skip, IH.
  - apply (Permutation_trans (perm_skip y IH)), Permutation_middle.
Qed.

Lemma diff_count : forall l1 l2 y, (count_occ eq_dec) (diff l2 l1) y = (count_occ eq_dec) l2 y - (count_occ eq_dec) l1 y.
Proof.
  intros l1; induction l1 as [| x l1 IH]; cbn; intros l2 y; [lia |].
  destruct (remove_one x l2) as [l2' |] eqn:E; rewrite IH.
  - apply remove_one_perm in E.
    rewrite (Permutation_count_occ eq_dec) in E. rewrite (E y). cbn.
    destruct (eq_dec x y); lia.
  - apply remove_one_absent, (count_occ_not_In eq_dec) in E.
    destruct (eq_dec x y); subst; lia.
Qed.

(** An element of [l2] is in [l1], or in what is left of [l2] after
    removing [l1]. *)
Lemma diff_in : forall l1 l2 y, In y l2 -> In y l1 \/ In y (diff l2 l1).
Proof.
  intros l1 l2 y H.
  destruct (in_dec eq_dec y l1) as [I | N]; [left; exact I | right].
  apply (count_occ_In eq_dec). rewrite diff_count.
  apply (count_occ_In eq_dec) in H. apply (count_occ_not_In eq_dec) in N. lia.
Qed.

(** What is left of [l2] is in [l2]. *)
Lemma diff_incl : forall l1 l2 y, In y (diff l2 l1) -> In y l2.
Proof.
  intros l1 l2 y H. apply (count_occ_In eq_dec) in H. rewrite diff_count in H.
  apply (count_occ_In eq_dec). lia.
Qed.

Lemma take_spec : forall x l any l',
  take x l any = Some l' -> Permutation l (x :: l') \/ (any = true /\ l' = l).
Proof.
  unfold take; intros x l any l' H.
  destruct (remove_one x l) eqn:E.
  - injection H as <-. left. apply remove_one_perm, E.
  - destruct any; [| discriminate]. injection H as <-. auto.
Qed.

Lemma same_perm : forall l1 l2, same l1 l2 = true -> Permutation l1 l2.
Proof.
  intros l1; induction l1 as [| x l1 IH]; cbn; intros l2 H.
  - destruct l2; [reflexivity | discriminate].
  - destruct (remove_one x l2) as [l2' |] eqn:E; [| discriminate].
    rewrite (remove_one_perm _ _ _ E). apply perm_skip, IH, H.
Qed.

End Multiset.

(** ** The tactic of the soundness proofs *)

(** Decides a permutation of lists by counting each element's
    occurrences on both sides: [eq_dec] decides equality, and
    [diff_count] is [diff_count] at the checker's equality. *)
Ltac perm eq_dec diff_count :=
  apply (Permutation_count_occ eq_dec); intros ?x;
  repeat rewrite map_app; repeat rewrite app_nil_r; cbn [map];
  repeat first [rewrite count_occ_app | progress cbn [count_occ]];
  repeat rewrite diff_count;
  repeat match goal with
         | |- context [eq_dec ?a ?b] => destruct (eq_dec a b); try subst
         end;
  lia.
