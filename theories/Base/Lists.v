(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * Lists, as the checkers of several calculi use them

    Membership of a number, and facts of [forallb] and [existsb], which
    the countermodel checkers of intuitionistic and of modal logic and
    the refutations of linear logic share. [KripkeCheck.mem],
    [FirstOrderCheck.kmem], [Countermodel.among] and the like are
    instances of these. *)

From Stdlib Require Import Bool List Permutation Arith.

(** Whether the number [v] is in [l]. *)
Definition mem (v : nat) (l : list nat) : bool := existsb (Nat.eqb v) l.

Lemma mem_In : forall v l, mem v l = true <-> In v l.
Proof.
  intros v l. unfold mem. rewrite existsb_exists. split.
  - intros [x [Hx E]]. apply Nat.eqb_eq in E. subst. exact Hx.
  - intros H. exists v. split; [exact H | apply Nat.eqb_refl].
Qed.

(** A test that fails on every member fails on each of them. *)
Lemma existsb_false : forall {X} (f : X -> bool) l x,
  existsb f l = false -> In x l -> f x = false.
Proof.
  intros X f l x H Hx. destruct (f x) eqn:E; [| reflexivity].
  assert (existsb f l = true) by (apply existsb_exists; exists x; auto). congruence.
Qed.

(** [forallb] reads a list as a multiset. *)
Lemma forallb_perm : forall {X} (f : X -> bool) l1 l2,
  Permutation l1 l2 -> forallb f l1 = forallb f l2.
Proof.
  intros X f l1 l2 H. induction H as [| x l1 l2 _ IH | x y l | l1 l2 l3 _ IH1 _ IH2]; cbn.
  - reflexivity.
  - now rewrite IH.
  - destruct (f x), (f y); reflexivity.
  - congruence.
Qed.

(** [existsb] reads a list as a multiset. *)
Lemma existsb_perm : forall {X} (f : X -> bool) l1 l2,
  Permutation l1 l2 -> existsb f l1 = existsb f l2.
Proof.
  intros X f l1 l2 H. induction H as [| x l1 l2 _ IH | x y l | l1 l2 l3 _ IH1 _ IH2]; cbn.
  - reflexivity.
  - now rewrite IH.
  - destruct (f x), (f y); reflexivity.
  - congruence.
Qed.
