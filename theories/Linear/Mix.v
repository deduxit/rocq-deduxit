(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * Mix as a hypothesis [?(⊥ ⊗ ⊥)]

    A derivation that uses binary Mix becomes a derivation without Mix
    of the same sequent with [?(⊥ ⊗ ⊥)] added. It uses no cut the
    first one did not use. The proof carries the extra formula up the
    derivation. A Mix of [⊢ Γ] and [⊢ Δ] becomes the [⊗] of
    [⊢ ⊥, ?(⊥ ⊗ ⊥), Γ] and [⊢ ⊥, ?(⊥ ⊗ ⊥), Δ] under a dereliction.
    Every rule with two premises, cut included, makes two copies of the
    extra formula, and a contraction merges them. The proof follows
    Yalla's [mix_to_ll] ([ll_fragments.v]) for binary Mix. *)

From Stdlib Require Import List Permutation.
From Deduxit.Linear Require Export Calculus.
Import ListNotations.

Section Mix.

Context {atom : Type}.
Local Notation formula := (formula atom).

(** A rule with one premise, applied behind an extra first formula
    [X]. *)
Lemma behind : forall R (X A B : formula) l,
  (forall m, ll R (A :: m) -> ll R (B :: m)) -> ll R (X :: A :: l) -> ll R (X :: B :: l).
Proof.
  intros R X A B l rule H.
  eapply ex_r; [apply rule; eapply ex_r; [exact H | apply perm_swap] | apply perm_swap].
Qed.

(** A derivation of [⊢ Γ] in any calculus gives a derivation of
    [⊢ ?(⊥ ⊗ ⊥), Γ] in the same calculus without Mix, with the same
    [weakening] and [cut]. *)
Theorem mix_to_ll : forall R (l : list formula),
  ll R l ->
  ll {| mix := false; weakening := weakening R; cut := cut R |} (wn (tens bot bot) :: l).
Proof.
  intros R l H. set (R' := {| mix := false; weakening := weakening R; cut := cut R |}).
  induction H.
  - apply wk_r, ax_r.
  - eapply ex_r; [exact IHll | apply perm_skip, H0].
  - apply wk_r, one_r.
  - eapply ex_r; [apply bot_r, IHll | apply perm_swap].
  - apply wk_r, top_r.
  - apply co_r.
    eapply ex_r.
    + apply (tens_r _ A B (wn (tens bot bot) :: l1) (wn (tens bot bot) :: l2)).
      * eapply ex_r; [exact IHll1 | apply perm_swap].
      * eapply ex_r; [exact IHll2 | apply perm_swap].
    + cbn. rewrite <- Permutation_middle.
      apply perm_trans with (wn (tens bot bot) :: tens A B :: wn (tens bot bot) :: l1 ++ l2);
        [apply perm_swap | apply perm_skip, perm_swap].
  - eapply ex_r; [apply parr_r | apply perm_swap].
    eapply ex_r; [exact IHll |].
    apply perm_trans with (A :: wn (tens bot bot) :: B :: l);
      [apply perm_swap | apply perm_skip, perm_swap].
  - eapply ex_r; [apply with_r | apply perm_swap].
    + eapply ex_r; [exact IHll1 | apply perm_swap].
    + eapply ex_r; [exact IHll2 | apply perm_swap].
  - revert IHll. apply behind. intro. apply plus_r1.
  - revert IHll. apply behind. intro. apply plus_r2.
  - eapply ex_r; [| apply perm_swap].
    apply (oc_r R' A (tens bot bot :: l)).
    eapply ex_r; [exact IHll | apply perm_swap].
  - revert IHll. apply behind. intro. apply de_r.
  - eapply ex_r; [apply wk_r, IHll | apply perm_swap].
  - eapply ex_r; [apply co_r | apply perm_swap].
    eapply ex_r; [exact IHll |].
    apply perm_trans with (wn A :: wn (tens bot bot) :: wn A :: l);
      [apply perm_swap | apply perm_skip, perm_swap].
  - (* Mix: the [⊗] of the two premises, each under a [⊥], then a
   dereliction. *)
    apply co_r, co_r.
    eapply ex_r.
    + apply de_r.
      apply (tens_r _ bot bot (wn (tens bot bot) :: l1) (wn (tens bot bot) :: l2));
        apply bot_r; [exact IHll1 | exact IHll2].
    + cbn. apply perm_skip, perm_skip, Permutation_sym, Permutation_middle.
  - eapply ex_r; [apply weakening_r, IHll | apply perm_swap]. assumption.
  - (* Cut: the two premises' copies contracted. *)
    apply co_r.
    eapply ex_r.
    + refine (cut_r R' _ A (wn (tens bot bot) :: l1) (wn (tens bot bot) :: l2) _ _).
      * assumption.
      * eapply ex_r; [exact IHll1 | apply perm_swap].
      * eapply ex_r; [exact IHll2 | apply perm_swap].
    + cbn. apply perm_skip. symmetry. apply Permutation_middle.
Qed.

(** From Mix to classical linear logic: a derivation of [⊢ Γ] with Mix
    gives one of [⊢ ?(⊥ ⊗ ⊥), Γ] in classical linear logic. *)
Corollary mix_to_classical : forall l : list formula,
  ll {| mix := true; weakening := false; cut := false |} l ->
  ll classical (wn (tens bot bot) :: l).
Proof. intros l H. exact (mix_to_ll _ l H). Qed.

End Mix.
