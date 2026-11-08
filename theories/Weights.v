(* linlog © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * Weighted counts: refutations where copies add literals

    The balance of [Refutations] gives up on an atom below an exponential,
    since copies add its literals any number of times. This file weighs
    the literals instead, an integer per atom, and follows what each
    formula can contribute to the weighted count of a derivable sequent,
    copies included:

    - a [?A] contributes the sum of any number of [A]'s contributions,
      none included, and a [!A] contributes nothing, since a promotion's
      context is all [?] formulas, which may take none;
    - an atom declared dead contributes nothing a sum can cancel: its
      positive literal is [dead], as [0] is, and its negative literal
      absorbs, as [⊤] does, so an axiom on it still balances;
    - [⊗] proves its sides apart, so a [⊤] on one side does not absorb a
      [dead] on the other.

    Every derivable sequent can contribute zero or absorb
    ([weighted_balance], without weakening and without cut, Mix allowed).
    So when no formula of a sequent can absorb and every contribution the
    sequent can make is positive, it is not derivable
    ([weighted_refutation]); [overweight] tests that by computation from
    a lower bound per formula. With the weight [1] on one atom and [0] on
    the others, the test says that the atom's literals outside the
    exponentials outnumber the other sign's while every copy adds
    literals of one sign, which is the one-sided count. With the weights
    of a Petri net's places that no transition raises and the target asks
    raised (a Farkas certificate of a Horn program's state equation), and
    the atoms no firing can reach declared dead, the test says that the
    state equation of the transitions that can fire has no solution.

    With weakening a derivation may drop formulas, and the count holds
    only of formulas a Horn program's proof never drops: the outputs.
    [outputs] counts them, the sign of the literals given as outputs and
    every formula built so that each sequent of the derivation has one
    output; a weakening drops an input alone, which a count with drops
    of the formulas without an output follows ([affine_balance],
    [affine_refutation]).

    The two-sided calculus inherits both through its one-sided
    translation ([Refutations.ill_ll]). *)

From Stdlib Require Import Bool List Permutation ZArith Lia.
From Linlog Require Export Refutations.
Import ListNotations.

(** ** Outcomes *)

(** What a formula can contribute to a weighted count: a number, nothing
    that a sum can cancel ([dead]), or everything ([absorb]). *)
Inductive outcome : Type :=
| num : Z -> outcome
| dead : outcome
| absorb : outcome.

(** The contribution of a [⊗], whose two sides are proved apart: a
    [dead] side stays dead whatever the other absorbs. *)
Definition otimes (a b : outcome) : outcome :=
  match a, b with
  | dead, _ | _, dead => dead
  | absorb, _ | _, absorb => absorb
  | num m, num n => num (m + n)
  end.

(** The contribution of formulas beside each other in a sequent, or of
    a [⅋]: an absorbing one takes everything. *)
Definition opar (a b : outcome) : outcome :=
  match a, b with
  | absorb, _ | _, absorb => absorb
  | dead, _ | _, dead => dead
  | num m, num n => num (m + n)
  end.

(** What a derivable sequent can contribute: zero, or everything. *)
Definition settled (o : outcome) : bool :=
  match o with
  | num z => (z =? 0)%Z
  | dead => false
  | absorb => true
  end.

Lemma opar_comm : forall a b, opar a b = opar b a.
Proof. intros [] []; cbn; try reflexivity. f_equal. lia. Qed.

Lemma opar_assoc : forall a b c, opar a (opar b c) = opar (opar a b) c.
Proof. intros [] [] []; cbn; try reflexivity. f_equal. lia. Qed.

Lemma opar_zero_l : forall a, opar (num 0) a = a.
Proof. intros []; reflexivity. Qed.

Lemma opar_zero_r : forall a, opar a (num 0) = a.
Proof. intros []; cbn; rewrite ?Z.add_0_r; reflexivity. Qed.

(** Two settled sequents side by side, as Mix puts them. *)
Lemma settled_opar : forall a b,
  settled a = true -> settled b = true -> settled (opar a b) = true.
Proof.
  intros [] []; cbn; intros H1 H2; rewrite ?Z.eqb_eq in *;
    first [reflexivity | discriminate | apply Z.eqb_eq; lia].
Qed.

(** The premises of a [⊗] settled, its conclusion is. *)
Lemma settled_tensor : forall a b g1 g2,
  settled (opar a g1) = true -> settled (opar b g2) = true ->
  settled (opar (otimes a b) (opar g1 g2)) = true.
Proof.
  intros [] [] [] []; cbn; intros H1 H2; rewrite ?Z.eqb_eq in *;
    first [reflexivity | discriminate | apply Z.eqb_eq; lia].
Qed.

(** ** Lower bounds *)

(** A lower bound of the numbers a formula can contribute: [never] where
    it can contribute none, [from z] where each is at least [z], and
    [unbounded]. *)
Inductive low : Type :=
| never : low
| from : Z -> low
| unbounded : low.

(** The bound of a sum. *)
Definition lsum (x y : low) : low :=
  match x, y with
  | never, _ | _, never => never
  | from a, from b => from (a + b)
  | _, _ => unbounded
  end.

(** The bound of either. *)
Definition lmin (x y : low) : low :=
  match x, y with
  | never, z | z, never => z
  | from a, from b => from (Z.min a b)
  | _, _ => unbounded
  end.

(** The bound of a sum of any number of copies, none included. *)
Definition lstar (x : low) : low :=
  match x with
  | never => from 0
  | from z => if (0 <=? z)%Z then from 0 else unbounded
  | unbounded => unbounded
  end.

(** That [n] respects the bound. *)
Definition below (x : low) (n : Z) : Prop :=
  match x with
  | never => False
  | from z => (z <= n)%Z
  | unbounded => True
  end.

(** Whether a bound rules zero out: every number above zero, or none. *)
Definition positive (x : low) : bool :=
  match x with
  | never => true
  | from z => (0 <? z)%Z
  | unbounded => false
  end.

(** Whether something other than [dead] can be contributed, by a formula
    that may absorb ([w]) with the bound [x]. *)
Definition reach (w : bool) (x : low) : bool :=
  w || match x with never => false | _ => true end.

Lemma below_lsum : forall x y m n, below x m -> below y n -> below (lsum x y) (m + n).
Proof. intros [|a|] [|b|] m n; cbn; intros; auto; lia. Qed.

Lemma below_lmin_l : forall x y n, below x n -> below (lmin x y) n.
Proof. intros [|a|] [|b|] n; cbn; intros; auto; lia. Qed.

Lemma below_lmin_r : forall x y n, below y n -> below (lmin x y) n.
Proof. intros [|a|] [|b|] n; cbn; intros; auto; lia. Qed.

Lemma below_lstar_zero : forall x, below (lstar x) 0.
Proof. intros [|z|]; cbn; try lia; auto. destruct (0 <=? z)%Z; cbn; auto; lia. Qed.

Lemma below_lstar : forall x m n, below x m -> below (lstar x) n -> below (lstar x) (m + n).
Proof.
  intros [|z|] m n; cbn; intros Hm Hn; auto; [contradiction |].
  destruct (0 <=? z)%Z eqn:E; cbn in *; auto. apply Z.leb_le in E. lia.
Qed.

Lemma lmin_zero_lstar : forall x, lmin (from 0) (lstar x) = lstar x.
Proof. intros [|z|]; cbn; try reflexivity. destruct (0 <=? z)%Z; reflexivity. Qed.

Lemma reach_below : forall w x n, below x n -> reach w x = true.
Proof. intros w [|z|] n; cbn; intros; [contradiction | |]; apply orb_true_r. Qed.

Section Weights.

Context {atom : Type}.
Local Notation formula := (formula atom).
Local Notation iformula := (iformula atom).

(** The weight a table gives an atom, as certificates write it: the
    first entry's, zero for an atom it does not list. *)
Fixpoint weight_of (atom_eqb : atom -> atom -> bool) (table : list (atom * Z)) (a : atom) : Z :=
  match table with
  | [] => 0%Z
  | (b, w) :: table => if atom_eqb b a then w else weight_of atom_eqb table a
  end.

(** The weight of each atom, and the atoms declared dead. Every theorem
    holds whatever the two functions are. *)
Variable y : atom -> Z.
Variable d : atom -> bool.

(** ** What a formula can contribute *)

Section Contributions.

(** The formulas that may be dropped, contributing zero: none without
    weakening. *)
Variable drop : formula -> bool.

(** [out A o]: [A] can contribute [o], over its additive alternatives and
    the copies of its [?] subformulas. *)
Inductive out : formula -> outcome -> Prop :=
| out_var : forall b, out (var b) (if d b then dead else num (y b))
| out_covar : forall b, out (covar b) (if d b then absorb else num (- y b))
| out_one : out one (num 0)
| out_bot : out bot (num 0)
| out_top : out top absorb
| out_zero : out zero dead
| out_tens : forall A B a b, out A a -> out B b -> out (tens A B) (otimes a b)
| out_parr : forall A B a b, out A a -> out B b -> out (parr A B) (opar a b)
| out_with1 : forall A B a, out A a -> out (awith A B) a
| out_with2 : forall A B b, out B b -> out (awith A B) b
| out_plus1 : forall A B a, out A a -> out (aplus A B) a
| out_plus2 : forall A B b, out B b -> out (aplus A B) b
| out_oc : forall A, out (oc A) (num 0)
| out_wn_none : forall A, out (wn A) (num 0)
| out_wn_more : forall A a o, out A a -> out (wn A) o -> out (wn A) (opar a o)
| out_drop : forall A, drop A = true -> out A (num 0).

(** [outs l o]: the formulas of [l] side by side can contribute [o]. *)
Inductive outs : list formula -> outcome -> Prop :=
| outs_nil : outs [] (num 0)
| outs_cons : forall A l a o, out A a -> outs l o -> outs (A :: l) (opar a o).

Lemma out_exists : forall A, exists o, out A o.
Proof.
  induction A as [b|b| | | | |A [a HA] B [b HB]|A [a HA] B [b HB]|A [a HA] B _|A [a HA] B _|A _|A _];
    eexists; constructor; eassumption.
Qed.

Lemma outs_exists : forall l, exists o, outs l o.
Proof.
  induction l as [|A l [o H]]; [eexists; constructor |].
  destruct (out_exists A) as [a HA]. eexists. constructor; eassumption.
Qed.

Lemma outs_app : forall l1 l2 o1 o2,
  outs l1 o1 -> outs l2 o2 -> outs (l1 ++ l2) (opar o1 o2).
Proof.
  intros l1 l2 o1 o2 H1 H2. induction H1; cbn [app].
  - now rewrite opar_zero_l.
  - rewrite <- opar_assoc. constructor; assumption.
Qed.

Lemma outs_perm : forall l1 l2 o, Permutation l1 l2 -> outs l1 o -> outs l2 o.
Proof.
  intros l1 l2 o P. revert o. induction P; intros o H.
  - exact H.
  - inversion H; subst. constructor; auto.
  - inversion H as [|? ? a o1 Ha H1]; subst. inversion H1 as [|? ? b o2 Hb H2]; subst.
    rewrite opar_assoc, (opar_comm a b), <- opar_assoc.
    repeat constructor; assumption.
  - auto.
Qed.

Lemma outs_wn : forall l, outs (map wn l) (num 0).
Proof.
  induction l as [|A l IH]; cbn; [constructor |].
  change (num 0) with (opar (num 0) (num 0)). constructor; [constructor | exact IH].
Qed.

(** Copies of a [?] formula put together. *)
Lemma out_wn_merge : forall F a1, out F a1 -> forall A, F = wn A ->
  forall a2, out (wn A) a2 -> out (wn A) (opar a1 a2).
Proof.
  intros F a1 H. induction H; intros A' E a2 H2; try discriminate.
  - injection E as <-. now rewrite opar_zero_l.
  - injection E as <-. rewrite <- opar_assoc. apply out_wn_more; [assumption |].
    now apply IHout2.
  - now rewrite opar_zero_l.
Qed.

(** The bound of a formula that may be dropped includes zero. *)
Definition keep (A : formula) (x : low) : low :=
  if drop A then lmin (from 0) x else x.

(** A lower bound of the numbers [A] can contribute. *)
Fixpoint least (A : formula) : low :=
  keep A
    match A with
    | var b => if d b then never else from (y b)
    | covar b => if d b then never else from (- y b)
    | one | bot => from 0
    | top | zero => never
    | tens A B | parr A B => lsum (least A) (least B)
    | awith A B | aplus A B => lmin (least A) (least B)
    | oc _ => from 0
    | wn A => lstar (least A)
    end.

(** Whether [A] may absorb. *)
Fixpoint absorbs (A : formula) : bool :=
  match A with
  | covar b => d b
  | top => true
  | tens A B =>
      absorbs A && reach (absorbs B) (least B) || absorbs B && reach (absorbs A) (least A)
  | parr A B | awith A B | aplus A B => absorbs A || absorbs B
  | wn A => absorbs A
  | _ => false
  end.

(** The bound of a sequent: the sum over its formulas. *)
Fixpoint leasts (l : list formula) : low :=
  match l with
  | [] => from 0
  | A :: l => lsum (least A) (leasts l)
  end.

Lemma below_keep : forall A x n, below x n -> below (keep A x) n.
Proof. intros A x n H. unfold keep. destruct (drop A); [apply below_lmin_r |]; exact H. Qed.

(** The bounds hold of every contribution. *)
Lemma out_bound : forall A o, out A o ->
  (o = absorb -> absorbs A = true) /\ (forall n, o = num n -> below (least A) n).
Proof.
  intros A o H. induction H as [b|b| | | | |A B a b _ [IA NA] _ [IB NB]
    |A B a b _ [IA NA] _ [IB NB]|A B a _ [IA NA]|A B b _ [IB NB]|A B a _ [IA NA]
    |A B b _ [IB NB]|A|A|A a o _ [IA NA] _ [IO NO]|A D]; cbn [absorbs least] in *.
  - split; [intros E; destruct (d b); discriminate |].
    intros n E'. apply below_keep. destruct (d b); [discriminate |].
    injection E' as <-. cbn; lia.
  - split; [intros E; destruct (d b); [reflexivity | discriminate] |].
    intros n E'. apply below_keep. destruct (d b); [discriminate |].
    injection E' as <-. cbn; lia.
  - split; [discriminate |]. intros n E. apply below_keep. injection E as <-. cbn; lia.
  - split; [discriminate |]. intros n E. apply below_keep. injection E as <-. cbn; lia.
  - split; [reflexivity | discriminate].
  - split; discriminate.
  - split.
    + intros E. destruct a, b; cbn in E; try discriminate.
      * rewrite IB by reflexivity. rewrite (reach_below _ _ _ (NA _ eq_refl)).
        apply orb_true_r.
      * rewrite IA by reflexivity. rewrite (reach_below _ _ _ (NB _ eq_refl)). reflexivity.
      * rewrite IA by reflexivity. rewrite IB by reflexivity. reflexivity.
    + intros n E. apply below_keep. destruct a, b; cbn in E; try discriminate.
      injection E as <-. apply below_lsum; auto.
  - split.
    + intros E. destruct a, b; cbn in E; try discriminate;
        rewrite ?IA, ?IB by reflexivity; rewrite ?orb_true_r; reflexivity.
    + intros n E. apply below_keep. destruct a, b; cbn in E; try discriminate.
      injection E as <-. apply below_lsum; auto.
  - split; [intros E; now rewrite IA |].
    intros n E. apply below_keep, below_lmin_l. auto.
  - split; [intros E; rewrite IB by assumption; apply orb_true_r |].
    intros n E. apply below_keep, below_lmin_r. auto.
  - split; [intros E; now rewrite IA |].
    intros n E. apply below_keep, below_lmin_l. auto.
  - split; [intros E; rewrite IB by assumption; apply orb_true_r |].
    intros n E. apply below_keep, below_lmin_r. auto.
  - split; [discriminate |]. intros n E. apply below_keep. injection E as <-. cbn; lia.
  - split; [discriminate |]. intros n E. injection E as <-.
    unfold keep. destruct (drop (wn A)); rewrite ?lmin_zero_lstar; apply below_lstar_zero.
  - split.
    + intros E. destruct a, o; cbn in E; try discriminate; auto.
    + intros n E. unfold keep in *. destruct (drop (wn A)); rewrite ?lmin_zero_lstar in *;
        destruct a, o; cbn in E; try discriminate; injection E as <-;
        apply below_lstar; auto.
  - split; [discriminate |]. intros n E. injection E as <-.
    destruct A; cbn [least]; unfold keep; rewrite D; apply below_lmin_l; cbn; lia.
Qed.

Lemma outs_bound : forall l o, outs l o ->
  (o = absorb -> existsb absorbs l = true) /\ (forall n, o = num n -> below (leasts l) n).
Proof.
  intros l o H. induction H as [|A l a o Ha _ [IO NO]]; cbn [existsb leasts].
  - split; [discriminate |]. intros n E. injection E as <-. cbn; lia.
  - destruct (out_bound A a Ha) as [IA NA]. split.
    + intros E. destruct a, o; cbn in E; try discriminate;
        rewrite ?IA, ?IO by reflexivity; rewrite ?orb_true_r; reflexivity.
    + intros n E. destruct a, o; cbn in E; try discriminate. injection E as <-.
      apply below_lsum; auto.
Qed.

(** A sequent that may contribute zero or absorb, of which no formula
    absorbs and whose bound is positive, does not exist. *)
Lemma settled_bound : forall l o,
  outs l o -> settled o = true -> existsb absorbs l = false -> positive (leasts l) = true -> False.
Proof.
  intros l o H S A P. destruct (outs_bound l o H) as [IO NO].
  destruct o as [z| |]; cbn in S; try discriminate.
  - apply Z.eqb_eq in S as ->. specialize (NO 0%Z eq_refl).
    destruct (leasts l) as [|z|]; cbn in *; try discriminate; auto. apply Z.ltb_lt in P. lia.
  - rewrite (IO eq_refl) in A. discriminate.
Qed.

End Contributions.

(** ** Without weakening *)

(** Nothing is dropped. *)
Definition nodrop (A : formula) : bool := false.

(** Without weakening and without cut, every derivable sequent can
    contribute zero or absorb, Mix allowed. *)
Theorem weighted_balance : forall R l, ll R l -> weakening R = false -> cut R = false ->
  exists o, outs nodrop l o /\ settled o = true.
Proof.
  intros R l H W K. induction H.
  - eexists. split; [repeat constructor |].
    destruct (d a); cbn; [reflexivity | apply Z.eqb_eq; lia].
  - destruct IHll as [o [Ho S]]. exists o. split; [eapply outs_perm |]; eassumption.
  - eexists. split; [repeat constructor | reflexivity].
  - destruct IHll as [o [Ho S]]. exists (opar (num 0) o).
    split; [repeat constructor; assumption | now rewrite opar_zero_l].
  - destruct (outs_exists nodrop l) as [o Ho].
    exists (opar absorb o). split; [repeat constructor; assumption | reflexivity].
  - destruct IHll1 as [o1 [P1 S1]], IHll2 as [o2 [P2 S2]].
    inversion P1 as [|? ? a g1 Ha Hg1]; subst. inversion P2 as [|? ? b g2 Hb Hg2]; subst.
    exists (opar (otimes a b) (opar g1 g2)). split.
    + constructor; [constructor; assumption | apply outs_app; assumption].
    + apply settled_tensor; assumption.
  - destruct IHll as [o [Ho S]].
    inversion Ho as [|? ? a o1 Ha P1]; subst. inversion P1 as [|? ? b g Hb Hg]; subst.
    exists (opar (opar a b) g). split; [repeat constructor; assumption |].
    now rewrite <- opar_assoc.
  - destruct IHll1 as [o [Ho S]].
    inversion Ho as [|? ? a g Ha Hg]; subst.
    exists (opar a g). split; [repeat constructor; assumption | exact S].
  - destruct IHll as [o [Ho S]].
    inversion Ho as [|? ? a g Ha Hg]; subst.
    exists (opar a g). split; [apply outs_cons; [apply out_plus1 |]; assumption | exact S].
  - destruct IHll as [o [Ho S]].
    inversion Ho as [|? ? b g Hb Hg]; subst.
    exists (opar b g). split; [apply outs_cons; [apply out_plus2 |]; assumption | exact S].
  - exists (opar (num 0) (num 0)). split; [constructor; [constructor | apply outs_wn] |].
    reflexivity.
  - destruct IHll as [o [Ho S]].
    inversion Ho as [|? ? a g Ha Hg]; subst.
    exists (opar (opar a (num 0)) g). split.
    + constructor; [apply out_wn_more; [| apply out_wn_none] |]; assumption.
    + now rewrite opar_zero_r.
  - destruct IHll as [o [Ho S]]. exists (opar (num 0) o).
    split; [repeat constructor; assumption | now rewrite opar_zero_l].
  - destruct IHll as [o [Ho S]].
    inversion Ho as [|? ? a1 o1 Ha1 P1]; subst. inversion P1 as [|? ? a2 g Ha2 Hg]; subst.
    exists (opar (opar a1 a2) g). split.
    + constructor; [eapply out_wn_merge; [eassumption | reflexivity | assumption] | assumption].
    + now rewrite <- opar_assoc.
  - destruct IHll1 as [o1 [P1 S1]], IHll2 as [o2 [P2 S2]].
    exists (opar o1 o2). split; [apply outs_app; assumption | apply settled_opar; assumption].
  - congruence.
  - congruence.
Qed.

(** Whether the weights refute a sequent in a calculus: one without
    weakening and without cut, no formula that may absorb, and every
    contribution of the sequent above zero, or none. *)
Definition overweight (R : rules) (l : list formula) : bool :=
  negb (weakening R) && negb (cut R)
  && negb (existsb (absorbs nodrop) l) && positive (leasts nodrop l).

(** Weights that the test accepts refute a sequent. *)
Theorem weighted_refutation : forall R l, overweight R l = true -> ~ ll R l.
Proof.
  intros R l T H. unfold overweight in T.
  apply andb_prop in T as [T P]. apply andb_prop in T as [T A].
  apply andb_prop in T as [W K]. apply negb_true_iff in W, K, A.
  destruct (weighted_balance R l H W K) as [o [Ho S]].
  exact (settled_bound nodrop l o Ho S A P).
Qed.

(** Weights that the test accepts of the translation refute a two-sided
    sequent. *)
Theorem iweighted_refutation : forall R G C,
  overweight (lrules R) (one_sided G C) = true -> ~ ill R G C.
Proof.
  intros R G C T H. exact (weighted_refutation _ _ T (ill_ll R G C H)).
Qed.

(** ** With weakening *)

Section Outputs.

(** Whether the positive literals are the outputs, else the negative
    ones. *)
Variable p : bool.

(** The outputs of a formula: one for a literal of the output sign, a
    [1], a [⊤] and a [!] formula, none for the other literals, [⊥], [0]
    and a [?] formula; a [⊗] has one fewer than its sides, a [⅋] as many,
    an additive the more of its sides'. *)
Fixpoint outputs (A : formula) : Z :=
  match A with
  | var _ => if p then 1 else 0
  | covar _ => if p then 0 else 1
  | one | top | oc _ => 1
  | bot | zero | wn _ => 0
  | tens A B => outputs A + outputs B - 1
  | parr A B => outputs A + outputs B
  | awith A B | aplus A B => Z.max (outputs A) (outputs B)
  end.

(** Whether every subformula has outputs, none below zero, and every
    formula below a [?] has none. *)
Fixpoint shaped (A : formula) : bool :=
  (0 <=? outputs A)%Z &&
  match A with
  | tens A B | parr A B | awith A B | aplus A B => shaped A && shaped B
  | oc A => shaped A
  | wn A => (outputs A =? 0)%Z && shaped A
  | _ => true
  end.

(** The outputs of a sequent. *)
Fixpoint outputs_all (l : list formula) : Z :=
  match l with
  | [] => 0
  | A :: l => outputs A + outputs_all l
  end.

(** The formulas without an output may be dropped. *)
Definition droppable (A : formula) : bool := (outputs A =? 0)%Z.

Lemma shaped_outputs : forall A, shaped A = true -> (0 <= outputs A)%Z.
Proof. intros A H. destruct A; cbn [shaped] in H; apply andb_prop in H as [H _]; now apply Z.leb_le. Qed.

Lemma outputs_all_nonneg : forall l, forallb shaped l = true -> (0 <= outputs_all l)%Z.
Proof.
  induction l as [|A l IH]; cbn; [lia |]. intros H. apply andb_prop in H as [HA Hl].
  pose proof (shaped_outputs A HA). specialize (IH Hl). lia.
Qed.

Lemma outputs_all_app : forall l1 l2, outputs_all (l1 ++ l2) = (outputs_all l1 + outputs_all l2)%Z.
Proof. induction l1 as [|A l1 IH]; intro l2; cbn; [| rewrite IH]; lia. Qed.

Lemma outputs_all_perm : forall l1 l2, Permutation l1 l2 -> outputs_all l1 = outputs_all l2.
Proof. intros l1 l2 H. induction H; cbn; lia. Qed.

Lemma outputs_all_wn : forall l, outputs_all (map wn l) = 0%Z.
Proof. induction l; cbn; lia. Qed.

Lemma forallb_shaped_perm : forall l1 l2,
  Permutation l1 l2 -> forallb shaped l1 = forallb shaped l2.
Proof. exact (forallb_perm shaped). Qed.

(** Shortcuts through the shape of a compound formula. *)
Local Ltac unshape :=
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_prop in H as [? ?]
  | H : forallb _ (_ ++ _) = true |- _ => rewrite forallb_app in H
  | H : forallb _ (_ :: _) = true |- _ => cbn [forallb] in H
  | H : shaped (_ _) = true |- _ => cbn [shaped] in H
  | H : shaped (_ _ _) = true |- _ => cbn [shaped] in H
  end.

(** Without cut, every derivable sequent of shaped formulas has an
    output, and one with exactly one output can contribute zero or
    absorb, its formulas without an output dropped where weakening
    dropped them. *)
Theorem affine_balance : forall R l, ll R l -> cut R = false -> forallb shaped l = true ->
  (1 <= outputs_all l)%Z /\
  (outputs_all l = 1%Z -> exists o, outs droppable l o /\ settled o = true).
Proof.
  intros R l H K. induction H; intro F; cbn [outputs_all outputs] in *.
  - split; [destruct p; lia |]. intros _. eexists. split; [repeat constructor |].
    destruct (d a); cbn; [reflexivity | apply Z.eqb_eq; lia].
  - rewrite <- (forallb_shaped_perm _ _ H0) in F. destruct (IHll F) as [Q E].
    rewrite <- (outputs_all_perm _ _ H0). split; [exact Q |]. intros E1.
    destruct (E E1) as [o [Ho S]]. exists o. split; [eapply outs_perm |]; eassumption.
  - split; [lia |]. intros _. eexists. split; [repeat constructor | reflexivity].
  - unshape. destruct (IHll ltac:(assumption)) as [Q E]. split; [lia |]. intros E1.
    destruct (E ltac:(lia)) as [o [Ho S]]. exists (opar (num 0) o).
    split; [repeat constructor; assumption | now rewrite opar_zero_l].
  - unshape. pose proof (outputs_all_nonneg l ltac:(assumption)). split; [lia |]. intros _.
    destruct (outs_exists droppable l) as [o Ho].
    exists (opar absorb o). split; [repeat constructor; assumption | reflexivity].
  - unshape. destruct (IHll1 ltac:(cbn; rewrite ?andb_true_iff; tauto)) as [Q1 E1].
    destruct (IHll2 ltac:(cbn; rewrite ?andb_true_iff; tauto)) as [Q2 E2].
    cbn [outputs_all] in Q1, Q2, E1, E2. rewrite outputs_all_app.
    split; [lia |]. intros E.
    destruct (E1 ltac:(lia)) as [o1 [P1 S1]], (E2 ltac:(lia)) as [o2 [P2 S2]].
    inversion P1 as [|? ? a g1 Ha Hg1]; subst. inversion P2 as [|? ? b g2 Hb Hg2]; subst.
    exists (opar (otimes a b) (opar g1 g2)). split.
    + constructor; [constructor; assumption | apply outs_app; assumption].
    + apply settled_tensor; assumption.
  - unshape. destruct (IHll ltac:(cbn; rewrite ?andb_true_iff; tauto)) as [Q E].
    cbn [outputs_all] in Q, E. split; [lia |]. intros E1.
    destruct (E ltac:(lia)) as [o [Ho S]].
    inversion Ho as [|? ? a o1 Ha P1]; subst. inversion P1 as [|? ? b g Hb Hg]; subst.
    exists (opar (opar a b) g). split; [repeat constructor; assumption |].
    now rewrite <- opar_assoc.
  - unshape. destruct (IHll1 ltac:(cbn; rewrite ?andb_true_iff; tauto)) as [Q1 E1].
    destruct (IHll2 ltac:(cbn; rewrite ?andb_true_iff; tauto)) as [Q2 E2].
    cbn [outputs_all] in Q1, Q2, E1, E2. split; [lia |]. intros E.
    destruct (E1 ltac:(lia)) as [o [Ho S]].
    inversion Ho as [|? ? a g Ha Hg]; subst.
    exists (opar a g). split; [repeat constructor; assumption | exact S].
  - unshape. destruct (IHll ltac:(cbn; rewrite ?andb_true_iff; tauto)) as [Q E].
    cbn [outputs_all] in Q, E. split; [lia |]. intros E1.
    destruct (E ltac:(lia)) as [o [Ho S]].
    inversion Ho as [|? ? a g Ha Hg]; subst.
    exists (opar a g). split; [apply outs_cons; [apply out_plus1 |]; assumption | exact S].
  - unshape. destruct (IHll ltac:(cbn; rewrite ?andb_true_iff; tauto)) as [Q E].
    cbn [outputs_all] in Q, E. split; [lia |]. intros E1.
    destruct (E ltac:(lia)) as [o [Ho S]].
    inversion Ho as [|? ? b g Hb Hg]; subst.
    exists (opar b g). split; [apply outs_cons; [apply out_plus2 |]; assumption | exact S].
  - rewrite outputs_all_wn. split; [lia |]. intros _.
    exists (opar (num 0) (num 0)). split; [constructor; [constructor | apply outs_wn] |].
    reflexivity.
  - unshape. match goal with Hq : (outputs _ =? 0)%Z = true |- _ => apply Z.eqb_eq in Hq end.
    destruct (IHll ltac:(cbn; rewrite ?andb_true_iff; tauto)) as [Q E].
    cbn [outputs_all] in Q, E. split; [lia |]. intros E1.
    destruct (E ltac:(lia)) as [o [Ho S]].
    inversion Ho as [|? ? a g Ha Hg]; subst.
    exists (opar (opar a (num 0)) g). split.
    + constructor; [apply out_wn_more; [| apply out_wn_none] |]; assumption.
    + now rewrite opar_zero_r.
  - unshape. destruct (IHll ltac:(assumption)) as [Q E]. split; [lia |]. intros E1.
    destruct (E ltac:(lia)) as [o [Ho S]]. exists (opar (num 0) o).
    split; [repeat constructor; assumption | now rewrite opar_zero_l].
  - unshape. destruct (IHll ltac:(cbn; rewrite ?andb_true_iff; tauto)) as [Q E].
    cbn [outputs_all outputs] in Q, E. split; [lia |]. intros E1.
    destruct (E ltac:(lia)) as [o [Ho S]].
    inversion Ho as [|? ? a1 o1 Ha1 P1]; subst. inversion P1 as [|? ? a2 g Ha2 Hg]; subst.
    exists (opar (opar a1 a2) g). split.
    + constructor; [eapply out_wn_merge; [eassumption | reflexivity | assumption] | assumption].
    + now rewrite <- opar_assoc.
  - rewrite forallb_app in F. apply andb_prop in F as [F1 F2].
    destruct (IHll1 F1) as [Q1 _], (IHll2 F2) as [Q2 _].
    rewrite outputs_all_app. split; [lia |]. lia.
  - unshape. pose proof (shaped_outputs A ltac:(assumption)) as N.
    destruct (IHll ltac:(assumption)) as [Q E]. split; [lia |]. intros E1.
    destruct (E ltac:(lia)) as [o [Ho S]]. exists (opar (num 0) o). split.
    + constructor; [apply out_drop; unfold droppable; apply Z.eqb_eq; lia | assumption].
    + now rewrite opar_zero_l.
  - congruence.
Qed.

(** Whether the weights refute a sequent in a calculus with weakening or
    without: one without cut, shaped formulas with one output, no formula
    that may absorb, and every contribution of the sequent above zero,
    or none, the formulas without an output dropped or not. *)
Definition overweight_affine (R : rules) (l : list formula) : bool :=
  negb (cut R) && forallb shaped l && (outputs_all l =? 1)%Z
  && negb (existsb (absorbs droppable) l) && positive (leasts droppable l).

(** Weights that the test accepts refute a sequent, with weakening or
    without. *)
Theorem affine_refutation : forall R l, overweight_affine R l = true -> ~ ll R l.
Proof.
  intros R l T H. unfold overweight_affine in T.
  apply andb_prop in T as [T P]. apply andb_prop in T as [T A].
  apply andb_prop in T as [T O]. apply andb_prop in T as [K F].
  apply negb_true_iff in K, A. apply Z.eqb_eq in O.
  destruct (affine_balance R l H K F) as [_ E].
  destruct (E O) as [o [Ho S]].
  exact (settled_bound droppable l o Ho S A P).
Qed.

End Outputs.

(** Weights that the test accepts of the translation refute a two-sided
    sequent, with weakening or without. *)
Theorem iaffine_refutation : forall p R G C,
  overweight_affine p (lrules R) (one_sided G C) = true -> ~ ill R G C.
Proof.
  intros p R G C T H. exact (affine_refutation p _ _ T (ill_ll R G C H)).
Qed.

End Weights.
