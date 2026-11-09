(* linlog © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * Weighted counts of first-order sequents

    The weighted count of [Weights] over the first-order calculi, without
    weakening: a quantifier's rule changes no literal's predicate, and no
    literal without a bound variable at all, so a count that weighs each
    literal by its predicate, or by the whole literal where no literal of
    the predicate has a bound variable, is the same of an instance as of
    the quantified body. [value] is that weight: [table p ts] for a
    predicate [fixed p], whose literals the test requires closed
    ([pinned]), [weight p] for the others. With the weight [1] on one
    predicate the test is the one-sided count over all its atoms
    together; with [1] on one closed atom of a fixed predicate, over that
    atom alone.

    [weighted_balance] and [weighted_refutation] state it one-sided;
    [ill_ll] embeds the two-sided calculus in the one-sided one, as
    [Refutations.ill_ll] does the propositional one, and
    [iweighted_refutation] states it two-sided. No atom is declared dead
    here: the dead atoms serve the state equation of Horn programs, which
    are propositional. The outcomes and bounds are those of [Weights]. *)

From Stdlib Require Import Bool List Permutation ZArith Lia.
From Deduxit.Linear Require Calculus Intuitionistic TermsCheck.
From Deduxit.Linear Require Weights.
Import Weights(outcome(..), otimes, opar, settled, opar_comm, opar_assoc, opar_zero_l,
  opar_zero_r, settled_opar, settled_tensor, low(..), lsum, lmin, lstar, below, positive,
  reach, below_lsum, below_lmin_l, below_lmin_r, below_lstar_zero, below_lstar, reach_below).
From Deduxit.Linear Require Import FirstOrderCalculus FirstOrderIntuitionistic.
Import ListNotations.

Section Weights.

Context {symbol : Type}.
Local Notation term := (term symbol).
Local Notation formula := (formula symbol).
Local Notation iformula := (iformula symbol).

(** The predicates weighed by their literals, the weights of their
    literals, and the weights of the other predicates. Every theorem
    holds whatever the three functions are. *)
Variable fixed : symbol -> bool.
Variable table : symbol -> list term -> Z.
Variable weight : symbol -> Z.

(** The weight of a literal. *)
Definition value (p : symbol) (ts : list term) : Z :=
  if fixed p then table p ts else weight p.

(** [out A o]: [A] can contribute [o], over its additive alternatives,
    the copies of its [?] subformulas and the instances of its
    quantifiers. *)
Inductive out : formula -> outcome -> Prop :=
| out_var : forall p ts, out (var p ts) (num (value p ts))
| out_covar : forall p ts, out (covar p ts) (num (- value p ts))
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
| out_fall : forall A t o, out (subst 0 t A) o -> out (fall A) o
| out_fex : forall A t o, out (subst 0 t A) o -> out (fex A) o.

(** [outs l o]: the formulas of [l] side by side can contribute [o]. *)
Inductive outs : list formula -> outcome -> Prop :=
| outs_nil : outs [] (num 0)
| outs_cons : forall A l a o, out A a -> outs l o -> outs (A :: l) (opar a o).

(** The connectives of a formula, which an instance keeps. *)
Fixpoint size (A : formula) : nat :=
  match A with
  | var _ _ | covar _ _ | one | bot | top | zero => 1
  | tens A B | parr A B | awith A B | aplus A B => S (size A + size B)
  | oc A | wn A | fall A | fex A => S (size A)
  end.

Lemma size_subst : forall A k t, size (subst k t A) = size A.
Proof. induction A; intros k t; cbn; rewrite ?IHA, ?IHA1, ?IHA2; reflexivity. Qed.

Lemma out_exists : forall A, exists o, out A o.
Proof.
  intro A. remember (size A) as n eqn:E. assert (L : size A <= n) by lia. clear E.
  revert A L. induction n as [|n IH]; intros A L; [destruct A; cbn in L; lia |].
  destruct A as [p ts|p ts| | | | |A B|A B|A B|A B|A|A|A|A]; cbn in L;
    try (eexists; constructor; fail).
  - destruct (IH A ltac:(lia)) as [a HA], (IH B ltac:(lia)) as [b HB].
    eexists. constructor; eassumption.
  - destruct (IH A ltac:(lia)) as [a HA], (IH B ltac:(lia)) as [b HB].
    eexists. constructor; eassumption.
  - destruct (IH A ltac:(lia)) as [a HA]. eexists. apply out_with1; eassumption.
  - destruct (IH A ltac:(lia)) as [a HA]. eexists. apply out_plus1; eassumption.
  - destruct (IH (subst 0 (eigen 0) A) ltac:(rewrite size_subst; lia)) as [a HA].
    eexists. eapply out_fall; eassumption.
  - destruct (IH (subst 0 (eigen 0) A) ltac:(rewrite size_subst; lia)) as [a HA].
    eexists. eapply out_fex; eassumption.
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

Lemma out_wn_merge : forall F a1, out F a1 -> forall A, F = wn A ->
  forall a2, out (wn A) a2 -> out (wn A) (opar a1 a2).
Proof.
  intros F a1 H. induction H; intros A' E a2 H2; try discriminate.
  - injection E as <-. now rewrite opar_zero_l.
  - injection E as <-. rewrite <- opar_assoc. apply out_wn_more; [assumption |].
    now apply IHout2.
Qed.

(** ** Bounds *)

(** Whether every literal of a fixed predicate in [A] is closed, so that
    no instance changes it. *)
Fixpoint pinned (A : formula) : bool :=
  match A with
  | var p ts | covar p ts => negb (fixed p) || forallb tclosed ts
  | one | bot | top | zero => true
  | tens A B | parr A B | awith A B | aplus A B => pinned A && pinned B
  | oc A | wn A | fall A | fex A => pinned A
  end.

(** A lower bound of the numbers [A] can contribute. *)
Fixpoint least (A : formula) : low :=
  match A with
  | var p ts => from (value p ts)
  | covar p ts => from (- value p ts)
  | one | bot => from 0
  | top | zero => never
  | tens A B | parr A B => lsum (least A) (least B)
  | awith A B | aplus A B => lmin (least A) (least B)
  | oc _ => from 0
  | wn A => lstar (least A)
  | fall A | fex A => least A
  end.

(** Whether [A] may absorb. *)
Fixpoint absorbs (A : formula) : bool :=
  match A with
  | top => true
  | tens A B =>
      absorbs A && reach (absorbs B) (least B) || absorbs B && reach (absorbs A) (least A)
  | parr A B | awith A B | aplus A B => absorbs A || absorbs B
  | wn A | fall A | fex A => absorbs A
  | _ => false
  end.

(** The bound of a sequent. *)
Fixpoint leasts (l : list formula) : low :=
  match l with
  | [] => from 0
  | A :: l => lsum (least A) (leasts l)
  end.

Lemma tsubst_closed : forall (t : term) k u, tclosed t = true -> tsubst k u t = t.
Proof.
  induction t as [n|a|f l IH] using TermsCheck.term_ind'; intros k u C; cbn in *;
    try discriminate; [reflexivity |].
  f_equal. induction IH as [|t l Ht _ IHl]; cbn in *; [reflexivity |].
  apply andb_prop in C as [Ct Cl]. now rewrite Ht, IHl.
Qed.

Lemma value_subst : forall p ts k u, negb (fixed p) || forallb tclosed ts = true ->
  value p (map (tsubst k u) ts) = value p ts.
Proof.
  intros p ts k u P. unfold value. destruct (fixed p); cbn in P; [| reflexivity].
  f_equal. induction ts as [|t ts IH]; cbn in *; [reflexivity |].
  apply andb_prop in P as [Pt Pts]. now rewrite tsubst_closed, IH.
Qed.

(** An instance of a pinned formula has its bounds, and is pinned. *)
Lemma subst_pinned : forall A k u, pinned A = true ->
  pinned (subst k u A) = true /\ least (subst k u A) = least A
  /\ absorbs (subst k u A) = absorbs A.
Proof.
  induction A as [p ts|p ts| | | | |A IA B IB|A IA B IB|A IA B IB|A IA B IB|A IA|A IA|A IA|A IA];
    intros k u P; cbn [pinned subst least absorbs] in *;
    try (apply andb_prop in P as [PA PB];
         destruct (IA k u PA) as [QA [LA AA]], (IB k u PB) as [QB [LB AB]];
         rewrite QA, QB, LA, LB, AA, AB; repeat split; fail);
    try (destruct (IA k u P) as [QA [LA AA]]; rewrite QA, LA, AA; repeat split; fail);
    try (destruct (IA (S k) u P) as [QA [LA AA]]; rewrite QA, LA, AA; repeat split; fail);
    try (destruct (IA k u P) as [QA _]; rewrite QA; repeat split; fail);
    try (repeat split; reflexivity).
  - rewrite value_subst by exact P. split; [| split; reflexivity].
    destruct (fixed p); cbn in *; [| reflexivity].
    induction ts as [|t ts IH]; cbn in *; [reflexivity |].
    apply andb_prop in P as [Pt Pts]. rewrite tsubst_closed by exact Pt. now rewrite Pt, IH.
  - rewrite value_subst by exact P. split; [| split; reflexivity].
    destruct (fixed p); cbn in *; [| reflexivity].
    induction ts as [|t ts IH]; cbn in *; [reflexivity |].
    apply andb_prop in P as [Pt Pts]. rewrite tsubst_closed by exact Pt. now rewrite Pt, IH.
Qed.

(** The bounds hold of every contribution of a pinned formula. *)
Lemma out_bound : forall A o, out A o -> pinned A = true ->
  (o = absorb -> absorbs A = true) /\ (forall n, o = num n -> below (least A) n).
Proof.
  intros A o H. induction H as [p ts|p ts| | | | |A B a b _ IA _ IB
    |A B a b _ IA _ IB|A B a _ IA|A B b _ IB|A B a _ IA
    |A B b _ IB|A|A|A a o _ IA _ IO|A t o _ IA|A t o _ IA]; intros P;
    cbn [pinned absorbs least] in *.
  - split; [discriminate |]. intros n E. injection E as <-. cbn; lia.
  - split; [discriminate |]. intros n E. injection E as <-. cbn; lia.
  - split; [discriminate |]. intros n E. injection E as <-. cbn; lia.
  - split; [discriminate |]. intros n E. injection E as <-. cbn; lia.
  - split; [reflexivity | discriminate].
  - split; discriminate.
  - apply andb_prop in P as [PA PB]. destruct (IA PA) as [IA' NA], (IB PB) as [IB' NB]. split.
    + intros E. destruct a, b; cbn in E; try discriminate.
      * rewrite IB' by reflexivity. rewrite (reach_below _ _ _ (NA _ eq_refl)).
        apply orb_true_r.
      * rewrite IA' by reflexivity. rewrite (reach_below _ _ _ (NB _ eq_refl)). reflexivity.
      * rewrite IA', IB' by reflexivity. reflexivity.
    + intros n E. destruct a, b; cbn in E; try discriminate.
      injection E as <-. apply below_lsum; auto.
  - apply andb_prop in P as [PA PB]. destruct (IA PA) as [IA' NA], (IB PB) as [IB' NB]. split.
    + intros E. destruct a, b; cbn in E; try discriminate;
        rewrite ?IA', ?IB' by reflexivity; rewrite ?orb_true_r; reflexivity.
    + intros n E. destruct a, b; cbn in E; try discriminate.
      injection E as <-. apply below_lsum; auto.
  - apply andb_prop in P as [PA _]. destruct (IA PA) as [IA' NA].
    split; [intros E; now rewrite IA' |]. intros n E. apply below_lmin_l. auto.
  - apply andb_prop in P as [_ PB]. destruct (IB PB) as [IB' NB].
    split; [intros E; rewrite IB' by assumption; apply orb_true_r |].
    intros n E. apply below_lmin_r. auto.
  - apply andb_prop in P as [PA _]. destruct (IA PA) as [IA' NA].
    split; [intros E; now rewrite IA' |]. intros n E. apply below_lmin_l. auto.
  - apply andb_prop in P as [_ PB]. destruct (IB PB) as [IB' NB].
    split; [intros E; rewrite IB' by assumption; apply orb_true_r |].
    intros n E. apply below_lmin_r. auto.
  - split; [discriminate |]. intros n E. injection E as <-. cbn; lia.
  - split; [discriminate |]. intros n E. injection E as <-. apply below_lstar_zero.
  - destruct (IA P) as [IA' NA], (IO P) as [IO' NO]. split.
    + intros E. destruct a, o; cbn in E; try discriminate; auto.
    + intros n E. destruct a, o; cbn in E; try discriminate. injection E as <-.
      apply below_lstar; auto.
  - destruct (subst_pinned A 0 t P) as [Q [L Ab]]. rewrite <- L, <- Ab. exact (IA Q).
  - destruct (subst_pinned A 0 t P) as [Q [L Ab]]. rewrite <- L, <- Ab. exact (IA Q).
Qed.

Lemma outs_bound : forall l o, outs l o -> forallb pinned l = true ->
  (o = absorb -> existsb absorbs l = true) /\ (forall n, o = num n -> below (leasts l) n).
Proof.
  intros l o H. induction H as [|A l a o Ha _ IH]; intros P; cbn [existsb leasts forallb] in *.
  - split; [discriminate |]. intros n E. injection E as <-. cbn; lia.
  - apply andb_prop in P as [PA Pl].
    destruct (out_bound A a Ha PA) as [IA NA], (IH Pl) as [IO NO]. split.
    + intros E. destruct a, o; cbn in E; try discriminate;
        rewrite ?IA, ?IO by reflexivity; rewrite ?orb_true_r; reflexivity.
    + intros n E. destruct a, o; cbn in E; try discriminate. injection E as <-.
      apply below_lsum; auto.
Qed.

(** ** The invariant and the refutation *)

(** Without weakening and without cut, every derivable sequent can
    contribute zero or absorb, Mix allowed. *)
Theorem weighted_balance : forall R l, ll R l ->
  Calculus.weakening R = false -> Calculus.cut R = false ->
  exists o, outs l o /\ settled o = true.
Proof.
  intros R l H W K. induction H.
  - eexists. split; [repeat constructor |]. cbn. apply Z.eqb_eq. lia.
  - destruct IHll as [o [Ho S]]. exists o. split; [eapply outs_perm |]; eassumption.
  - eexists. split; [repeat constructor | reflexivity].
  - destruct IHll as [o [Ho S]]. exists (opar (num 0) o).
    split; [repeat constructor; assumption | now rewrite opar_zero_l].
  - destruct (outs_exists l) as [o Ho].
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
  - destruct IHll1 as [o [Ho S]]. inversion Ho as [|? ? a g Ha Hg]; subst.
    exists (opar a g). split; [repeat constructor; assumption | exact S].
  - destruct IHll as [o [Ho S]]. inversion Ho as [|? ? a g Ha Hg]; subst.
    exists (opar a g). split; [apply outs_cons; [apply out_plus1 |]; assumption | exact S].
  - destruct IHll as [o [Ho S]]. inversion Ho as [|? ? b g Hb Hg]; subst.
    exists (opar b g). split; [apply outs_cons; [apply out_plus2 |]; assumption | exact S].
  - exists (opar (num 0) (num 0)). split; [constructor; [constructor | apply outs_wn] |].
    reflexivity.
  - destruct IHll as [o [Ho S]]. inversion Ho as [|? ? a g Ha Hg]; subst.
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
  - destruct IHll as [o [Ho S]]. inversion Ho as [|? ? a' g Ha Hg]; subst.
    exists (opar a' g). split; [apply outs_cons; [eapply out_fall |]; eassumption | exact S].
  - destruct IHll as [o [Ho S]]. inversion Ho as [|? ? a' g Ha Hg]; subst.
    exists (opar a' g). split; [apply outs_cons; [eapply out_fex |]; eassumption | exact S].
Qed.

(** Whether the weights refute a sequent in a calculus: one without
    weakening and without cut, every literal of a fixed predicate
    closed, no formula that may absorb, and every contribution of the
    sequent above zero, or none. *)
Definition overweight (R : Calculus.rules) (l : list formula) : bool :=
  negb (Calculus.weakening R) && negb (Calculus.cut R) && forallb pinned l
  && negb (existsb absorbs l) && positive (leasts l).

(** Weights that the test accepts refute a sequent. *)
Theorem weighted_refutation : forall R l, overweight R l = true -> ~ ll R l.
Proof.
  intros R l T H. unfold overweight in T.
  apply andb_prop in T as [T Q]. apply andb_prop in T as [T A].
  apply andb_prop in T as [T P]. apply andb_prop in T as [W K].
  apply negb_true_iff in W, K, A.
  destruct (weighted_balance R l H W K) as [o [Ho S]].
  destruct (outs_bound l o Ho P) as [IO NO].
  destruct o as [z| |]; cbn in S; try discriminate.
  - apply Z.eqb_eq in S as ->. specialize (NO 0%Z eq_refl).
    destruct (leasts l) as [|z|]; cbn in *; try discriminate; auto. apply Z.ltb_lt in Q. lia.
  - rewrite (IO eq_refl) in A. discriminate.
Qed.

End Weights.

(** ** The two-sided calculus in the one-sided one *)

Section Translation.

Context {symbol : Type}.
Local Notation formula := (formula symbol).
Local Notation iformula := (iformula symbol).

(** A first-order intuitionistic formula as a one-sided one: [A ⊸ B] is
    [A⊥ ⅋ B]. *)
Fixpoint itr (A : iformula) : formula :=
  match A with
  | ivar p ts => var p ts
  | ione => one
  | itens A B => tens (itr A) (itr B)
  | ilmap A B => parr (dual (itr A)) (itr B)
  | itop => top
  | iwith A B => awith (itr A) (itr B)
  | izero => zero
  | iplus A B => aplus (itr A) (itr B)
  | ioc A => oc (itr A)
  | iall A => fall (itr A)
  | iex A => fex (itr A)
  end.

(** A two-sided sequent [Γ ⊢ C] as the one-sided [⊢ C, Γ⊥]. *)
Definition one_sided (G : list iformula) (C : iformula) : list formula :=
  itr C :: map (fun A => dual (itr A)) G.

Lemma dual_dual : forall A : formula, dual (dual A) = A.
Proof. induction A; cbn; congruence. Qed.

Lemma dual_subst : forall (A : formula) k u, dual (subst k u A) = subst k u (dual A).
Proof. induction A; intros k u; cbn; congruence. Qed.

Lemma itr_isubst : forall A k u, itr (isubst k u A) = subst k u (itr A).
Proof. induction A; intros k u; cbn; rewrite ?IHA, ?IHA1, ?IHA2, ?dual_subst; reflexivity. Qed.

Lemma occurs_dual : forall b (A : formula), occurs b (dual A) = occurs b A.
Proof. induction A; cbn; congruence. Qed.

Lemma occurs_itr : forall b A, occurs b (itr A) = ioccurs b A.
Proof. induction A; cbn; rewrite ?occurs_dual; congruence. Qed.

(** A fresh eigenvariable stays fresh in the translation. *)
Lemma fresh_one_sided : forall b G C,
  ifresh b (C :: G) -> forall A, In A (itr C :: map (fun A => dual (itr A)) G) -> occurs b A = false.
Proof.
  intros b G C F A [<- | I].
  - rewrite occurs_itr. apply F. now left.
  - apply in_map_iff in I as [B [<- I]]. rewrite occurs_dual, occurs_itr. apply F. now right.
Qed.

(** The first two formulas exchanged. *)
Local Lemma swap : forall R (A B : formula) l, ll R (A :: B :: l) -> ll R (B :: A :: l).
Proof. intros. eapply ex_r; [eassumption | apply perm_swap]. Qed.

(** Every derivation of the two-sided calculus gives one of its
    one-sided translation, without Mix and with the same weakening and
    cut. *)
Theorem ill_ll : forall R G C, ill R G C -> ll (Refutations.lrules R) (one_sided G C).
Proof.
  intros R G C H. unfold one_sided. induction H; cbn in *.
  - apply swap, ax_r.
  - eapply ex_r; [exact IHill |]. apply perm_skip, Permutation_map, H0.
  - apply one_r.
  - apply swap, bot_r, IHill.
  - rewrite map_app. apply tens_r; assumption.
  - apply swap, parr_r.
    eapply ex_r; [exact IHill |].
    apply perm_trans with (dual (itr A) :: itr C :: dual (itr B) :: map (fun A => dual (itr A)) l);
      [apply perm_swap | apply perm_skip, perm_swap].
  - apply parr_r. apply swap. exact IHill.
  - rewrite dual_dual, map_app. apply swap.
    eapply ex_r.
    + apply (tens_r _ (itr A) (dual (itr B)) (map (fun A => dual (itr A)) l1)
               (itr C :: map (fun A => dual (itr A)) l2)); [exact IHill1 | apply swap, IHill2].
    + apply perm_skip. symmetry. apply Permutation_middle.
  - apply top_r.
  - apply with_r; assumption.
  - apply swap, plus_r1, swap, IHill.
  - apply swap, plus_r2, swap, IHill.
  - apply swap, top_r.
  - apply plus_r1. exact IHill.
  - apply plus_r2. exact IHill.
  - apply swap, with_r; apply swap; assumption.
  - rewrite map_map in *. cbn in *.
    replace (map (fun x => wn (dual (itr x))) l) with (map wn (map (fun x => dual (itr x)) l))
      in * by now rewrite map_map.
    apply oc_r, IHill.
  - apply swap, de_r, swap, IHill.
  - apply swap, wk_r, IHill.
  - apply swap, co_r.
    eapply ex_r; [exact IHill |].
    apply perm_trans with (wn (dual (itr A)) :: itr C :: wn (dual (itr A)) :: map (fun A => dual (itr A)) l);
      [apply perm_swap | apply perm_skip, perm_swap].
  - apply swap, weakening_r; [exact H | exact IHill].
  - rewrite map_app. eapply ex_r.
    + refine (cut_r (Refutations.lrules R) _ (itr A) (map (fun A => dual (itr A)) l1)
        (itr C :: map (fun A => dual (itr A)) l2) _ _); [assumption | exact IHill1 |].
      apply swap, IHill2.
    + symmetry. apply Permutation_middle.
  - apply (fall_r _ _ a).
    + exact (fresh_one_sided a l (iall A) H).
    + rewrite <- itr_isubst. exact IHill.
  - apply swap, (fex_r _ _ t); [exact H |]. rewrite <- dual_subst, <- itr_isubst.
    apply swap, IHill.
  - apply (fex_r _ _ t); [exact H |]. rewrite <- itr_isubst. exact IHill.
  - apply swap, (fall_r _ _ a).
    + intros B [<- | [<- | I]].
      * cbn. rewrite occurs_dual, occurs_itr. apply (H (iex A)). now left.
      * rewrite occurs_itr. apply H. right. now left.
      * apply in_map_iff in I as [D [<- I]]. rewrite occurs_dual, occurs_itr.
        apply H. now right; right.
    + rewrite <- dual_subst, <- itr_isubst. apply swap, IHill.
Qed.

End Translation.

(** Weights that the test accepts of the translation refute a two-sided
    first-order sequent. *)
Theorem iweighted_refutation : forall {symbol : Type} fixed table weight R G C,
  overweight (symbol := symbol) fixed table weight (Refutations.lrules R) (one_sided G C) = true ->
  ~ ill R G C.
Proof.
  intros symbol fixed table weight R G C T H.
  exact (weighted_refutation fixed table weight _ _ T (ill_ll R G C H)).
Qed.
