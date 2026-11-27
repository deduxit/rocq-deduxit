(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * Finite structures and the soundness of LK

    A finite structure has the domain [0 … size - 1], a value
    [fn f l < size] for every function symbol and list of arguments, and
    the predicates as boolean functions. [eval η ρ A] computes whether
    the formula [A] is true ([eval_fast] the same, stopping as soon as a
    connective or a quantifier is decided), with [η] giving the eigenvariables' values
    and [ρ] the bound variables', the innermost first: a quantifier
    ranges over the domain, so truth is computed, not assumed decidable.

    [classical_soundness] says that every derivable sequent [Γ ⊢ Δ] of LK
    holds in every finite structure: where all of [Γ] is true, one of [Δ]
    is. [classical_countermodel] turns a structure that makes [Γ] true
    and [Δ] false into a proof that the sequent is underivable, with cut
    or without. *)

From Stdlib Require Import List Permutation Bool Arith Lia.
From Deduxit.Linear Require Import TermsCheck.
From Deduxit.Intuitionistic Require Export FirstOrderCalculus.
From Deduxit.Base Require Lists.
Import ListNotations.

Section Classical.

Context {symbol : Type}.

Variable size : nat.
Variable fn : symbol -> list nat -> nat.
Variable pred : symbol -> list nat -> bool.

(** The value of the term [t]. A bound variable that no quantifier
    binds takes the value [0]. *)
Fixpoint value (eta : nat -> nat) (rho : list nat) (t : term symbol) : nat :=
  match t with
  | bound n => nth n rho 0
  | eigen a => eta a
  | tapp f l => fn f (map (value eta rho) l)
  end.

(** Whether the formula [A] is true. *)
Fixpoint eval (eta : nat -> nat) (rho : list nat) (A : formula symbol) : bool :=
  match A with
  | var p l => pred p (map (value eta rho) l)
  | bot => false
  | wedge A B => eval eta rho A && eval eta rho B
  | vee A B => eval eta rho A || eval eta rho B
  | imp A B => implb (eval eta rho A) (eval eta rho B)
  | fall A => forallb (fun d => eval eta (d :: rho) A) (seq 0 size)
  | fex A => existsb (fun d => eval eta (d :: rho) A) (seq 0 size)
  end.

(** [forallb] that stops at the first member that fails. Under
    [vm_compute] the standard [forallb] and [&&] evaluate every member,
    which a quantifier decided at its first element need not. *)
Fixpoint allb {X} (f : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l => if f x then allb f l else false
  end.

(** [existsb] that stops at the first member that holds. *)
Fixpoint anyb {X} (f : X -> bool) (l : list X) : bool :=
  match l with
  | [] => false
  | x :: l => if f x then true else anyb f l
  end.

(** [allb] is [forallb]. *)
Lemma allb_forallb : forall {X} (f : X -> bool) l, allb f l = forallb f l.
Proof.
  intros X f l. induction l as [| x l IH]; cbn; [reflexivity |].
  rewrite IH. destruct (f x); reflexivity.
Qed.

(** [anyb] is [existsb]. *)
Lemma anyb_existsb : forall {X} (f : X -> bool) l, anyb f l = existsb f l.
Proof.
  intros X f l. induction l as [| x l IH]; cbn; [reflexivity |].
  rewrite IH. destruct (f x); reflexivity.
Qed.

(** [eval], stopping at the first operand or element that decides a
    connective or a quantifier: what a certificate computes. *)
Fixpoint eval_fast (eta : nat -> nat) (rho : list nat) (A : formula symbol) : bool :=
  match A with
  | var p l => pred p (map (value eta rho) l)
  | bot => false
  | wedge A B => if eval_fast eta rho A then eval_fast eta rho B else false
  | vee A B => if eval_fast eta rho A then true else eval_fast eta rho B
  | imp A B => if eval_fast eta rho A then eval_fast eta rho B else true
  | fall A => allb (fun d => eval_fast eta (d :: rho) A) (seq 0 size)
  | fex A => anyb (fun d => eval_fast eta (d :: rho) A) (seq 0 size)
  end.

(** [eta] with the eigenvariable [a] taking the value [d]. *)
Definition cupdate (eta : nat -> nat) (a : nat) (d : nat) : nat -> nat :=
  fun b => if Nat.eqb b a then d else eta b.

(** A closed term has the same value under every [ρ]. *)
Lemma closed_value : forall eta rho rho' t, tclosed t = true -> value eta rho t = value eta rho' t.
Proof.
  intros eta rho rho' t. induction t as [n | a | f l IH] using term_ind'; cbn; intros H.
  - discriminate.
  - reflexivity.
  - f_equal. apply map_ext_in. intros x Hx. rewrite forallb_forall in H.
    rewrite Forall_forall in IH. apply IH; [exact Hx | apply H; exact Hx].
Qed.

(** Substituting a closed term for the bound variable [k] is putting its
    value at place [k] of [ρ]. *)
Lemma value_tsubst : forall eta t s k rho, tclosed t = true -> length rho = k ->
  value eta (rho ++ [value eta [] t]) s = value eta rho (tsubst k t s).
Proof.
  intros eta t s k rho Ht Hk. induction s as [n | a | f l IH] using term_ind'; cbn.
  - destruct (Nat.eqb_spec n k) as [E | E].
    + subst n. rewrite app_nth2 by lia. rewrite Hk, Nat.sub_diag. cbn.
      apply closed_value. exact Ht.
    + cbn. destruct (Nat.lt_ge_cases n k) as [Hl | Hl].
      * rewrite app_nth1 by lia. reflexivity.
      * rewrite app_nth2 by lia. rewrite (nth_overflow rho) by lia.
        destruct (n - length rho) as [| m] eqn:Em; [lia |]. cbn. destruct m; reflexivity.
  - reflexivity.
  - f_equal. rewrite map_map. apply map_ext_in. intros x Hx.
    rewrite Forall_forall in IH. apply IH. exact Hx.
Qed.

(** [forallb] of functions that agree on the list. *)
Lemma forallb_ext_in : forall {X} (f g : X -> bool) l, (forall x, In x l -> f x = g x) ->
  forallb f l = forallb g l.
Proof.
  intros X f g l H. induction l as [| x l IH]; cbn; [reflexivity |].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity |]. intros y Hy. apply H. right. exact Hy.
Qed.

(** [existsb] of functions that agree on the list. *)
Lemma existsb_ext_in : forall {X} (f g : X -> bool) l, (forall x, In x l -> f x = g x) ->
  existsb f l = existsb g l.
Proof.
  intros X f g l H. induction l as [| x l IH]; cbn; [reflexivity |].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity |]. intros y Hy. apply H. right. exact Hy.
Qed.

(** [eval_fast] computes [eval]. *)
Lemma eval_fast_eval : forall A eta rho, eval_fast eta rho A = eval eta rho A.
Proof.
  intros A; induction A as [p l | | A IHA B IHB | A IHA B IHB | A IHA B IHB | A IHA | A IHA];
    intros eta rho; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHA, IHB. destruct (eval eta rho A); reflexivity.
  - rewrite IHA, IHB. destruct (eval eta rho A); reflexivity.
  - rewrite IHA, IHB. destruct (eval eta rho A); reflexivity.
  - rewrite allb_forallb. apply forallb_ext_in. intros d _. apply IHA.
  - rewrite anyb_existsb. apply existsb_ext_in. intros d _. apply IHA.
Qed.

(** [allb] and [anyb] of [eval_fast] over a list of formulas are
    [forallb] and [existsb] of [eval]. *)
Lemma allb_eval : forall eta rho l, allb (eval_fast eta rho) l = forallb (eval eta rho) l.
Proof.
  intros eta rho l. rewrite allb_forallb. apply forallb_ext_in. intros A _. apply eval_fast_eval.
Qed.

Lemma anyb_eval : forall eta rho l, anyb (eval_fast eta rho) l = existsb (eval eta rho) l.
Proof.
  intros eta rho l. rewrite anyb_existsb. apply existsb_ext_in. intros A _. apply eval_fast_eval.
Qed.

(** The truth of an instance at a closed term is the truth of the body
    at the term's value. *)
Lemma eval_subst : forall t, tclosed t = true -> forall A k rho eta, length rho = k ->
  eval eta (rho ++ [value eta [] t]) A = eval eta rho (subst k t A).
Proof.
  intros t Ht A. induction A as [p l | | A IHA B IHB | A IHA B IHB | A IHA B IHB | A IHA | A IHA];
    intros k rho eta Hk; cbn.
  - f_equal. rewrite map_map. apply map_ext_in. intros s _. apply value_tsubst; assumption.
  - reflexivity.
  - rewrite (IHA k rho eta Hk), (IHB k rho eta Hk). reflexivity.
  - rewrite (IHA k rho eta Hk), (IHB k rho eta Hk). reflexivity.
  - rewrite (IHA k rho eta Hk), (IHB k rho eta Hk). reflexivity.
  - apply forallb_ext_in. intros d _. apply (IHA (S k) (d :: rho) eta). cbn. rewrite Hk. reflexivity.
  - apply existsb_ext_in. intros d _. apply (IHA (S k) (d :: rho) eta). cbn. rewrite Hk. reflexivity.
Qed.

(** An existential list fails on each member. *)
Lemma existsb_false_in : forall {X} (f : X -> bool) l x, existsb f l = false -> In x l -> f x = false.
Proof. exact @Lists.existsb_false. Qed.

(** The value of an eigenvariable that does not occur in [t] does not
    matter. *)
Lemma value_update : forall eta a d rho t, toccurs a t = false ->
  value (cupdate eta a d) rho t = value eta rho t.
Proof.
  intros eta a d rho t. induction t as [n | b | f l IH] using term_ind'; cbn; intros H.
  - reflexivity.
  - unfold cupdate. rewrite Nat.eqb_sym, H. reflexivity.
  - f_equal. apply map_ext_in. intros x Hx. rewrite Forall_forall in IH.
    apply IH; [exact Hx | exact (existsb_false_in _ _ _ H Hx)].
Qed.

(** The value of an eigenvariable that does not occur in [A] does not
    matter. *)
Lemma eval_update : forall a d A eta rho, occurs a A = false ->
  eval (cupdate eta a d) rho A = eval eta rho A.
Proof.
  intros a d A. induction A as [p l | | A IHA B IHB | A IHA B IHB | A IHA B IHB | A IHA | A IHA];
    intros eta rho H; cbn in *.
  - f_equal. apply map_ext_in. intros t Ht. exact (value_update _ _ _ _ _ (existsb_false_in _ _ _ H Ht)).
  - reflexivity.
  - apply orb_false_iff in H as [HA HB]. rewrite IHA, IHB by assumption. reflexivity.
  - apply orb_false_iff in H as [HA HB]. rewrite IHA, IHB by assumption. reflexivity.
  - apply orb_false_iff in H as [HA HB]. rewrite IHA, IHB by assumption. reflexivity.
  - apply forallb_ext_in. intros e _. apply IHA. exact H.
  - apply existsb_ext_in. intros e _. apply IHA. exact H.
Qed.

(** [forallb] and [existsb] of formulas in which [a] does not occur do
    not depend on its value. *)
Lemma eval_update_all : forall a d l eta, (forall A, In A l -> occurs a A = false) ->
  forallb (eval (cupdate eta a d) []) l = forallb (eval eta []) l
  /\ existsb (eval (cupdate eta a d) []) l = existsb (eval eta []) l.
Proof.
  intros a d l eta H. split; [apply forallb_ext_in | apply existsb_ext_in];
    intros A HA; apply eval_update; exact (H A HA).
Qed.

(** [forallb] and [existsb] read a list as a set. *)
Lemma forallb_perm : forall {X} (f : X -> bool) l1 l2, Permutation l1 l2 -> forallb f l1 = forallb f l2.
Proof. exact @Lists.forallb_perm. Qed.

(** [existsb] reads a list as a set. *)
Lemma existsb_perm : forall {X} (f : X -> bool) l1 l2, Permutation l1 l2 -> existsb f l1 = existsb f l2.
Proof. exact @Lists.existsb_perm. Qed.

Hypothesis size_pos : 0 < size.
Hypothesis fn_closed : forall f l, fn f l < size.

(** Over elements of the domain, a term's value is in the domain. *)
Lemma value_dom : forall eta t, (forall a, eta a < size) -> value eta [] t < size.
Proof.
  intros eta [n | a | f l] He; cbn.
  - destruct n; exact size_pos.
  - apply He.
  - apply fn_closed.
Qed.

(** An element of the domain is in [seq 0 size]. *)
Lemma in_domain : forall d, d < size -> In d (seq 0 size).
Proof. intros d H. apply in_seq. lia. Qed.

(** Every derivable sequent holds under every value of the
    eigenvariables in the domain: where all of [Γ] is true, one of [Δ]
    is. *)
Theorem classical_soundness : forall c G Dl, lk c G Dl ->
  forall eta, (forall a, eta a < size) ->
  forallb (eval eta []) G = true -> existsb (eval eta []) Dl = true.
Proof.
  intros c G Dl P. induction P as [A | l1 l2 d P IHP Hp | l d1 d2 P IHP Hp | A l d P IHP
    | A l d P IHP | A l d P IHP | A l d P IHP | | A B l d P1 IHP1 P2 IHP2 | A B l d P IHP
    | A B l d P IHP | A B l d P1 IHP1 P2 IHP2 | A B l d P IHP | A B l d P1 IHP1 P2 IHP2
    | Hc A l d P1 IHP1 P2 IHP2 | A a l d Hf P IHP | A t l d Ht P IHP | A t l d Ht P IHP
    | A a l d Hf P IHP]; intros eta He HG; cbn in *.
  - rewrite andb_true_r in HG. rewrite HG. reflexivity.
  - apply IHP; [exact He |]. rewrite (forallb_perm _ _ _ Hp). exact HG.
  - rewrite <- (existsb_perm _ _ _ Hp). exact (IHP eta He HG).
  - apply andb_true_iff in HG as [_ HG]. exact (IHP eta He HG).
  - rewrite (IHP eta He HG). apply orb_true_r.
  - apply andb_true_iff in HG as [HA HG]. apply IHP; [exact He |]. cbn. rewrite HA, HG. reflexivity.
  - specialize (IHP eta He HG). cbn in IHP. destruct (eval eta [] A); [reflexivity | exact IHP].
  - discriminate.
  - specialize (IHP1 eta He HG). specialize (IHP2 eta He HG). cbn in IHP1, IHP2.
    destruct (eval eta [] A), (eval eta [] B); cbn in *; auto.
  - apply andb_true_iff in HG as [HAB HG]. apply andb_true_iff in HAB as [HA HB].
    apply IHP; [exact He |]. cbn. rewrite HA, HB, HG. reflexivity.
  - specialize (IHP eta He HG). cbn in IHP. rewrite orb_assoc in IHP. exact IHP.
  - apply andb_true_iff in HG as [HAB HG]. apply orb_true_iff in HAB as [HA | HB].
    + apply IHP1; [exact He |]. cbn. rewrite HA, HG. reflexivity.
    + apply IHP2; [exact He |]. cbn. rewrite HB, HG. reflexivity.
  - destruct (eval eta [] A) eqn:HA; cbn; [| reflexivity].
    apply IHP; [exact He |]. cbn. rewrite HA, HG. reflexivity.
  - apply andb_true_iff in HG as [Himp HG]. specialize (IHP1 eta He HG). cbn in IHP1.
    destruct (eval eta [] A) eqn:HA; cbn in *.
    + apply IHP2; [exact He |]. cbn. rewrite Himp, HG. reflexivity.
    + exact IHP1.
  - specialize (IHP1 eta He HG). cbn in IHP1. destruct (eval eta [] A) eqn:HA; cbn in IHP1.
    + apply IHP2; [exact He |]. cbn. rewrite HA, HG. reflexivity.
    + exact IHP1.
  - destruct (existsb (eval eta []) d) eqn:Hd; [apply orb_true_r |]. rewrite orb_false_r.
    apply forallb_forall. intros e Hin. apply in_seq in Hin.
    assert (HA : occurs a A = false) by exact (Hf (fall A) (or_introl eq_refl)).
    assert (Hl : forall x, In x l -> occurs a x = false)
      by (intros x Hx; apply Hf; right; apply in_or_app; left; exact Hx).
    assert (Hdl : forall x, In x d -> occurs a x = false)
      by (intros x Hx; apply Hf; right; apply in_or_app; right; exact Hx).
    assert (He' : forall b, cupdate eta a e b < size)
      by (intros b; unfold cupdate; destruct (Nat.eqb b a); [lia | apply He]).
    pose proof (IHP (cupdate eta a e) He') as H. cbn in H.
    rewrite (proj1 (eval_update_all a e l eta Hl)), (proj2 (eval_update_all a e d eta Hdl)), Hd in H.
    rewrite orb_false_r in H. specialize (H HG).
    rewrite <- (eval_subst (eigen a) eq_refl A 0 [] (cupdate eta a e) eq_refl) in H.
    cbn in H. unfold cupdate in H at 2. rewrite Nat.eqb_refl in H.
    rewrite eval_update in H by exact HA. exact H.
  - apply andb_true_iff in HG as [Hall HG]. apply IHP; [exact He |]. cbn. rewrite HG, andb_true_r.
    rewrite <- (eval_subst t Ht A 0 [] eta eq_refl). rewrite forallb_forall in Hall.
    apply Hall. apply in_domain. apply value_dom. exact He.
  - specialize (IHP eta He HG). cbn in IHP. apply orb_true_iff in IHP as [HA | Hd].
    + apply orb_true_iff. left. apply existsb_exists. exists (value eta [] t).
      split; [apply in_domain; apply value_dom; exact He |].
      pose proof (eval_subst t Ht A 0 [] eta eq_refl) as E. cbn in E. rewrite E. exact HA.
    + rewrite Hd. apply orb_true_r.
  - apply andb_true_iff in HG as [Hex HG]. apply existsb_exists in Hex as [e [Hin HA]].
    apply in_seq in Hin.
    assert (HAf : occurs a A = false) by exact (Hf (fex A) (or_introl eq_refl)).
    assert (Hl : forall x, In x l -> occurs a x = false)
      by (intros x Hx; apply Hf; right; apply in_or_app; left; exact Hx).
    assert (Hdl : forall x, In x d -> occurs a x = false)
      by (intros x Hx; apply Hf; right; apply in_or_app; right; exact Hx).
    assert (He' : forall b, cupdate eta a e b < size)
      by (intros b; unfold cupdate; destruct (Nat.eqb b a); [lia | apply He]).
    rewrite <- (proj2 (eval_update_all a e d eta Hdl)). apply IHP; [exact He' |]. cbn.
    rewrite (proj1 (eval_update_all a e l eta Hl)), HG, andb_true_r.
    rewrite <- (eval_subst (eigen a) eq_refl A 0 [] (cupdate eta a e) eq_refl). cbn.
    unfold cupdate at 2. rewrite Nat.eqb_refl. rewrite eval_update by exact HAf. exact HA.
Qed.

(** A structure that makes every formula of [Γ] true and every formula
    of [Δ] false shows [Γ ⊢ Δ] underivable in LK. The eigenvariables take
    the value [0]. *)
Theorem classical_countermodel : forall c G Dl,
  forallb (eval (fun _ => 0) []) G && negb (existsb (eval (fun _ => 0) []) Dl) = true -> ~ lk c G Dl.
Proof.
  intros c G Dl H P. apply andb_true_iff in H as [HG HD].
  rewrite (classical_soundness c G Dl P (fun _ => 0) (fun _ => size_pos) HG) in HD. discriminate.
Qed.

End Classical.
