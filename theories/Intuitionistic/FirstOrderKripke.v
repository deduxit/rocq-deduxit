(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * First-order Kripke models with growing domains, and their soundness

    A first-order Kripke model (Troelstra and van Dalen, _Constructivism
    in Mathematics_, §2.5) has worlds with a preorder [le], read "later
    than or equal to", and at each world a domain, the elements of a
    type [element] for which [dom w] holds. Domains grow along [le]:
    every element of a world is an element of every later world. Each
    world interprets the function symbols ([fn]) and the predicates
    ([pred]); a later world keeps the values of the functions on the
    earlier world's elements, and the predicates' true tuples. The worlds
    in [absurd] force [⊥]: none in intuitionistic logic, any set closed
    upwards in minimal logic, where [⊥] is one more atom.

    [forces w η ρ A] says that the world [w] forces [A], with [η] giving
    the eigenvariables' values and [ρ] the bound variables', the
    innermost first. [∀x. A] is forced at [w] when every later world
    forces [A] of each of its own elements; [∃x. A] when [w] forces [A]
    of one of its elements.

    [kripke_soundness] says that every derivable sequent of LJ or LM
    holds in every model of its logic; [kripke_countermodel] turns a
    world that forces the hypotheses and not the conclusion into a proof
    that the sequent is underivable, with cut or without. The section
    [Chain] is the model with a world for each natural number, which no
    finite model replaces: it refutes [¬¬∀x. (p(x) ∨ ¬p(x))] and the
    double-negation shift [(∀x. ¬¬p(x)) → ¬¬(∀x. p(x))]. *)

From Stdlib Require Import List Permutation Bool Arith Lia.
From Deduxit.Linear Require Import TermsCheck.
From Deduxit.Intuitionistic Require Calculus.
From Deduxit.Intuitionistic Require Export FirstOrderCalculus.
From Deduxit.Base Require Lists.
Import ListNotations.

Section Kripke.

Context {symbol : Type}.

Variable world : Type.
Variable le : world -> world -> Prop.
Variable element : Type.
Variable d0 : element.
Variable dom : world -> element -> Prop.
Variable fn : world -> symbol -> list element -> element.
Variable pred : world -> symbol -> list element -> Prop.
Variable absurd : world -> Prop.

(** The data make a Kripke model of the logic of [R]. [d0] is an element
    of every domain: it is the value of a bound variable that no
    quantifier binds, and it makes every domain inhabited, as first-order
    logic asks. *)
Record model (R : Calculus.rules) : Prop := {
  model_refl : forall w, le w w;
  model_trans : forall u v w, le u v -> le v w -> le u w;
  model_dom : forall w v d, le w v -> dom w d -> dom v d;
  model_default : forall w, dom w d0;
  model_closed : forall w f l, Forall (dom w) l -> dom w (fn w f l);
  model_agree : forall w v f l, le w v -> Forall (dom w) l -> fn v f l = fn w f l;
  model_pred : forall w v p l, le w v -> pred w p l -> pred v p l;
  model_absurd : forall w v, le w v -> absurd w -> absurd v;
  model_explosion : Calculus.explosion R = true -> forall w, ~ absurd w;
}.

(** The value of the term [t] at the world [w]. *)
Fixpoint teval (w : world) (eta : nat -> element) (rho : list element) (t : term symbol) : element :=
  match t with
  | bound n => nth n rho d0
  | eigen a => eta a
  | tapp f l => fn w f (map (teval w eta rho) l)
  end.

(** The world [w] forces the formula [A]. *)
Fixpoint forces (w : world) (eta : nat -> element) (rho : list element) (A : formula symbol) : Prop :=
  match A with
  | var p l => pred w p (map (teval w eta rho) l)
  | bot => absurd w
  | wedge A B => forces w eta rho A /\ forces w eta rho B
  | vee A B => forces w eta rho A \/ forces w eta rho B
  | imp A B => forall v, le w v -> forces v eta rho A -> forces v eta rho B
  | fall A => forall v, le w v -> forall d, dom v d -> forces v eta (d :: rho) A
  | fex A => exists d, dom w d /\ forces w eta (d :: rho) A
  end.

(** [eta] with the eigenvariable [a] taking the value [d]. *)
Definition update (eta : nat -> element) (a : nat) (d : element) : nat -> element :=
  fun b => if Nat.eqb b a then d else eta b.

(** An updated eigenvariable has its new value. *)
Lemma teval_update_eigen : forall w eta a d rho, teval w (update eta a d) rho (eigen a) = d.
Proof.
  intros w eta a d rho. cbn. unfold update. rewrite Nat.eqb_refl. reflexivity.
Qed.

(** A closed term has the same value under every [ρ]. *)
Lemma closed_teval : forall w eta rho rho' t, tclosed t = true ->
  teval w eta rho t = teval w eta rho' t.
Proof.
  intros w eta rho rho' t. induction t as [n | a | f l IH] using term_ind'; cbn; intros H.
  - discriminate.
  - reflexivity.
  - f_equal. apply map_ext_in. intros x Hx. rewrite forallb_forall in H.
    rewrite Forall_forall in IH. apply IH; [exact Hx | apply H; exact Hx].
Qed.

(** Substituting a closed term for the bound variable [k] is putting its
    value at place [k] of [ρ]. A bound variable past [k] has no value in
    either, and both give [d0]. *)
Lemma teval_tsubst : forall w eta t s k rho, tclosed t = true -> length rho = k ->
  teval w eta (rho ++ [teval w eta [] t]) s = teval w eta rho (tsubst k t s).
Proof.
  intros w eta t s k rho Ht Hk. induction s as [n | a | f l IH] using term_ind'; cbn.
  - destruct (Nat.eqb_spec n k) as [E | E].
    + subst n. rewrite app_nth2 by lia. rewrite Hk, Nat.sub_diag. cbn.
      apply closed_teval. exact Ht.
    + cbn. destruct (Nat.lt_ge_cases n k) as [Hl | Hl].
      * rewrite app_nth1 by lia. reflexivity.
      * rewrite app_nth2 by lia. rewrite (nth_overflow rho) by lia.
        destruct (n - length rho) as [| m] eqn:Em; [lia |]. cbn. destruct m; reflexivity.
  - reflexivity.
  - f_equal. rewrite map_map. apply map_ext_in. intros x Hx.
    rewrite Forall_forall in IH. apply IH. exact Hx.
Qed.

(** An existential list fails on each member. *)
Lemma existsb_false : forall {X} (f : X -> bool) l x, existsb f l = false -> In x l -> f x = false.
Proof. exact @Lists.existsb_false. Qed.

(** The value of an eigenvariable that does not occur in [t] does not
    matter. *)
Lemma teval_update : forall w eta a d rho t, toccurs a t = false ->
  teval w (update eta a d) rho t = teval w eta rho t.
Proof.
  intros w eta a d rho t. induction t as [n | b | f l IH] using term_ind'; cbn; intros H.
  - reflexivity.
  - unfold update. rewrite Nat.eqb_sym, H. reflexivity.
  - f_equal. apply map_ext_in. intros x Hx. rewrite Forall_forall in IH.
    apply IH; [exact Hx | exact (existsb_false _ _ _ H Hx)].
Qed.

(** The value of an eigenvariable that does not occur in [A] does not
    matter. *)
Lemma forces_update : forall a d A w eta rho, occurs a A = false ->
  forces w (update eta a d) rho A <-> forces w eta rho A.
Proof.
  intros a d A. induction A as [p l | | A IHA B IHB | A IHA B IHB | A IHA B IHB | A IHA | A IHA];
    intros w eta rho H; cbn in *.
  - replace (map (teval w (update eta a d) rho) l) with (map (teval w eta rho) l); [reflexivity |].
    apply map_ext_in. intros t Ht. symmetry. exact (teval_update _ _ _ _ _ _ (existsb_false _ _ _ H Ht)).
  - reflexivity.
  - apply orb_false_iff in H as [HA HB]. rewrite (IHA w eta rho HA), (IHB w eta rho HB). reflexivity.
  - apply orb_false_iff in H as [HA HB]. rewrite (IHA w eta rho HA), (IHB w eta rho HB). reflexivity.
  - apply orb_false_iff in H as [HA HB]. split.
    + intros Hi v Hle Hv. apply (proj1 (IHB v eta rho HB)). apply (Hi v Hle).
      apply (proj2 (IHA v eta rho HA)). exact Hv.
    + intros Hi v Hle Hv. apply (proj2 (IHB v eta rho HB)). apply (Hi v Hle).
      apply (proj1 (IHA v eta rho HA)). exact Hv.
  - split.
    + intros Hi v Hle e He. apply (proj1 (IHA v eta (e :: rho) H)). exact (Hi v Hle e He).
    + intros Hi v Hle e He. apply (proj2 (IHA v eta (e :: rho) H)). exact (Hi v Hle e He).
  - split.
    + intros [e [He HA]]. exists e. split; [exact He |]. exact (proj1 (IHA w eta (e :: rho) H) HA).
    + intros [e [He HA]]. exists e. split; [exact He |]. exact (proj2 (IHA w eta (e :: rho) H) HA).
Qed.

Variable R : Calculus.rules.
Hypothesis M : model R.

(** A place of [ρ], or [d0] past its end, is an element of a domain
    that holds [ρ]. *)
Lemma nth_dom : forall w rho n, Forall (dom w) rho -> dom w (nth n rho d0).
Proof.
  intros w rho n H. destruct (Nat.lt_ge_cases n (length rho)) as [Hn | Hn].
  - rewrite Forall_forall in H. apply H. apply nth_In. exact Hn.
  - rewrite nth_overflow by exact Hn. apply (model_default _ M).
Qed.

(** Over elements of [w], a term's value is an element of [w], and
    every later world gives it the same value. *)
Lemma teval_persist : forall w v eta rho t, le w v -> (forall a, dom w (eta a)) ->
  Forall (dom w) rho -> dom w (teval w eta rho t) /\ teval v eta rho t = teval w eta rho t.
Proof.
  intros w v eta rho t Hle He Hr. induction t as [n | a | f l IH] using term_ind'; cbn.
  - split; [apply nth_dom; exact Hr | reflexivity].
  - split; [apply He | reflexivity].
  - rewrite Forall_forall in IH.
    assert (Hl : map (teval v eta rho) l = map (teval w eta rho) l).
    { apply map_ext_in. intros x Hx. exact (proj2 (IH x Hx)). }
    assert (Hd : Forall (dom w) (map (teval w eta rho) l)).
    { apply Forall_forall. intros y Hy. apply in_map_iff in Hy as [x [<- Hx]]. exact (proj1 (IH x Hx)). }
    rewrite Hl. split; [exact (model_closed _ M _ _ _ Hd) | exact (model_agree _ M _ _ _ _ Hle Hd)].
Qed.

(** What a world forces of its elements, every later world forces. *)
Lemma persistence : forall A w v eta rho, le w v -> (forall a, dom w (eta a)) ->
  Forall (dom w) rho -> forces w eta rho A -> forces v eta rho A.
Proof.
  induction A as [p l | | A IHA B IHB | A IHA B IHB | A IHA B IHB | A IHA | A IHA];
    intros w v eta rho Hle He Hr H; cbn in *.
  - replace (map (teval v eta rho) l) with (map (teval w eta rho) l).
    + exact (model_pred _ M _ _ _ _ Hle H).
    + apply map_ext_in. intros t _. symmetry. exact (proj2 (teval_persist w v eta rho t Hle He Hr)).
  - exact (model_absurd _ M _ _ Hle H).
  - destruct H as [HA HB]. split; [exact (IHA _ _ _ _ Hle He Hr HA) | exact (IHB _ _ _ _ Hle He Hr HB)].
  - destruct H as [HA | HB];
      [left; exact (IHA _ _ _ _ Hle He Hr HA) | right; exact (IHB _ _ _ _ Hle He Hr HB)].
  - intros u Hvu HA. exact (H u (model_trans _ M _ _ _ Hle Hvu) HA).
  - intros u Hvu d Hd. exact (H u (model_trans _ M _ _ _ Hle Hvu) d Hd).
  - destruct H as [d [Hd HA]]. exists d. split; [exact (model_dom _ M _ _ _ Hle Hd) |].
    apply (IHA w v eta (d :: rho) Hle He); [constructor; assumption | exact HA].
Qed.

(** Forcing an instance is forcing the body with the term's value at
    the bound variable's place, where every later world gives the term
    the same value [e]. *)
Lemma forces_subst : forall t, tclosed t = true -> forall A k rho w eta e, length rho = k ->
  (forall v, le w v -> teval v eta [] t = e) ->
  (forces w eta (rho ++ [e]) A <-> forces w eta rho (subst k t A)).
Proof.
  intros t Ht A. induction A as [p l | | A IHA B IHB | A IHA B IHB | A IHA B IHB | A IHA | A IHA];
    intros k rho w eta e Hk He; cbn.
  - rewrite map_map.
    replace (map (teval w eta (rho ++ [e])) l) with (map (fun s => teval w eta rho (tsubst k t s)) l);
      [reflexivity |].
    apply map_ext_in. intros s _. rewrite <- (He w (model_refl _ M w)).
    symmetry. apply teval_tsubst; assumption.
  - reflexivity.
  - rewrite (IHA k rho w eta e Hk He), (IHB k rho w eta e Hk He). reflexivity.
  - rewrite (IHA k rho w eta e Hk He), (IHB k rho w eta e Hk He). reflexivity.
  - split; intros Hi v Hle HA;
      assert (Hv : forall u, le v u -> teval u eta [] t = e)
        by (intros u Hu; apply He; exact (model_trans _ M _ _ _ Hle Hu)).
    + apply (proj1 (IHB k rho v eta e Hk Hv)). apply (Hi v Hle).
      exact (proj2 (IHA k rho v eta e Hk Hv) HA).
    + apply (proj2 (IHB k rho v eta e Hk Hv)). apply (Hi v Hle).
      exact (proj1 (IHA k rho v eta e Hk Hv) HA).
  - split; intros Hi v Hle d Hd;
      assert (Hv : forall u, le v u -> teval u eta [] t = e)
        by (intros u Hu; apply He; exact (model_trans _ M _ _ _ Hle Hu)).
    + exact (proj1 (IHA (S k) (d :: rho) v eta e (f_equal S Hk) Hv) (Hi v Hle d Hd)).
    + exact (proj2 (IHA (S k) (d :: rho) v eta e (f_equal S Hk) Hv) (Hi v Hle d Hd)).
  - split; intros [d [Hd HA]]; exists d; split; try exact Hd.
    + exact (proj1 (IHA (S k) (d :: rho) w eta e (f_equal S Hk) He) HA).
    + exact (proj2 (IHA (S k) (d :: rho) w eta e (f_equal S Hk) He) HA).
Qed.

(** A world forces the instance of [A] at a closed term exactly when it
    forces [A] of the term's value. *)
Lemma forces_instance : forall t A w eta, tclosed t = true -> (forall a, dom w (eta a)) ->
  (forces w eta [teval w eta [] t] A <-> forces w eta [] (subst 0 t A)).
Proof.
  intros t A w eta Ht He. apply (forces_subst t Ht A 0 [] w eta); [reflexivity |].
  intros v Hle. exact (proj2 (teval_persist w v eta [] t Hle He (Forall_nil _))).
Qed.

(** The formulas of [l] in which [a] does not occur are forced alike
    whatever value [a] takes. *)
Lemma forces_update_all : forall a d l w eta, (forall A, In A l -> occurs a A = false) ->
  Forall (forces w eta []) l -> Forall (forces w (update eta a d) []) l.
Proof.
  intros a d l w eta Hf H. apply Forall_forall. intros A HA.
  apply (forces_update a d A w eta [] (Hf A HA)). rewrite Forall_forall in H. exact (H A HA).
Qed.

(** Every derivable sequent holds at every world, under every value of
    the eigenvariables in that world's domain. *)
Theorem kripke_soundness : forall G C, lj R G C ->
  forall w eta, (forall a, dom w (eta a)) -> Forall (forces w eta []) G -> forces w eta [] C.
Proof.
  intros G C P. induction P as [A | l1 l2 C P IHP Hp | A l C P IHP | A l C P IHP
    | Hexp C | A B l P1 IHP1 P2 IHP2 | A B l C P IHP | A B l P IHP | A B l P IHP
    | A B l C P1 IHP1 P2 IHP2 | A B l P IHP | A B l C P1 IHP1 P2 IHP2
    | Hcut A l C P1 IHP1 P2 IHP2 | A a l Hf P IHP | A t l C Ht P IHP | A t l Ht P IHP
    | A a l C Hf P IHP]; intros w eta He HG.
  - apply Forall_cons_iff in HG as [HA _]. exact HA.
  - apply IHP; [exact He |]. apply Forall_forall. intros x Hx.
    eapply Forall_forall; [exact HG |]. apply Permutation_in with l1; assumption.
  - apply Forall_cons_iff in HG as [_ Hl]. exact (IHP w eta He Hl).
  - apply Forall_cons_iff in HG as [HA Hl]. apply IHP; [exact He |]. repeat constructor; assumption.
  - apply Forall_cons_iff in HG as [Hbot _]. cbn in Hbot.
    exfalso. exact (model_explosion _ M Hexp w Hbot).
  - split; [exact (IHP1 w eta He HG) | exact (IHP2 w eta He HG)].
  - apply Forall_cons_iff in HG as [[HA HB] Hl]. apply IHP; [exact He |]. repeat constructor; assumption.
  - left. exact (IHP w eta He HG).
  - right. exact (IHP w eta He HG).
  - apply Forall_cons_iff in HG as [[HA | HB] Hl].
    + apply IHP1; [exact He |]. constructor; assumption.
    + apply IHP2; [exact He |]. constructor; assumption.
  - intros v Hle HA. apply IHP; [intros a; exact (model_dom _ M _ _ _ Hle (He a)) |].
    constructor; [exact HA |]. eapply Forall_impl; [| exact HG].
    intros x Hx. exact (persistence x w v eta [] Hle He (Forall_nil _) Hx).
  - apply Forall_cons_iff in HG as [Himp Hl]. apply IHP2; [exact He |]. constructor; [| exact Hl].
    exact (Himp w (model_refl _ M w) (IHP1 w eta He Hl)).
  - apply IHP2; [exact He |]. constructor; [exact (IHP1 w eta He HG) | exact HG].
  - intros v Hle d Hd.
    assert (HA : occurs a A = false) by exact (Hf (fall A) (or_introl eq_refl)).
    assert (He' : forall b, dom v (update eta a d b)).
    { intros b. unfold update. destruct (Nat.eqb b a); [exact Hd | exact (model_dom _ M _ _ _ Hle (He b))]. }
    apply (forces_update a d A v eta [d] HA).
    assert (Hl : Forall (forces v (update eta a d) []) l).
    { apply forces_update_all; [intros x Hx; exact (Hf x (or_intror Hx)) |].
      eapply Forall_impl; [| exact HG].
      intros x Hx. exact (persistence x w v eta [] Hle He (Forall_nil _) Hx). }
    pose proof (proj2 (forces_instance (eigen a) A v (update eta a d) eq_refl He')
                  (IHP v (update eta a d) He' Hl)) as Hi.
    rewrite teval_update_eigen in Hi. exact Hi.
  - apply Forall_cons_iff in HG as [Hall Hl]. apply IHP; [exact He |]. constructor; [| exact Hl].
    apply (forces_instance t A w eta Ht He). apply Hall; [apply (model_refl _ M) |].
    exact (proj1 (teval_persist w w eta [] t (model_refl _ M w) He (Forall_nil _))).
  - exists (teval w eta [] t).
    split; [exact (proj1 (teval_persist w w eta [] t (model_refl _ M w) He (Forall_nil _))) |].
    apply (forces_instance t A w eta Ht He). exact (IHP w eta He HG).
  - apply Forall_cons_iff in HG as [[d [Hd HA]] Hl].
    assert (HAf : occurs a A = false) by exact (Hf (fex A) (or_introl eq_refl)).
    assert (HC : occurs a C = false) by exact (Hf C (or_intror (or_introl eq_refl))).
    assert (He' : forall b, dom w (update eta a d b)).
    { intros b. unfold update. destruct (Nat.eqb b a); [exact Hd | exact (He b)]. }
    apply (forces_update a d C w eta [] HC). apply IHP; [exact He' |]. constructor.
    + apply (forces_instance (eigen a) A w (update eta a d) eq_refl He').
      rewrite teval_update_eigen. apply (forces_update a d A w eta [d] HAf). exact HA.
    + apply forces_update_all; [intros x Hx; exact (Hf x (or_intror (or_intror Hx))) | exact Hl].
Qed.

(** A world that forces the hypotheses and not the conclusion shows the
    sequent underivable. The eigenvariables take the value [d0]. *)
Theorem kripke_countermodel : forall G C w,
  Forall (forces w (fun _ => d0) []) G -> ~ forces w (fun _ => d0) [] C -> ~ lj R G C.
Proof.
  intros G C w HG HC P. apply HC.
  apply (kripke_soundness G C P w); [intros a; apply (model_default _ M) | exact HG].
Qed.

End Kripke.

Arguments model {symbol} world le element d0 dom fn pred absurd R.
Arguments teval {symbol world element} d0 fn w eta rho t.
Arguments forces {symbol world} le {element} d0 dom fn pred absurd w eta rho A.

(** ** The infinite chain

    The worlds are the natural numbers in their order, the domain of the
    world [n] is [0 … n], and every unary predicate holds of [k] from the
    world [k + 1] on. Each world has an element, its own number, of which
    the predicate does not hold yet but will. So no world forces
    [∀x. (p(x) ∨ ¬p(x))] or [∀x. p(x)], and every world forces
    [∀x. ¬¬p(x)].

    No finite model refutes these formulas in intuitionistic logic: each
    world of a finite model sees a last one, which forces every formula
    that classical logic proves, so it forces the formula under [¬¬]. *)

Section Chain.

Context {symbol : Type}.

(** The domain of the world [n]: [0 … n]. *)
Definition chain_dom (n d : nat) : Prop := d <= n.

(** No function symbol matters; each takes the value [0]. *)
Definition chain_fn (n : nat) (f : symbol) (l : list nat) : nat := 0.

(** A unary predicate holds of [k] at the worlds after [k]. *)
Definition chain_pred (n : nat) (p : symbol) (l : list nat) : Prop :=
  match l with
  | [k] => k < n
  | _ => False
  end.

(** No world forces [⊥]. *)
Definition chain_absurd (n : nat) : Prop := False.

(** The chain is a Kripke model of every logic. *)
Lemma chain_model : forall R, model nat le nat 0 chain_dom chain_fn chain_pred chain_absurd R.
Proof.
  intros R. unfold chain_dom, chain_fn, chain_pred, chain_absurd. split.
  - intros w. lia.
  - intros u v w. lia.
  - intros w v d. lia.
  - intros w. lia.
  - intros w f l _. lia.
  - reflexivity.
  - intros w v p [| k [| j l]] Hle H; try contradiction. lia.
  - intros w v _ [].
  - intros _ w [].
Qed.

(** The chain refutes [⊢ ¬¬∀x. (p(x) ∨ ¬p(x))], in LJ and LM, with cut
    or without. *)
Theorem chain_excluded_middle : forall R (p : symbol),
  ~ lj R [] (neg (neg (fall (vee (var p [bound 0]) (neg (var p [bound 0])))))).
Proof.
  intros R p.
  apply (kripke_countermodel nat le nat 0 chain_dom chain_fn chain_pred chain_absurd R (chain_model R) [] _ 0).
  - constructor.
  - unfold neg. cbn. unfold chain_dom, chain_pred, chain_absurd.
    intros H. apply (H 0 (le_n 0)). intros u _ Hu.
    destruct (Hu u (le_n u) u (le_n u)) as [Hp | Hn]; [lia |].
    apply (Hn (S u)); lia.
Qed.

(** The chain refutes the double-negation shift,
    [⊢ (∀x. ¬¬p(x)) → ¬¬(∀x. p(x))], in LJ and LM, with cut or without. *)
Theorem chain_double_negation_shift : forall R (p : symbol),
  ~ lj R [] (imp (fall (neg (neg (var p [bound 0])))) (neg (neg (fall (var p [bound 0]))))).
Proof.
  intros R p.
  apply (kripke_countermodel nat le nat 0 chain_dom chain_fn chain_pred chain_absurd R (chain_model R) [] _ 0).
  - constructor.
  - unfold neg. cbn. unfold chain_dom, chain_pred, chain_absurd.
    intros H. refine (H 0 (le_n 0) _ 0 (le_n 0) _).
    + intros v _ d Hd v0 Hv0 Hn. apply (Hn (S (d + v0))); lia.
    + intros u _ Hall. specialize (Hall u (le_n u) u (le_n u)). lia.
Qed.

End Chain.
