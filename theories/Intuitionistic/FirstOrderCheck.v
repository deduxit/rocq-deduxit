(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * Finite first-order countermodels as data, and their checkers

    A certificate states a finite model as data and checks it by
    computation; a theorem turns the answer [true] into the sequent's
    underivability.

    - A finite structure ([structure]: its size, its function tables and
      its true facts) refutes [Γ ⊢ Δ] in LK when [srefutes] accepts it:
      [apply (fo_classical_refutation String.eqb c S Γ Δ). vm_compute.
      reflexivity.]
    - A finite Kripke model with growing domains ([kripke_model]) refutes
      [Γ ⊢ C] in LJ or LM when [krefutes] accepts it and its world:
      [apply (fo_kripke_refutation String.eqb String.eqb_spec R M w).
      vm_compute. reflexivity.]

    The domain of a structure, and of each world, is [0 … size - 1]. A
    function table [(f, k, values)] gives [f] of [k] arguments
    [d₀ … dₖ₋₁] the value at place [d₀·sizeᵏ⁻¹ + … + dₖ₋₁] of [values]; a
    symbol and arity without a table, or a place past the end, give [0].
    A fact [(p, [d₀; …])] says that [p] holds of those elements.

    The worlds of a Kripke model are [0 … length later - 1]; [later]
    lists for each world the worlds later than it (the world itself may
    be left out), [sizes], [tables] and [facts] give each world's domain
    size, function tables and facts, and [absurd] lists the worlds that
    force [⊥]. [kwell_formed] checks that the order is transitive and
    names worlds only, that every domain is inhabited and every table
    value in its world's domain, and along the order that the domains
    grow, the facts persist, [⊥] persists, and a later world's functions
    agree with the earlier world's on its elements; in LJ no world forces
    [⊥]. *)

From Stdlib Require Import List Bool Arith Lia.
From Deduxit.Intuitionistic Require Calculus.
From Deduxit.Intuitionistic Require Export FirstOrderKripke FirstOrderClassical.
From Deduxit.Base Require Lists.
Import ListNotations.

Section Tables.

Context {symbol : Type}.
Variable symbol_eqb : symbol -> symbol -> bool.

(** A function table: a symbol, its arity and its values. *)
Definition table : Type := (symbol * nat * list nat)%type.

(** The place of the arguments [l] in a table over [size] elements. *)
Definition index (size : nat) (l : list nat) : nat := fold_left (fun i d => i * size + d) l 0.

(** The values of the table of [f] with [k] arguments. *)
Definition lookup (tables : list table) (f : symbol) (k : nat) : option (list nat) :=
  match find (fun '(g, j, _) => symbol_eqb g f && Nat.eqb j k) tables with
  | Some (_, _, values) => Some values
  | None => None
  end.

(** The value of [f] at the arguments [l]. *)
Definition value_of (size : nat) (tables : list table) (f : symbol) (l : list nat) : nat :=
  match lookup tables f (length l) with
  | Some values => nth (index size l) values 0
  | None => 0
  end.

(** Equality of lists of numbers. *)
Fixpoint nats_eqb (l k : list nat) : bool :=
  match l, k with
  | [], [] => true
  | x :: l, y :: k => Nat.eqb x y && nats_eqb l k
  | _, _ => false
  end.

(** [p] holds of [l] by the facts. *)
Definition holds (facts : list (symbol * list nat)) (p : symbol) (l : list nat) : bool :=
  existsb (fun '(q, k) => symbol_eqb q p && nats_eqb k l) facts.

(** Every list of [k] numbers below [n]. *)
Fixpoint tuples (k n : nat) : list (list nat) :=
  match k with
  | 0 => [[]]
  | S k => flat_map (fun d => map (cons d) (tuples k n)) (seq 0 n)
  end.

(** Every value of the tables is below [size]. *)
Definition bounded (size : nat) (tables : list table) : bool :=
  forallb (fun '(_, _, values) => forallb (fun x => x <? size) values) tables.

(** [nats_eqb] decides equality. *)
Lemma nats_eqb_spec : forall l k, reflect (l = k) (nats_eqb l k).
Proof.
  intros l k. apply iff_reflect. apply iff_sym. revert k.
  induction l as [| x l IH]; intros [| y k]; cbn; try (split; congruence).
  rewrite andb_true_iff, Nat.eqb_eq, IH. split; [intros [-> ->]; reflexivity | intros E; injection E; auto].
Qed.

(** Every list of [k] numbers below [n] is one of [tuples k n]. *)
Lemma tuples_in : forall l n, Forall (fun d => d < n) l -> In l (tuples (length l) n).
Proof.
  intros l; induction l as [| d l IH]; intros n H; cbn; [left; reflexivity |].
  apply Forall_cons_iff in H as [Hd Hl]. apply in_flat_map. exists d. split.
  - apply in_seq. lia.
  - apply in_map. exact (IH n Hl).
Qed.

(** The values of bounded tables are below [size]. *)
Lemma value_of_bounded : forall size tables f l, 0 < size -> bounded size tables = true ->
  value_of size tables f l < size.
Proof.
  intros size tables f l Hs Hb. unfold value_of.
  destruct (lookup tables f (length l)) as [values |] eqn:E; [| exact Hs].
  unfold lookup in E.
  destruct (find (fun '(g, j, _) => symbol_eqb g f && Nat.eqb j (length l)) tables)
    as [[[g j] vs] |] eqn:F; [| discriminate].
  injection E as ->. apply find_some in F as [Hin _]. unfold bounded in Hb. rewrite forallb_forall in Hb.
  specialize (Hb _ Hin). cbn in Hb. rewrite forallb_forall in Hb.
  destruct (Nat.lt_ge_cases (index size l) (length values)) as [Hi | Hi].
  - apply Nat.ltb_lt. apply Hb. apply nth_In. exact Hi.
  - rewrite nth_overflow by exact Hi. exact Hs.
Qed.

Hypothesis symbol_eqb_spec : forall f g, reflect (f = g) (symbol_eqb f g).

(** A table found for [f] and [k] is a member [(f, k, values)]. *)
Lemma lookup_in : forall tables f k values, lookup tables f k = Some values -> In (f, k, values) tables.
Proof.
  intros tables f k values H. unfold lookup in H.
  destruct (find (fun '(g, j, _) => symbol_eqb g f && Nat.eqb j k) tables)
    as [[[g j] vs] |] eqn:E; [| discriminate].
  injection H as <-. apply find_some in E as [Hin Hm]. apply andb_true_iff in Hm as [Hg Hj].
  destruct (symbol_eqb_spec g f); [subst g | discriminate]. apply Nat.eqb_eq in Hj. subst j. exact Hin.
Qed.

(** A fact holds exactly when the facts list it. *)
Lemma holds_iff : forall facts p l, holds facts p l = true <-> In (p, l) facts.
Proof.
  intros facts p l. split; intros H.
  - unfold holds in H. apply existsb_exists in H as [[q k] [Hin Hm]].
    apply andb_true_iff in Hm as [Hq Hk]. destruct (symbol_eqb_spec q p); [subst q | discriminate].
    destruct (nats_eqb_spec k l) as [-> | _]; [exact Hin | discriminate Hk].
  - apply existsb_exists. exists (p, l). split; [exact H |].
    apply andb_true_iff. split; [destruct (symbol_eqb_spec p p); [reflexivity | contradiction] |].
    destruct (nats_eqb_spec l l) as [_ | N]; [reflexivity | contradiction].
Qed.

End Tables.

Arguments table symbol : clear implicits.

Section Structures.

Context {symbol : Type}.
Variable symbol_eqb : symbol -> symbol -> bool.

(** A finite structure. *)
Record structure : Type := Structure {
  size : nat;                         (** the domain is [0 … size - 1] *)
  functions : list (table symbol);    (** the function tables *)
  predicates : list (symbol * list nat); (** the true facts *)
}.

(** The structure makes every formula of [G] true and every formula of
    [Dl] false. *)
Definition srefutes (S : structure) (G Dl : list (formula symbol)) : bool :=
  let ev := eval_fast (size S) (value_of symbol_eqb (size S) (functions S))
              (holds symbol_eqb (predicates S)) (fun _ => 0) [] in
  (1 <=? size S) && bounded (size S) (functions S) && allb ev G && negb (anyb ev Dl).

End Structures.

Arguments structure symbol : clear implicits.

(** A finite structure that [srefutes] accepts shows the sequent
    underivable in LK, with cut or without. *)
Theorem fo_classical_refutation : forall {symbol} (symbol_eqb : symbol -> symbol -> bool) c S G Dl,
  srefutes symbol_eqb S G Dl = true -> ~ lk c G Dl.
Proof.
  intros symbol symbol_eqb c S G Dl H. unfold srefutes in H.
  apply andb_true_iff in H as [H HD]. apply andb_true_iff in H as [H HG].
  apply andb_true_iff in H as [Hs Hb]. apply Nat.leb_le in Hs.
  rewrite allb_eval in HG. rewrite anyb_eval in HD.
  apply (classical_countermodel (size S) (value_of symbol_eqb (size S) (functions S))
           (holds symbol_eqb (predicates S)) Hs (fun f l => value_of_bounded symbol_eqb _ _ f l Hs Hb)).
  rewrite HG, HD. reflexivity.
Qed.

Section KripkeModels.

Context {symbol : Type}.
Variable symbol_eqb : symbol -> symbol -> bool.

(** A finite Kripke model with growing domains. *)
Record kripke_model : Type := KripkeModel {
  later : list (list nat);                  (** for each world, the worlds later than it *)
  sizes : list nat;                         (** for each world, the size of its domain *)
  tables : list (list (table symbol));      (** for each world, its function tables *)
  facts : list (list (symbol * list nat));  (** for each world, its true facts *)
  absurd : list nat;                        (** the worlds that force [⊥] *)
}.

Variable M : kripke_model.

(** The number of worlds. *)
Definition nworlds : nat := length (later M).

(** The worlds. *)
Definition kworlds : list nat := seq 0 nworlds.

(** The worlds later than [w], [w] first. *)
Definition kups (w : nat) : list nat := w :: nth w (later M) [].

(** The size of the domain of [w]. *)
Definition size_at (w : nat) : nat := nth w (sizes M) 1.

(** The function tables of [w]. *)
Definition tables_at (w : nat) : list (table symbol) := nth w (tables M) [].

(** The facts of [w]. *)
Definition facts_at (w : nat) : list (symbol * list nat) := nth w (facts M) [].

(** [w] forces [⊥]. *)
Definition absurd_at (w : nat) : bool := Lists.mem w (absurd M).

(** The value of [f] at [l] in [w]. *)
Definition fn_at (w : nat) (f : symbol) (l : list nat) : nat :=
  value_of symbol_eqb (size_at w) (tables_at w) f l.

(** A later world [v] agrees with [w] on [w]'s elements, for every
    table of either. *)
Definition agree (w v : nat) : bool :=
  forallb (fun '(f, k, _) =>
    forallb (fun l => Nat.eqb (fn_at v f l) (fn_at w f l)) (tuples k (size_at w)))
    (tables_at w ++ tables_at v).

(** What a later world [v] of [w] must satisfy. *)
Definition above_ok (w v : nat) : bool :=
  (v <? nworlds)
  && forallb (fun u => Lists.mem u (kups w)) (kups v)
  && (size_at w <=? size_at v)
  && forallb (fun '(p, l) => holds symbol_eqb (facts_at v) p l) (facts_at w)
  && implb (absurd_at w) (absurd_at v)
  && agree w v.

(** What a world must satisfy. *)
Definition world_ok (w : nat) : bool :=
  (1 <=? size_at w) && bounded (size_at w) (tables_at w) && forallb (above_ok w) (kups w).

(** The model is one of [R]'s. *)
Definition kwell_formed (R : Calculus.rules) : bool :=
  (length (sizes M) =? nworlds) && (length (tables M) =? nworlds) && (length (facts M) =? nworlds)
  && forallb world_ok kworlds
  && implb (Calculus.explosion R) (length (absurd M) =? 0).

(** Whether [w] forces [A], the eigenvariables taking the value [0]. *)
Fixpoint kforces (w : nat) (rho : list nat) (A : formula symbol) : bool :=
  match A with
  | var p l => holds symbol_eqb (facts_at w) p (map (teval 0 fn_at w (fun _ => 0) rho) l)
  | bot => absurd_at w
  | wedge A B => kforces w rho A && kforces w rho B
  | vee A B => kforces w rho A || kforces w rho B
  | imp A B => forallb (fun v => implb (kforces v rho A) (kforces v rho B)) (kups w)
  | fall A => forallb (fun v => forallb (fun d => kforces v (d :: rho) A) (seq 0 (size_at v))) (kups w)
  | fex A => existsb (fun d => kforces w (d :: rho) A) (seq 0 (size_at w))
  end.

(** [kforces], stopping at the first operand, world or element that
    decides a connective or a quantifier: what a certificate computes. *)
Fixpoint kforces_fast (w : nat) (rho : list nat) (A : formula symbol) : bool :=
  match A with
  | var p l => holds symbol_eqb (facts_at w) p (map (teval 0 fn_at w (fun _ => 0) rho) l)
  | bot => absurd_at w
  | wedge A B => if kforces_fast w rho A then kforces_fast w rho B else false
  | vee A B => if kforces_fast w rho A then true else kforces_fast w rho B
  | imp A B => allb (fun v => if kforces_fast v rho A then kforces_fast v rho B else true) (kups w)
  | fall A =>
      allb (fun v => allb (fun d => kforces_fast v (d :: rho) A) (seq 0 (size_at v))) (kups w)
  | fex A => anyb (fun d => kforces_fast w (d :: rho) A) (seq 0 (size_at w))
  end.

(** [kforces_fast] computes [kforces]. *)
Lemma kforces_fast_kforces : forall A w rho, kforces_fast w rho A = kforces w rho A.
Proof.
  intros A; induction A as [p l | | A IHA B IHB | A IHA B IHB | A IHA B IHB | A IHA | A IHA];
    intros w rho; cbn [kforces_fast kforces].
  - reflexivity.
  - reflexivity.
  - rewrite IHA, IHB. destruct (kforces w rho A); reflexivity.
  - rewrite IHA, IHB. destruct (kforces w rho A); reflexivity.
  - rewrite allb_forallb. apply forallb_ext_in. intros v _. rewrite IHA, IHB.
    destruct (kforces v rho A); reflexivity.
  - rewrite allb_forallb. apply forallb_ext_in. intros v _.
    rewrite allb_forallb. apply forallb_ext_in. intros d _. apply IHA.
  - rewrite anyb_existsb. apply existsb_ext_in. intros d _. apply IHA.
Qed.

(** The model is one of [R]'s, and its world [w] forces every formula of
    [G] and not [C]. *)
Definition krefutes (R : Calculus.rules) (w : nat) (G : list (formula symbol)) (C : formula symbol) : bool :=
  kwell_formed R && (w <? nworlds) && allb (kforces_fast w []) G && negb (kforces_fast w [] C).

(** The model read as a Kripke model over the natural numbers: a number
    past the worlds is later only than itself, has the domain [{0}], no
    table and no fact. *)
Local Definition kle (w v : nat) : Prop := Lists.mem v (kups w) = true.
(** The domain of [w]. *)
Local Definition kdom (w d : nat) : Prop := d < size_at w.
(** The predicates of [w]. *)
Local Definition kpred (w : nat) (p : symbol) (l : list nat) : Prop := holds symbol_eqb (facts_at w) p l = true.
(** [w] forces [⊥]. *)
Local Definition kabs (w : nat) : Prop := absurd_at w = true.

(** [kforces] computes forcing, at every world. *)
Lemma kforces_forces : forall A w rho,
  kforces w rho A = true <-> forces kle 0 kdom fn_at kpred kabs w (fun _ => 0) rho A.
Proof.
  intros A; induction A as [p l | | A IHA B IHB | A IHA B IHB | A IHA B IHB | A IHA | A IHA];
    intros w rho; cbn [kforces forces]; unfold kle, kdom, kpred, kabs.
  - reflexivity.
  - reflexivity.
  - rewrite andb_true_iff, IHA, IHB. reflexivity.
  - rewrite orb_true_iff, IHA, IHB. reflexivity.
  - rewrite forallb_forall. split.
    + intros H v Hle HA. apply Lists.mem_iff in Hle. specialize (H v Hle).
      apply IHB. apply IHA in HA. rewrite HA in H. exact H.
    + intros H v Hv. destruct (kforces v rho A) eqn:E; [| reflexivity]. cbn.
      apply IHB. apply H; [apply Lists.mem_iff; exact Hv | apply IHA; exact E].
  - rewrite forallb_forall. split.
    + intros H v Hle d Hd. apply Lists.mem_iff in Hle. specialize (H v Hle).
      rewrite forallb_forall in H. apply IHA. apply H. apply in_seq. lia.
    + intros H v Hv. apply forallb_forall. intros d Hd. apply in_seq in Hd.
      apply IHA. apply H; [apply Lists.mem_iff; exact Hv | lia].
  - rewrite existsb_exists. split.
    + intros [d [Hd H]]. apply in_seq in Hd. exists d. split; [lia | apply IHA; exact H].
    + intros [d [Hd H]]. exists d. split; [apply in_seq; lia | apply IHA; exact H].
Qed.

(** A number past the worlds has itself alone above it. *)
Lemma kups_past : forall w, nworlds <= w -> kups w = [w].
Proof.
  intros w H. unfold kups. rewrite nth_overflow by exact H. reflexivity.
Qed.

(** A step from a number past the worlds stays there. *)
Lemma kle_past : forall w v, nworlds <= w -> kle w v -> v = w.
Proof.
  intros w v Hw H. unfold kle in H. rewrite kups_past in H by exact Hw.
  apply Lists.mem_iff in H. destruct H as [E | []]. symmetry. exact E.
Qed.

Hypothesis symbol_eqb_spec : forall f g, reflect (f = g) (symbol_eqb f g).

Variable R : Calculus.rules.
Hypothesis Hwf : kwell_formed R = true.

(** What [kwell_formed] checks of the lists. *)
Lemma wf_lists : length (sizes M) = nworlds /\ length (tables M) = nworlds /\ length (facts M) = nworlds
  /\ (Calculus.explosion R = true -> absurd M = []).
Proof.
  pose proof Hwf as H. unfold kwell_formed in H. repeat rewrite andb_true_iff in H.
  destruct H as [[[[Hs Ht] Hf] _] Hx]. apply Nat.eqb_eq in Hs, Ht, Hf.
  repeat split; try assumption. intros Hexp. rewrite Hexp in Hx. cbn in Hx.
  apply Nat.eqb_eq, length_zero_iff_nil in Hx. exact Hx.
Qed.

(** What [kwell_formed] checks of each world. *)
Lemma wf_world : forall w, w < nworlds -> world_ok w = true.
Proof.
  intros w Hw. pose proof Hwf as H. unfold kwell_formed in H. repeat rewrite andb_true_iff in H.
  destruct H as [[_ H] _]. rewrite forallb_forall in H. apply H. apply in_seq. lia.
Qed.

(** What [kwell_formed] checks of each world and each later one. *)
Lemma wf_above : forall w v, w < nworlds -> In v (kups w) ->
  v < nworlds
  /\ (forall u, In u (kups v) -> In u (kups w))
  /\ size_at w <= size_at v
  /\ (forall p l, In (p, l) (facts_at w) -> holds symbol_eqb (facts_at v) p l = true)
  /\ (absurd_at w = true -> absurd_at v = true)
  /\ agree w v = true.
Proof.
  intros w v Hw Hv. pose proof (wf_world w Hw) as H. unfold world_ok in H.
  apply andb_true_iff in H as [_ H]. rewrite forallb_forall in H. specialize (H v Hv).
  unfold above_ok in H. repeat rewrite andb_true_iff in H.
  destruct H as [[[[[Hn Ht] Hs] Hp] Ha] Hg]. repeat split.
  - apply Nat.ltb_lt. exact Hn.
  - intros u Hu. rewrite forallb_forall in Ht. apply Lists.mem_iff. exact (Ht u Hu).
  - apply Nat.leb_le. exact Hs.
  - intros p l Hpl. rewrite forallb_forall in Hp. exact (Hp (p, l) Hpl).
  - intros E. rewrite E in Ha. exact Ha.
  - exact Hg.
Qed.

(** Every domain is inhabited, and every table value of a world is in
    its domain. *)
Lemma wf_tables : forall w, 0 < size_at w /\ bounded (size_at w) (tables_at w) = true.
Proof.
  intros w. destruct (Nat.lt_ge_cases w nworlds) as [Hw | Hw].
  - pose proof (wf_world w Hw) as H. unfold world_ok in H. repeat rewrite andb_true_iff in H.
    destruct H as [[Hs Hb] _]. apply Nat.leb_le in Hs. split; [lia | exact Hb].
  - destruct wf_lists as [Hs [Ht _]]. unfold size_at, tables_at.
    rewrite (nth_overflow (sizes M)) by lia. rewrite (nth_overflow (tables M)) by lia.
    split; [lia | reflexivity].
Qed.

(** Where [agree] holds, the later world keeps the functions' values on
    the earlier world's elements. *)
Lemma agree_fn : forall w v f l, agree w v = true -> Forall (kdom w) l -> fn_at v f l = fn_at w f l.
Proof.
  intros w v f l Hg Hl. unfold agree in Hg. rewrite forallb_forall in Hg.
  assert (Hcover : forall values, In (f, length l, values) (tables_at w ++ tables_at v) ->
                     fn_at v f l = fn_at w f l).
  { intros values Hin. specialize (Hg _ Hin). cbn in Hg. rewrite forallb_forall in Hg.
    apply Nat.eqb_eq. apply Hg. apply tuples_in. exact Hl. }
  unfold fn_at at 1. unfold value_of at 1.
  destruct (lookup symbol_eqb (tables_at v) f (length l)) as [values |] eqn:Ev.
  - rewrite <- (Hcover values) by (apply in_or_app; right; apply (lookup_in symbol_eqb symbol_eqb_spec); exact Ev).
    unfold fn_at, value_of. rewrite Ev. reflexivity.
  - unfold fn_at, value_of. destruct (lookup symbol_eqb (tables_at w) f (length l)) as [values |] eqn:Ew;
      [| reflexivity].
    pose proof (Hcover values) as E.
    unfold fn_at, value_of in E. rewrite Ev, Ew in E. apply E.
    apply in_or_app. left. apply (lookup_in symbol_eqb symbol_eqb_spec). exact Ew.
Qed.

(** A well-formed model is a Kripke model of its logic. *)
Lemma kwell_formed_model : model nat kle nat 0 kdom fn_at kpred kabs R.
Proof.
  split.
  - intros w. unfold kle, kups. apply Lists.mem_iff. left. reflexivity.
  - intros u v w Huv Hvw. destruct (Nat.lt_ge_cases u nworlds) as [Hu | Hu].
    + unfold kle in *. apply Lists.mem_iff in Huv, Hvw. apply Lists.mem_iff.
      exact (proj1 (proj2 (wf_above u v Hu Huv)) w Hvw).
    + apply kle_past in Huv; [subst; exact Hvw | exact Hu].
  - intros w v d Hle Hd. unfold kdom in *. destruct (Nat.lt_ge_cases w nworlds) as [Hw | Hw].
    + unfold kle in Hle. apply Lists.mem_iff in Hle.
      pose proof (proj1 (proj2 (proj2 (wf_above w v Hw Hle)))). lia.
    + apply kle_past in Hle; [subst; exact Hd | exact Hw].
  - intros w. unfold kdom. exact (proj1 (wf_tables w)).
  - intros w f l _. unfold kdom, fn_at.
    exact (value_of_bounded symbol_eqb _ _ f l (proj1 (wf_tables w)) (proj2 (wf_tables w))).
  - intros w v f l Hle Hl. destruct (Nat.lt_ge_cases w nworlds) as [Hw | Hw].
    + unfold kle in Hle. apply Lists.mem_iff in Hle.
      exact (agree_fn w v f l (proj2 (proj2 (proj2 (proj2 (proj2 (wf_above w v Hw Hle)))))) Hl).
    + apply kle_past in Hle; [subst; reflexivity | exact Hw].
  - intros w v p l Hle H. unfold kpred in *. destruct (Nat.lt_ge_cases w nworlds) as [Hw | Hw].
    + unfold kle in Hle. apply Lists.mem_iff in Hle.
      apply (proj1 (proj2 (proj2 (proj2 (wf_above w v Hw Hle))))).
      exact (proj1 (holds_iff symbol_eqb symbol_eqb_spec _ _ _) H).
    + apply kle_past in Hle; [subst; exact H | exact Hw].
  - intros w v Hle H. unfold kabs in *. destruct (Nat.lt_ge_cases w nworlds) as [Hw | Hw].
    + unfold kle in Hle. apply Lists.mem_iff in Hle.
      exact (proj1 (proj2 (proj2 (proj2 (proj2 (wf_above w v Hw Hle))))) H).
    + apply kle_past in Hle; [subst; exact H | exact Hw].
  - intros Hexp w H. unfold kabs, absurd_at, Lists.mem in H.
    rewrite (proj2 (proj2 (proj2 wf_lists)) Hexp) in H. discriminate.
Qed.

End KripkeModels.

Arguments kripke_model symbol : clear implicits.

(** A finite Kripke model that [krefutes] accepts shows the sequent
    underivable in LJ or LM, with cut or without. *)
Theorem fo_kripke_refutation : forall {symbol} (symbol_eqb : symbol -> symbol -> bool),
  (forall f g, reflect (f = g) (symbol_eqb f g)) ->
  forall R M w G C, krefutes symbol_eqb M R w G C = true -> ~ lj R G C.
Proof.
  intros symbol symbol_eqb spec R M w G C H. unfold krefutes in H.
  repeat rewrite andb_true_iff in H. destruct H as [[[Hwf _] HG] HC].
  apply (kripke_countermodel _ _ _ _ _ _ _ _ R (kwell_formed_model symbol_eqb M spec R Hwf) G C w).
  - apply Forall_forall. intros A HA. rewrite allb_forallb, forallb_forall in HG.
    apply (kforces_forces symbol_eqb M A w []). rewrite <- kforces_fast_kforces. exact (HG A HA).
  - rewrite <- (kforces_forces symbol_eqb M C w []). rewrite <- kforces_fast_kforces.
    apply negb_true_iff in HC. rewrite HC. discriminate.
Qed.
