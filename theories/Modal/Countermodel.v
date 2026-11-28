(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * Finite countermodels

    A finite Kripke model as data, and a test a computation decides:
    [refutes C w Γ Δ] says that the model's frame meets the conditions
    [C] and that its world [w] forces every formula of [Γ] and none of
    [Δ]. [modal_refutation] concludes that the sequent is not valid in
    the system of [C].

    The worlds are the numbers below the length of [arrows]. The arrows
    are the relation itself: nothing is added to them, so a model of a
    reflexive system lists every world among the worlds it sees. *)

From Stdlib Require Import List Bool Arith Lia.
From Deduxit.Modal Require Export Kripke.
From Deduxit.Base Require Lists.
Import ListNotations.

Section Countermodel.

Context {atom : Type}.

Variable atom_eqb : atom -> atom -> bool.

(** A finite model: for each world, the worlds it sees and the atoms
    true at it. *)
Record model : Type := Model {
  arrows : list (list nat);
  atoms : list (list atom);
}.

Variable m : model.

(** The number of worlds. *)
Definition size : nat := length (arrows m).

(** The worlds that [w] sees. *)
Definition sees (w : nat) : list nat := nth w (arrows m) [].

(** Every world. *)
Definition worlds : list nat := seq 0 size.

(** Whether the list [l] holds the world [w]. *)
Definition among (w : nat) (l : list nat) : bool := Lists.mem w l.

(** Whether the world [w] is marked in the table [l]. *)
Definition forced_at (l : list bool) (w : nat) : bool := nth w l false.

(** For each world, whether it forces [A]. The table of a formula is
    computed once from the tables of its parts, so the cost does not
    grow with the nesting of the modalities. *)
Fixpoint forced (A : formula atom) : list bool :=
  match A with
  | var a => map (fun w => existsb (atom_eqb a) (nth w (atoms m) [])) worlds
  | top => map (fun _ => true) worlds
  | bot => map (fun _ => false) worlds
  | neg A =>
      let fa := forced A in
      map (fun w => negb (forced_at fa w)) worlds
  | wedge A B =>
      let fa := forced A in
      let fb := forced B in
      map (fun w => forced_at fa w && forced_at fb w) worlds
  | vee A B =>
      let fa := forced A in
      let fb := forced B in
      map (fun w => forced_at fa w || forced_at fb w) worlds
  | imp A B =>
      let fa := forced A in
      let fb := forced B in
      map (fun w => implb (forced_at fa w) (forced_at fb w)) worlds
  | equiv A B =>
      let fa := forced A in
      let fb := forced B in
      map (fun w => Bool.eqb (forced_at fa w) (forced_at fb w)) worlds
  | box A =>
      let fa := forced A in
      map (fun w => forallb (forced_at fa) (sees w)) worlds
  | dia A =>
      let fa := forced A in
      map (fun w => existsb (forced_at fa) (sees w)) worlds
  end.

(** Whether every arrow leads to a world. *)
Definition bounded : bool :=
  forallb (forallb (fun v => v <? size)) (arrows m).

(** Whether the arrows meet every condition of [C]. *)
Definition meets (C : conditions) : bool :=
  bounded
  && implb (serial C)
       (forallb (fun w => match sees w with [] => false | _ :: _ => true end)
          worlds)
  && implb (reflexive C)
       (forallb (fun w => among w (sees w)) worlds)
  && implb (symmetric C)
       (forallb (fun w => forallb (fun v => among w (sees v)) (sees w)) worlds)
  && implb (transitive C)
       (forallb (fun w =>
          forallb (fun v => forallb (fun u => among u (sees w)) (sees v))
            (sees w)) worlds)
  && implb (euclidean C)
       (forallb (fun w =>
          forallb (fun v => forallb (fun u => among u (sees v)) (sees w))
            (sees w)) worlds).

(** Whether the model is one of the system of [C] whose world [w]
    forces every formula of [Γ] and none of [Δ]. *)
Definition refutes (C : conditions) (w : nat) (Γ Δ : list (formula atom)) : bool :=
  meets C && (w <? size)
  && forallb (fun A => forced_at (forced A) w) Γ
  && forallb (fun B => negb (forced_at (forced B) w)) Δ.

(** The model as a Kripke model: its worlds, its relation and its
    valuation. *)
Definition world : Type := { w : nat | w < size }.

Definition R (x y : world) : Prop := In (proj1_sig y) (sees (proj1_sig x)).

Definition V (x : world) (a : atom) : Prop :=
  existsb (atom_eqb a) (nth (proj1_sig x) (atoms m) []) = true.

Lemma in_worlds : forall w, w < size -> In w worlds.
Proof.
  intros w H. apply in_seq. lia.
Qed.

Lemma among_iff : forall w l, among w l = true <-> In w l.
Proof. exact Lists.mem_iff. Qed.

Lemma sees_bounded : bounded = true ->
  forall w v, In v (sees w) -> v < size.
Proof.
  intros Hb w v Hv. unfold sees in Hv.
  destruct (Nat.lt_ge_cases w (length (arrows m))) as [Hw | Hw].
  - pose proof (proj1 (forallb_forall _ _) Hb _ (nth_In _ [] Hw)) as Hl.
    exact (proj1 (Nat.ltb_lt v size) (proj1 (forallb_forall _ _) Hl v Hv)).
  - rewrite (nth_overflow _ _ Hw) in Hv. destruct Hv.
Qed.

Lemma table : forall (f : nat -> bool) n s w,
  w < n -> nth w (map f (seq s n)) false = f (s + w).
Proof.
  intros f n; induction n as [| n IH]; intros s w H; [lia |].
  destruct w as [| w]; cbn [seq map nth].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite (IH (S s) w) by lia. rewrite Nat.add_succ_r. reflexivity.
Qed.

Lemma forced_table : forall (f : nat -> bool) (x : world),
  forced_at (map f worlds) (proj1_sig x) = f (proj1_sig x).
Proof.
  intros f [w Hw]. unfold forced_at, worlds. exact (table f size 0 w Hw).
Qed.

Lemma meets_frame : forall C, meets C = true -> frame R C.
Proof.
  intros C H. unfold meets in H.
  repeat match goal with
  | E : _ && _ = true |- _ => apply andb_true_iff in E; destruct E
  end.
  match goal with E : bounded = true |- _ => rename E into Hb end.
  assert (at_world : forall f (x : world), forallb f worlds = true ->
            f (proj1_sig x) = true).
  { intros f [w Hw] E. exact (proj1 (forallb_forall _ _) E w (in_worlds w Hw)). }
  split; intro Hc;
    match goal with
    | E : implb ?c _ = true |- _ =>
        match type of Hc with c = true => rewrite Hc in E; cbn [implb] in E;
          rename E into Hall
        end
    end.
  - intros x. pose proof (at_world _ x Hall) as Hx. cbn beta in Hx.
    destruct (sees (proj1_sig x)) as [| v l] eqn:E; [discriminate |].
    assert (Hv : v < size).
    { apply (sees_bounded Hb (proj1_sig x)). rewrite E. left. reflexivity. }
    exists (exist _ v Hv). unfold R. cbn [proj1_sig]. rewrite E. left. reflexivity.
  - intros x. exact (proj1 (among_iff _ _) (at_world _ x Hall)).
  - intros x y Hxy. pose proof (at_world _ x Hall) as Hx. cbn beta in Hx.
    exact (proj1 (among_iff _ _) (proj1 (forallb_forall _ _) Hx _ Hxy)).
  - intros x y z Hxy Hyz. pose proof (at_world _ x Hall) as Hx. cbn beta in Hx.
    pose proof (proj1 (forallb_forall _ _) Hx _ Hxy) as Hy. cbn beta in Hy.
    exact (proj1 (among_iff _ _) (proj1 (forallb_forall _ _) Hy _ Hyz)).
  - intros x y z Hxy Hxz. pose proof (at_world _ x Hall) as Hx. cbn beta in Hx.
    pose proof (proj1 (forallb_forall _ _) Hx _ Hxy) as Hy. cbn beta in Hy.
    exact (proj1 (among_iff _ _) (proj1 (forallb_forall _ _) Hy _ Hxz)).
Qed.

Lemma reflect_neg : forall b P, (b = true <-> P) -> (negb b = true <-> ~ P).
Proof.
  intros [|] P [H1 H2]; cbn; split; intro H; try discriminate.
  - exfalso. exact (H (H1 eq_refl)).
  - intro HP. discriminate (H2 HP).
  - reflexivity.
Qed.

Lemma reflect_iff : forall b c P Q, (b = true <-> P) -> (c = true <-> Q) ->
  (Bool.eqb b c = true <-> (P <-> Q)).
Proof.
  intros [|] [|] P Q [H1 H2] [H3 H4]; cbn; split; intro H; try reflexivity;
    try discriminate.
  - split; intro; [exact (H3 eq_refl) | exact (H1 eq_refl)].
  - discriminate (H4 (proj1 H (H1 eq_refl))).
  - discriminate (H2 (proj2 H (H3 eq_refl))).
  - split; intro HP; [discriminate (H2 HP) | discriminate (H4 HP)].
Qed.

(** The table of a formula marks exactly the worlds that force it. *)
Lemma forced_forces : bounded = true -> forall A (x : world),
  forced_at (forced A) (proj1_sig x) = true <-> forces R V x A.
Proof.
  intros Hb A.
  induction A as [a | | | A IHA | A IHA B IHB | A IHA B IHB | A IHA B IHB
    | A IHA B IHB | A IHA | A IHA]; intros x; cbn [forced forces];
    cbv zeta; rewrite forced_table.
  - reflexivity.
  - split; intro; [exact I | reflexivity].
  - split; [discriminate | intros []].
  - exact (reflect_neg _ _ (IHA x)).
  - rewrite andb_true_iff. split; intros [H1 H2].
    + split; [exact (proj1 (IHA x) H1) | exact (proj1 (IHB x) H2)].
    + split; [exact (proj2 (IHA x) H1) | exact (proj2 (IHB x) H2)].
  - rewrite orb_true_iff. split; intros [H | H].
    + left. exact (proj1 (IHA x) H).
    + right. exact (proj1 (IHB x) H).
    + left. exact (proj2 (IHA x) H).
    + right. exact (proj2 (IHB x) H).
  - rewrite implb_true_iff. split; intros H HA.
    + exact (proj1 (IHB x) (H (proj2 (IHA x) HA))).
    + exact (proj2 (IHB x) (H (proj1 (IHA x) HA))).
  - exact (reflect_iff _ _ _ _ (IHA x) (IHB x)).
  - split.
    + intros H v Hv.
      exact (proj1 (IHA v) (proj1 (forallb_forall _ _) H _ Hv)).
    + intro H. apply forallb_forall. intros u Hu.
      pose proof (sees_bounded Hb _ _ Hu) as Hlt.
      exact (proj2 (IHA (exist _ u Hlt)) (H (exist _ u Hlt) Hu)).
  - split.
    + intro H. apply existsb_exists in H as [u [Hu Hf]].
      pose proof (sees_bounded Hb _ _ Hu) as Hlt.
      exists (exist _ u Hlt). split; [exact Hu |].
      exact (proj1 (IHA (exist _ u Hlt)) Hf).
    + intros [v [Hv Hf]]. apply existsb_exists.
      exists (proj1_sig v). split; [exact Hv | exact (proj2 (IHA v) Hf)].
Qed.

(** A finite model decides every formula at every world, so its forcing
    is stable. *)
Lemma finite_stable : bounded = true -> stable R V.
Proof.
  intros Hb x A H. apply (forced_forces Hb).
  destruct (forced_at (forced A) (proj1_sig x)) eqn:E; [reflexivity |].
  exfalso. apply H. intro Hf. apply (forced_forces Hb) in Hf. congruence.
Qed.

(** A model of the system with a world that forces every formula of [Γ]
    and none of [Δ] shows the sequent [Γ ⊢ Δ] not valid. *)
Theorem modal_refutation : forall C w (Γ Δ : list (formula atom)),
  refutes C w Γ Δ = true -> ~ valid C Γ Δ.
Proof.
  intros C w Γ Δ H Hv. unfold refutes in H.
  apply andb_true_iff in H as [H HD]. apply andb_true_iff in H as [H HG].
  apply andb_true_iff in H as [Hm Hw]. apply Nat.ltb_lt in Hw.
  assert (Hb : bounded = true).
  { unfold meets in Hm.
    repeat match goal with
    | E : _ && _ = true |- _ => apply andb_true_iff in E; destruct E
    end. assumption. }
  set (x := exist (fun w => w < size) w Hw : world).
  assert (Hx : Forall (forces R V x) Γ).
  { apply Forall_forall. intros A HA. apply (forced_forces Hb).
    exact (proj1 (forallb_forall _ _) HG A HA). }
  pose proof (Hv world R V (meets_frame C Hm) (finite_stable Hb) x Hx) as He.
  apply Exists_exists in He as [B [HB Hf]].
  apply (forced_forces Hb) in Hf. cbn [proj1_sig x] in Hf.
  pose proof (proj1 (forallb_forall _ _) HD B HB) as Hn. cbn beta in Hn.
  unfold x in Hf. cbn [proj1_sig] in Hf. rewrite Hf in Hn. discriminate.
Qed.

End Countermodel.

Arguments model atom : clear implicits.
