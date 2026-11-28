(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * Finite Kripke models as data, and their checker

    A certificate states a finite model as data ([finite_model]) and the
    world that refutes the sequent; [refutes] checks both by
    computation, and [kripke_refutation] turns its answer [true] into
    [~ lj R Γ C]:

    [apply (kripke_refutation String.eqb String.eqb_spec intuitionistic
    {| later := [[1; 2]; []; []]; atoms := [[]; ["a"]; ["b"]];
    absurd := [] |} 0). vm_compute. reflexivity.]

    The worlds are the numbers below [length (later M)]. [later M] lists
    for each world the worlds later than it (the world itself may be
    left out, since every world is later than itself), [atoms M] the
    atoms each world forces (a world past its end forces none), and
    [absurd M] the worlds that force [⊥], which LJ requires empty.
    [refutes] checks that the relation is transitive, names worlds
    only, and that later worlds force every atom and every [⊥] earlier
    ones do; then it computes, for each subformula, the worlds that
    force it, and asks the given world to force every hypothesis and not
    the conclusion. *)

From Stdlib Require Import List Bool Arith.
From Deduxit.Intuitionistic Require Export Kripke.
From Deduxit.Base Require Lists.
Import ListNotations.

Section Check.

Context {atom : Type}.

(** A finite Kripke model. *)
Record finite_model : Type := FiniteModel {
  later : list (list nat);  (** for each world, the worlds later than it *)
  atoms : list (list atom); (** for each world, the atoms it forces *)
  absurd : list nat;        (** the worlds that force [⊥] *)
}.

Variable atom_eqb : atom -> atom -> bool.
Variable M : finite_model.

(** The number of worlds. *)
Definition size : nat := length (later M).

(** The worlds. *)
Definition worlds : list nat := seq 0 size.

(** The worlds later than [w], [w] first. *)
Definition ups (w : nat) : list nat := w :: nth w (later M) [].

(** The atoms [w] forces. *)
Definition atoms_at (w : nat) : list atom := nth w (atoms M) [].

(** [w] forces the atom [a]. *)
Definition forces_atom (w : nat) (a : atom) : bool := existsb (atom_eqb a) (atoms_at w).

(** [w] forces [⊥]. *)
Definition absurd_at (w : nat) : bool := Lists.mem w (absurd M).

(** The model is one of the logic of [R]: the relation is transitive
    and names worlds only, a later world forces every atom and every
    [⊥] an earlier one does, and in LJ no world forces [⊥]. *)
Definition well_formed (R : rules) : bool :=
  forallb (fun w =>
    forallb (fun v =>
      (v <? size)
      && forallb (fun u => Lists.mem u (ups w)) (ups v)
      && forallb (forces_atom v) (atoms_at w)
      && implb (absurd_at w) (absurd_at v))
    (ups w))
  worlds
  && implb (explosion R) (length (absurd M) =? 0).

(** For each world in order, whether it forces [A]. *)
Fixpoint forced (A : formula atom) : list bool :=
  match A with
  | var a => map (fun w => forces_atom w a) worlds
  | bot => map absurd_at worlds
  | wedge A B =>
      let fa := forced A in let fb := forced B in
      map (fun w => nth w fa false && nth w fb false) worlds
  | vee A B =>
      let fa := forced A in let fb := forced B in
      map (fun w => nth w fa false || nth w fb false) worlds
  | imp A B =>
      let fa := forced A in let fb := forced B in
      map (fun w => forallb (fun v => implb (nth v fa false) (nth v fb false)) (ups w)) worlds
  end.

(** The model is one of [R]'s and its world [w] forces every formula of
    [G] and not [C]. *)
Definition refutes (R : rules) (w : nat) (G : list (formula atom)) (C : formula atom) : bool :=
  well_formed R && (w <? size)
  && forallb (fun A => nth w (forced A) false) G
  && negb (nth w (forced C) false).

(** The model read as a Kripke model over the natural numbers: a number
    past the worlds is later only than itself and forces no atom.
    [le w v]: [v] is later than [w]. *)
Local Definition le (w v : nat) : Prop := Lists.mem v (ups w) = true.
(** [w] forces the atom [a]. *)
Local Definition val (w : nat) (a : atom) : Prop := forces_atom w a = true.
(** [w] forces [⊥]. *)
Local Definition abs (w : nat) : Prop := absurd_at w = true.

(** A number past the worlds has itself alone above it. *)
Lemma ups_past : forall w, size <= w -> ups w = [w].
Proof.
  intros w H. unfold ups. rewrite nth_overflow by exact H. reflexivity.
Qed.

(** A vector over the worlds holds, at a world, its entry. *)
Lemma nth_worlds : forall (f : nat -> bool) w,
  w < size -> nth w (map f worlds) false = f w.
Proof.
  intros f w H. unfold worlds.
  rewrite (nth_indep _ false (f 0)) by (rewrite length_map, length_seq; exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

(** What [well_formed] checks of each world and each later one. *)
Lemma well_formed_at : forall R, well_formed R = true ->
  forall w v, w < size -> In v (ups w) ->
  v < size
  /\ (forall u, In u (ups v) -> In u (ups w))
  /\ (forall a, In a (atoms_at w) -> forces_atom v a = true)
  /\ (absurd_at w = true -> absurd_at v = true).
Proof.
  intros R H w v Hw Hv. apply andb_true_iff in H as [H _].
  rewrite forallb_forall in H.
  assert (Hw' : In w worlds) by (apply in_seq; split; [apply Nat.le_0_l | exact Hw]).
  specialize (H w Hw'). rewrite forallb_forall in H. specialize (H v Hv).
  repeat rewrite andb_true_iff in H. destruct H as [[[Hsize Htrans] Hatoms] Habs].
  repeat split.
  - apply Nat.ltb_lt. exact Hsize.
  - intros u Hu. rewrite forallb_forall in Htrans. apply Lists.mem_iff. exact (Htrans u Hu).
  - intros a Ha. rewrite forallb_forall in Hatoms. exact (Hatoms a Ha).
  - intros Hw''. rewrite Hw'' in Habs. exact Habs.
Qed.

(** A step from a world past the worlds stays there. *)
Lemma le_past : forall w v, size <= w -> le w v -> v = w.
Proof.
  intros w v Hw H. unfold le in H. rewrite ups_past in H by exact Hw.
  apply Lists.mem_iff in H. destruct H as [E | []]. symmetry. exact E.
Qed.

Hypothesis atom_eqb_spec : forall a b, reflect (a = b) (atom_eqb a b).

(** A well-formed model is a Kripke model of its logic. *)
Lemma well_formed_model : forall R, well_formed R = true -> model nat le val abs R.
Proof.
  intros R H. split.
  - intros w. unfold le, ups. apply Lists.mem_iff. left. reflexivity.
  - intros u v w Huv Hvw. destruct (Nat.lt_ge_cases u size) as [Hu | Hu].
    + unfold le in *. apply Lists.mem_iff in Huv, Hvw. apply Lists.mem_iff.
      exact (proj1 (proj2 (well_formed_at R H u v Hu Huv)) w Hvw).
    + apply le_past in Huv; [subst; exact Hvw | exact Hu].
  - intros w v a Hle Ha. destruct (Nat.lt_ge_cases w size) as [Hw | Hw].
    + unfold le, val, forces_atom in *. apply Lists.mem_iff in Hle.
      apply existsb_exists in Ha as [b [Hb E]].
      destruct (atom_eqb_spec a b); [subst | discriminate].
      exact (proj1 (proj2 (proj2 (well_formed_at R H w v Hw Hle))) b Hb).
    + apply le_past in Hle; [subst; exact Ha | exact Hw].
  - intros w v Hle Ha. destruct (Nat.lt_ge_cases w size) as [Hw | Hw].
    + unfold le, abs in *. apply Lists.mem_iff in Hle.
      exact (proj2 (proj2 (proj2 (well_formed_at R H w v Hw Hle))) Ha).
    + apply le_past in Hle; [subst; exact Ha | exact Hw].
  - intros Hexp w Hw. unfold abs, absurd_at, Lists.mem in Hw.
    apply andb_true_iff in H as [_ H]. rewrite Hexp in H. cbn in H.
    apply Nat.eqb_eq, length_zero_iff_nil in H. rewrite H in Hw. discriminate.
Qed.

(** At a world of a well-formed model, [forced] computes forcing. *)
Lemma forced_forces : forall R, well_formed R = true ->
  forall A w, w < size -> nth w (forced A) false = true <-> forces le val abs w A.
Proof.
  intros R H A. induction A as [a | | A IHA B IHB | A IHA B IHB | A IHA B IHB];
    intros w Hw; cbn [forced forces]; rewrite nth_worlds by exact Hw.
  - reflexivity.
  - reflexivity.
  - rewrite andb_true_iff, IHA, IHB by exact Hw. reflexivity.
  - rewrite orb_true_iff, IHA, IHB by exact Hw. reflexivity.
  - rewrite forallb_forall. split.
    + intros Himp v Hle HA. unfold le in Hle. apply Lists.mem_iff in Hle.
      pose proof (proj1 (well_formed_at R H w v Hw Hle)) as Hv.
      specialize (Himp v Hle). apply IHB; [exact Hv |].
      apply IHA in HA; [| exact Hv]. rewrite HA in Himp. exact Himp.
    + intros Himp v Hv. pose proof (proj1 (well_formed_at R H w v Hw Hv)) as Hs.
      destruct (nth v (forced A) false) eqn:E; [| reflexivity]. cbn.
      apply IHB; [exact Hs |]. apply Himp; [unfold le; apply Lists.mem_iff; exact Hv |].
      apply IHA; [exact Hs | exact E].
Qed.

End Check.

Arguments finite_model atom : clear implicits.

(** A finite model that [refutes] accepts shows the sequent underivable. *)
Theorem kripke_refutation : forall {atom} (atom_eqb : atom -> atom -> bool),
  (forall a b, reflect (a = b) (atom_eqb a b)) ->
  forall R M w G C, refutes atom_eqb M R w G C = true -> ~ lj R G C.
Proof.
  intros atom atom_eqb spec R M w G C H.
  unfold refutes in H. repeat rewrite andb_true_iff in H.
  destruct H as [[[Hwf Hw] HG] HC]. apply Nat.ltb_lt in Hw.
  apply (kripke_countermodel nat (le M) (val atom_eqb M) (abs M) R
           (well_formed_model atom_eqb M spec R Hwf) G C w).
  - apply Forall_forall. intros A HA. rewrite forallb_forall in HG.
    apply (forced_forces atom_eqb M R Hwf A w Hw). exact (HG A HA).
  - rewrite <- (forced_forces atom_eqb M R Hwf C w Hw).
    apply negb_true_iff in HC. rewrite HC. discriminate.
Qed.
