(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * Soundness of the labelled calculus for Kripke semantics

    [g3_sound] says that every sequent the labelled calculus of a
    system derives is valid in the system's frames: [g3 C L Rt] gives
    [lvalid C L Rt]. [lvalid_valid] reads a sequent at one label as an
    ordinary sequent, so a derivation of [x : Γ ⊢ x : Δ] shows [Γ ⊢ Δ]
    valid ([g3_valid]).

    The proof is by induction on the derivation, inside one model: no
    placing of the labels makes every item on the left true and every
    item on the right false. A rule with a new label moves that label to
    the world the rule needs and leaves every other label where it was.
    [wedge_r], [imp_r], [equiv_r] and [box_r] are the cases that use
    stable forcing.

    One instance of [ser] needs a second model: a new label that sees
    itself. A serial frame may have no such world, so the proof adds one
    beside the model, seen by no other world ([beside_R]); the new model
    is one of the system too, and forces at the old worlds what the old
    one did. *)

From Stdlib Require Import List String.
From Deduxit.Modal Require Export Calculus.
Import ListNotations.

Section Soundness.

Context {atom : Type}.

Section Placing.

Variable world : Type.
Variable R : world -> world -> Prop.
Variable V : world -> atom -> Prop.

(** The placing [ρ] with the label [y] moved to the world [v]. *)
Definition update (ρ : label -> world) (y : label) (v : world) : label -> world :=
  fun z => if String.eqb z y then v else ρ z.

Lemma update_same : forall ρ y v, update ρ y v y = v.
Proof.
  intros ρ y v. unfold update. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma update_other : forall ρ y v z, z <> y -> update ρ y v z = ρ z.
Proof.
  intros ρ y v z H. unfold update.
  destruct (String.eqb_spec z y); [contradiction | reflexivity].
Qed.

(** Moving a label changes no item that does not mention it. *)
Lemma holds_update : forall ρ y v (i : item atom),
  ~ mentions y i -> (holds R V (update ρ y v) i <-> holds R V ρ i).
Proof.
  intros ρ y v [x A | x z] H; unfold holds.
  - rewrite (update_other ρ y v x H). reflexivity.
  - assert (Hx : x <> y) by (intro E; apply H; left; exact E).
    assert (Hz : z <> y) by (intro E; apply H; right; exact E).
    rewrite (update_other ρ y v x Hx), (update_other ρ y v z Hz). reflexivity.
Qed.

Lemma sat_update : forall ρ y v (L Rt : list (item atom)),
  fresh y L Rt -> Forall (holds R V ρ) L ->
  Forall (holds R V (update ρ y v)) L.
Proof.
  intros ρ y v L Rt Hf HL. apply Forall_forall. intros i Hi.
  apply (proj2 (holds_update ρ y v i (Hf i (in_or_app _ _ _ (or_introl Hi))))).
  exact (proj1 (Forall_forall _ _) HL i Hi).
Qed.

Lemma unsat_update : forall ρ y v (L Rt : list (item atom)),
  fresh y L Rt -> Forall (fun i => ~ holds R V ρ i) Rt ->
  Forall (fun i => ~ holds R V (update ρ y v) i) Rt.
Proof.
  intros ρ y v L Rt Hf HR. apply Forall_forall. intros i Hi Hh.
  apply (proj1 (Forall_forall _ _) HR i Hi).
  exact (proj1 (holds_update ρ y v i (Hf i (in_or_app _ _ _ (or_intror Hi)))) Hh).
Qed.

End Placing.

Arguments update {world} ρ y v.
Arguments update_same {world} ρ y v.
Arguments update_other {world} ρ y v z _.

Section Beside.

Variable world : Type.
Variable R : world -> world -> Prop.
Variable V : world -> atom -> Prop.

(** The model with one more world, [None], which sees itself and
    nothing else, is seen by no other world and makes no atom true. *)
Definition beside_R (a b : option world) : Prop :=
  match a, b with
  | Some u, Some v => R u v
  | None, None => True
  | _, _ => False
  end.

Definition beside_V (a : option world) (p : atom) : Prop :=
  match a with
  | Some u => V u p
  | None => False
  end.

Lemma beside_frame : forall C, frame R C -> frame beside_R C.
Proof.
  intros C HF. split; intro Hc.
  - intros [u |].
    + destruct (frame_serial _ _ _ HF Hc u) as [v Hv]. exists (Some v). exact Hv.
    + exists None. exact I.
  - intros [u |]; [exact (frame_reflexive _ _ _ HF Hc u) | exact I].
  - intros [u |] [v |] H; try exact H.
    exact (frame_symmetric _ _ _ HF Hc u v H).
  - intros [u |] [v |] [w |] H1 H2; cbn in *; try exact I; try contradiction.
    exact (frame_transitive _ _ _ HF Hc u v w H1 H2).
  - intros [u |] [v |] [w |] H1 H2; cbn in *; try exact I; try contradiction.
    exact (frame_euclidean _ _ _ HF Hc u v w H1 H2).
Qed.

(** An old world forces what it forced. *)
Lemma beside_forces : forall (A : formula atom) u,
  forces beside_R beside_V (Some u) A <-> forces R V u A.
Proof.
  intros A; induction A as [a | | | A IHA | A IHA B IHB | A IHA B IHB | A IHA B IHB
    | A IHA B IHB | A IHA | A IHA]; intros u; cbn [forces beside_V];
    try (pose proof (IHA u) as IHAu); try (pose proof (IHB u) as IHBu);
    try tauto.
  - split.
    + intros H v Hv. exact (proj1 (IHA v) (H (Some v) Hv)).
    + intros H [v |] Hv; [exact (proj2 (IHA v) (H v Hv)) | destruct Hv].
  - split.
    + intros [[v |] [Hv HA]]; [| destruct Hv].
      exists v. split; [exact Hv | exact (proj1 (IHA v) HA)].
    + intros [v [Hv HA]]. exists (Some v). split; [exact Hv |].
      exact (proj2 (IHA v) HA).
Qed.

(** The new world decides every formula: it sees itself alone. *)
Lemma beside_decided : forall A : formula atom,
  forces beside_R beside_V None A \/ ~ forces beside_R beside_V None A.
Proof.
  intros A; induction A as [a | | | A IHA | A IHA B IHB | A IHA B IHB | A IHA B IHB
    | A IHA B IHB | A IHA | A IHA]; cbn [forces beside_V]; try tauto.
  - destruct IHA as [H | H].
    + left. intros [v |] Hv; [destruct Hv | exact H].
    + right. intro H'. exact (H (H' None I)).
  - destruct IHA as [H | H].
    + left. exists None. split; [exact I | exact H].
    + right. intros [[v |] [Hv HA]]; [destruct Hv | exact (H HA)].
Qed.

Lemma beside_stable : stable R V -> stable beside_R beside_V.
Proof.
  intros HS [u |] A H.
  - apply (proj2 (beside_forces A u)). apply HS. intro Hn. apply H.
    intro HA. exact (Hn (proj1 (beside_forces A u) HA)).
  - destruct (beside_decided A) as [HA | HA]; [exact HA | contradiction].
Qed.

(** The placing [ρ] in the new model, with the label [y] at the new
    world. *)
Definition aside (ρ : label -> world) (y : label) : label -> option world :=
  fun z => if String.eqb z y then None else Some (ρ z).

Lemma holds_aside : forall ρ y (i : item atom),
  ~ mentions y i ->
  (holds beside_R beside_V (aside ρ y) i <-> holds R V ρ i).
Proof.
  intros ρ y [x A | x z] H; unfold holds, aside.
  - destruct (String.eqb_spec x y) as [E | _]; [contradiction |].
    apply beside_forces.
  - destruct (String.eqb_spec x y) as [E | _]; [exfalso; apply H; left; exact E |].
    destruct (String.eqb_spec z y) as [E | _]; [exfalso; apply H; right; exact E |].
    reflexivity.
Qed.

End Beside.

(** No placing of the labels makes the left of a derivable sequent true
    and its right false. *)
Lemma g3_model : forall C (L Rt : list (item atom)), g3 C L Rt ->
  forall world (R : world -> world -> Prop) (V : world -> atom -> Prop),
    frame R C -> stable R V ->
    forall ρ, Forall (holds R V ρ) L -> ~ Forall (fun i => ~ holds R V ρ i) Rt.
Proof.
  intros C L Rt D.
  induction D as [x A L Rt Hl Hr | x L Rt Hl | x L Rt Hr
    | x A L Rt Hl D IHD | x A L Rt Hr D IHD
    | x A B L Rt Hl D IHD | x A B L Rt Hr D1 IHD1 D2 IHD2
    | x A B L Rt Hl D1 IHD1 D2 IHD2 | x A B L Rt Hr D IHD
    | x A B L Rt Hl D1 IHD1 D2 IHD2 | x A B L Rt Hr D IHD
    | x A B L Rt Hl D1 IHD1 D2 IHD2 | x A B L Rt Hr D1 IHD1 D2 IHD2
    | x y A L Rt Hl He D IHD | x y A L Rt Hr Hf D IHD
    | x y A L Rt Hl Hf D IHD | x y A L Rt Hr He D IHD
    | Hc x L Rt D IHD | Hc x y L Rt Hf D IHD | Hc x y L Rt He D IHD
    | Hc x y z L Rt H1 H2 D IHD | Hc x y z L Rt H1 H2 D IHD];
    intros world R V HF HS ρ HL HR;
    pose proof (proj1 (Forall_forall _ _) HL) as InL;
    pose proof (proj1 (Forall_forall _ _) HR) as InR;
    try (pose proof IHD as IHall; specialize (IHD world R V HF HS));
    try specialize (IHD1 world R V HF HS);
    try specialize (IHD2 world R V HF HS).
  - (* ax *)
    exact (InR _ Hr (InL _ Hl)).
  - (* bot_l *)
    exact (InL _ Hl).
  - (* top_r *)
    exact (InR _ Hr I).
  - (* neg_l *)
    apply (IHD ρ HL). constructor; [exact (InL _ Hl) | exact HR].
  - (* neg_r *)
    apply (InR _ Hr). intro HA.
    apply (IHD ρ); [constructor; [exact HA | exact HL] | exact HR].
  - (* wedge_l *)
    destruct (InL _ Hl) as [HA HB].
    apply (IHD ρ); [| exact HR].
    constructor; [exact HA | constructor; [exact HB | exact HL]].
  - (* wedge_r *)
    apply (InR _ Hr). split; apply HS; intro Hn.
    + apply (IHD1 ρ HL). constructor; [exact Hn | exact HR].
    + apply (IHD2 ρ HL). constructor; [exact Hn | exact HR].
  - (* vee_l *)
    destruct (InL _ Hl) as [HA | HB].
    + apply (IHD1 ρ); [constructor; [exact HA | exact HL] | exact HR].
    + apply (IHD2 ρ); [constructor; [exact HB | exact HL] | exact HR].
  - (* vee_r *)
    apply (IHD ρ HL).
    constructor; [| constructor; [| exact HR]]; intro H; apply (InR _ Hr).
    + left. exact H.
    + right. exact H.
  - (* imp_l *)
    apply (IHD1 ρ HL). constructor; [| exact HR]. intro HA.
    apply (IHD2 ρ); [constructor; [exact (InL _ Hl HA) | exact HL] | exact HR].
  - (* imp_r *)
    apply (InR _ Hr). intro HA. apply HS. intro Hn.
    apply (IHD ρ); constructor; assumption.
  - (* equiv_l *)
    destruct (InL _ Hl) as [Hab Hba]. apply (IHD2 ρ HL).
    constructor; [| constructor; [| exact HR]]; intro H; apply (IHD1 ρ);
      try exact HR.
    + constructor; [exact H | constructor; [exact (Hab H) | exact HL]].
    + constructor; [exact (Hba H) | constructor; [exact H | exact HL]].
  - (* equiv_r *)
    apply (InR _ Hr). split; intro H; apply HS; intro Hn.
    + apply (IHD1 ρ); constructor; assumption.
    + apply (IHD2 ρ); constructor; assumption.
  - (* box_l *)
    apply (IHD ρ); [constructor; [| exact HL] | exact HR].
    exact (InL _ Hl (ρ y) (InL _ He)).
  - (* box_r *)
    apply (InR _ Hr). intros v Hv. apply HS. intro Hn.
    assert (Hx : x <> y).
    { intro E. exact (Hf _ (in_or_app _ _ _ (or_intror Hr)) E). }
    apply (IHD (update ρ y v)).
    + constructor; [| exact (sat_update world R V ρ y v L Rt Hf HL)].
      unfold holds. rewrite update_same, (update_other ρ y v x Hx). exact Hv.
    + constructor; [| exact (unsat_update world R V ρ y v L Rt Hf HR)].
      unfold holds. rewrite update_same. exact Hn.
  - (* dia_l *)
    destruct (InL _ Hl) as [v [Hv HA]].
    assert (Hx : x <> y).
    { intro E. exact (Hf _ (in_or_app _ _ _ (or_introl Hl)) E). }
    apply (IHD (update ρ y v)); [| exact (unsat_update world R V ρ y v L Rt Hf HR)].
    constructor; [| constructor; [| exact (sat_update world R V ρ y v L Rt Hf HL)]];
      unfold holds.
    + rewrite update_same, (update_other ρ y v x Hx). exact Hv.
    + rewrite update_same. exact HA.
  - (* dia_r *)
    apply (IHD ρ HL). constructor; [| exact HR]. intro HA.
    apply (InR _ Hr). exists (ρ y). split; [exact (InL _ He) | exact HA].
  - (* ref *)
    apply (IHD ρ); [constructor; [| exact HL] | exact HR].
    exact (frame_reflexive _ _ _ HF Hc (ρ x)).
  - (* ser *)
    destruct (String.eqb_spec x y) as [-> | Hxy].
    + (* a new label that sees itself: the world beside the model *)
      apply (IHall (option world) (beside_R world R) (beside_V world V)
               (beside_frame world R C HF) (beside_stable world R V HS)
               (aside world ρ y)).
      * constructor.
        -- unfold holds, aside. rewrite String.eqb_refl. exact I.
        -- apply Forall_forall. intros i Hi.
           apply (proj2 (holds_aside world R V ρ y i
                           (Hf i (in_or_app _ _ _ (or_introl Hi))))).
           exact (InL i Hi).
      * apply Forall_forall. intros i Hi Hh. apply (InR i Hi).
        exact (proj1 (holds_aside world R V ρ y i
                        (Hf i (in_or_app _ _ _ (or_intror Hi)))) Hh).
    + destruct (frame_serial _ _ _ HF Hc (ρ x)) as [v Hv].
      apply (IHD (update ρ y v));
        [| exact (unsat_update world R V ρ y v L Rt Hf HR)].
      constructor; [| exact (sat_update world R V ρ y v L Rt Hf HL)].
      unfold holds. rewrite update_same, (update_other ρ y v x Hxy). exact Hv.
  - (* sym *)
    apply (IHD ρ); [constructor; [| exact HL] | exact HR].
    exact (frame_symmetric _ _ _ HF Hc _ _ (InL _ He)).
  - (* trans *)
    apply (IHD ρ); [constructor; [| exact HL] | exact HR].
    exact (frame_transitive _ _ _ HF Hc _ _ _ (InL _ H1) (InL _ H2)).
  - (* eucl *)
    apply (IHD ρ); [constructor; [| exact HL] | exact HR].
    exact (frame_euclidean _ _ _ HF Hc _ _ _ (InL _ H1) (InL _ H2)).
Qed.

(** Every sequent the calculus of a system derives is valid in the
    system's frames. *)
Theorem g3_sound : forall C (L Rt : list (item atom)), g3 C L Rt -> lvalid C L Rt.
Proof.
  intros C L Rt D world R V HF HS ρ.
  exact (g3_model C L Rt D world R V HF HS ρ).
Qed.

(** The disjunction of a list of formulas, [⊥] for none. *)
Fixpoint disjunction (Δ : list (formula atom)) : formula atom :=
  match Δ with
  | [] => bot
  | B :: Δ => vee B (disjunction Δ)
  end.

Lemma forces_disjunction : forall world R (V : world -> atom -> Prop) w Δ,
  forces R V w (disjunction Δ) <-> Exists (forces R V w) Δ.
Proof.
  intros world R V w Δ. induction Δ as [| B Δ IH]; cbn [disjunction forces].
  - split; [intros [] | intro H; inversion H].
  - split.
    + intros [H | H]; [apply Exists_cons_hd; exact H |].
      apply Exists_cons_tl. exact (proj1 IH H).
    + intro H. apply Exists_cons in H. destruct H as [H | H]; [left; exact H |].
      right. exact (proj2 IH H).
Qed.

(** A labelled sequent at one label is an ordinary sequent: where it is
    valid, so is the sequent of its formulas. Stable forcing turns "not
    all false" into "one true" here, through the disjunction of [Δ]. *)
Theorem lvalid_valid : forall C x (Γ Δ : list (formula atom)),
  lvalid C (map (lab x) Γ) (map (lab x) Δ) -> valid C Γ Δ.
Proof.
  intros C x Γ Δ H world R V HF HS w HG.
  apply (proj1 (forces_disjunction world R V w Δ)). apply HS. intro Hn.
  apply (H world R V HF HS (fun _ => w)).
  - apply Forall_forall. intros i Hi. apply in_map_iff in Hi as [A [<- HA]].
    exact (proj1 (Forall_forall _ _) HG A HA).
  - apply Forall_forall. intros i Hi Hh. apply in_map_iff in Hi as [B [<- HB]].
    apply Hn. apply (proj2 (forces_disjunction world R V w Δ)).
    apply Exists_exists. exists B. split; [exact HB | exact Hh].
Qed.

(** A derivation of [x : Γ ⊢ x : Δ] shows [Γ ⊢ Δ] valid. *)
Theorem g3_valid : forall C x (Γ Δ : list (formula atom)),
  g3 C (map (lab x) Γ) (map (lab x) Δ) -> valid C Γ Δ.
Proof.
  intros C x Γ Δ D. exact (lvalid_valid C x Γ Δ (g3_sound C _ _ D)).
Qed.

(** With the law of excluded middle every model has stable forcing, so
    [valid] and [lvalid] then speak of every model of the system. *)
Lemma excluded_middle_stable : (forall P : Prop, P \/ ~ P) ->
  forall world R (V : world -> atom -> Prop), stable R V.
Proof.
  intros EM world R V w A H.
  destruct (EM (forces R V w A)) as [HA | HA]; [exact HA | contradiction].
Qed.

End Soundness.
