(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * Kripke models and their soundness

    A Kripke model is a set of worlds with a preorder [le], read "later
    than or equal to", a valuation [val] that says which atoms each
    world forces, and the set [absurd] of worlds that force [⊥]. Both
    are monotone: what a world forces, every later world forces too. In
    intuitionistic logic no world forces [⊥]; in minimal logic [⊥] is
    one more atom.

    [kripke_soundness] says that every derivable sequent holds in every
    model: a world that forces the hypotheses forces the conclusion. So
    a model with a world that forces the hypotheses and not the
    conclusion shows the sequent underivable ([kripke_countermodel]),
    with cut or without. The model with one world is an assignment of
    truth values, which gives [classical_refutation]: a sequent false
    under some assignment is underivable. *)

From Stdlib Require Import List Permutation Bool.
From Deduxit.Intuitionistic Require Export Calculus.
Import ListNotations.

Section Kripke.

Context {atom : Type}.
Local Notation formula := (formula atom).

Variable world : Type.
Variable le : world -> world -> Prop.
Variable val : world -> atom -> Prop.
Variable absurd : world -> Prop.

(** [le], [val] and [absurd] make a Kripke model of the logic of [R]. *)
Record model (R : rules) : Prop := {
  model_refl : forall w, le w w;
  model_trans : forall u v w, le u v -> le v w -> le u w;
  model_val : forall w v a, le w v -> val w a -> val v a;
  model_absurd : forall w v, le w v -> absurd w -> absurd v;
  model_explosion : explosion R = true -> forall w, ~ absurd w;
}.

(** The world [w] forces the formula [A]. *)
Fixpoint forces (w : world) (A : formula) : Prop :=
  match A with
  | var a => val w a
  | bot => absurd w
  | wedge A B => forces w A /\ forces w B
  | vee A B => forces w A \/ forces w B
  | imp A B => forall v, le w v -> forces v A -> forces v B
  end.

Variable R : rules.
Hypothesis M : model R.

(** What a world forces, every later world forces. *)
Lemma persistence : forall A w v, le w v -> forces w A -> forces v A.
Proof.
  induction A as [a | | A IHA B IHB | A IHA B IHB | A IHA B IHB];
    intros w v Hle H; cbn in *.
  - exact (model_val _ M _ _ _ Hle H).
  - exact (model_absurd _ M _ _ Hle H).
  - destruct H as [HA HB]. split; [exact (IHA _ _ Hle HA) | exact (IHB _ _ Hle HB)].
  - destruct H as [HA | HB]; [left; exact (IHA _ _ Hle HA) | right; exact (IHB _ _ Hle HB)].
  - intros u Hvu HA. exact (H u (model_trans _ M _ _ _ Hle Hvu) HA).
Qed.

(** Every derivable sequent holds at every world of the model. *)
Theorem kripke_soundness : forall G C, lj R G C ->
  forall w, Forall (forces w) G -> forces w C.
Proof.
  intros G C D. induction D as [A | l1 l2 C D IHD Hp | A l C D IHD | A l C D IHD
    | Hexp C | A B l D1 IHD1 D2 IHD2 | A B l C D IHD | A B l D IHD | A B l D IHD
    | A B l C D1 IHD1 D2 IHD2 | A B l D IHD | A B l C D1 IHD1 D2 IHD2
    | Hcut A l C D1 IHD1 D2 IHD2]; intros w HG.
  - apply Forall_cons_iff in HG as [HA _]. exact HA.
  - apply IHD. apply Forall_forall. intros x Hx.
    eapply Forall_forall; [exact HG |]. apply Permutation_in with l1; assumption.
  - apply Forall_cons_iff in HG as [_ Hl]. exact (IHD w Hl).
  - apply Forall_cons_iff in HG as [HA Hl]. apply IHD. repeat constructor; assumption.
  - apply Forall_cons_iff in HG as [Hbot _]. cbn in Hbot.
    exfalso. exact (model_explosion _ M Hexp w Hbot).
  - split; [exact (IHD1 w HG) | exact (IHD2 w HG)].
  - apply Forall_cons_iff in HG as [[HA HB] Hl]. apply IHD. repeat constructor; assumption.
  - left. exact (IHD w HG).
  - right. exact (IHD w HG).
  - apply Forall_cons_iff in HG as [[HA | HB] Hl].
    + apply IHD1. constructor; assumption.
    + apply IHD2. constructor; assumption.
  - intros v Hle HA. apply IHD. constructor; [exact HA |].
    eapply Forall_impl; [| exact HG]. intros x. apply persistence. exact Hle.
  - apply Forall_cons_iff in HG as [Himp Hl]. apply IHD2. constructor; [| exact Hl].
    exact (Himp w (model_refl _ M w) (IHD1 w Hl)).
  - apply IHD2. constructor; [exact (IHD1 w HG) | exact HG].
Qed.

(** A world that forces the hypotheses and not the conclusion shows the
    sequent underivable. *)
Theorem kripke_countermodel : forall G C w,
  Forall (forces w) G -> ~ forces w C -> ~ lj R G C.
Proof.
  intros G C w HG HC D. exact (HC (kripke_soundness G C D w HG)).
Qed.

End Kripke.

Arguments model {atom} world le val absurd R.
Arguments forces {atom world} le val absurd w A.

Section Classical.

Context {atom : Type}.
Local Notation formula := (formula atom).

(** The truth value of a formula under an assignment [v] of the atoms,
    [⊥] false. *)
Fixpoint eval (v : atom -> bool) (A : formula) : bool :=
  match A with
  | var a => v a
  | bot => false
  | wedge A B => eval v A && eval v B
  | vee A B => eval v A || eval v B
  | imp A B => implb (eval v A) (eval v B)
  end.

(** The model with one world, forcing exactly the true atoms. *)
Lemma forces_eval : forall v A,
  forces (world := unit) (fun _ _ => True) (fun _ a => v a = true) (fun _ => False) tt A
  <-> eval v A = true.
Proof.
  intros v A. induction A as [a | | A IHA B IHB | A IHA B IHB | A IHA B IHB]; cbn.
  - reflexivity.
  - split; [intros [] | discriminate].
  - rewrite andb_true_iff, IHA, IHB. reflexivity.
  - rewrite orb_true_iff, IHA, IHB. reflexivity.
  - rewrite implb_true_iff, <- IHA, <- IHB. split.
    + intros H HA. exact (H tt I HA).
    + intros H [] _ HA. exact (H HA).
Qed.

(** A sequent whose hypotheses an assignment makes true and whose
    conclusion it makes false is underivable, in LJ and LM, with cut or
    without. *)
Theorem classical_refutation : forall R v G C,
  forallb (eval v) G && negb (eval v C) = true -> ~ lj R G C.
Proof.
  intros R v G C H. apply andb_true_iff in H as [HG HC].
  apply (kripke_countermodel unit (fun _ _ => True) (fun _ a => v a = true)
           (fun _ => False) R) with tt.
  - split; auto.
  - apply Forall_forall. intros A HA. apply forces_eval.
    apply forallb_forall with (x := A) in HG; assumption.
  - rewrite forces_eval. apply negb_true_iff in HC. rewrite HC. discriminate.
Qed.

End Classical.
