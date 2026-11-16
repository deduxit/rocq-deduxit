(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * Kripke models and validity

    This file is what a certificate's statement rests on: read it to
    know what such a certificate claims. [valid C Γ Δ] says that the
    sequent [Γ ⊢ Δ] holds in every Kripke model whose frame meets the
    conditions [C]: a world that forces every formula of [Γ] forces one
    of [Δ].

    A Kripke model is a type of worlds, a relation [R] between them,
    read "sees", and a valuation [V] that says which atoms hold at each
    world. A modal system is the logic of the frames that meet some of
    five conditions on [R]; [conditions] says which, and [System] names
    the fifteen systems they give, from K to S5.

    The logic is classical, so [valid] speaks of the models whose
    forcing is stable under double negation ([stable]), as Doczkal and
    Smolka do ("Constructive completeness for modal logic with
    transitive closure", CPP 2012, section 2). With the law of excluded
    middle every model is one. Without it not every model is: [p ∨ ¬p]
    is forced only where the proposition [V w p] is decided.

    The file derives nothing and assumes nothing. *)

From Stdlib Require Import List.
From Deduxit.Modal Require Export Formulas.
Import ListNotations.

(** The conditions a system puts on the relation of its frames. *)
Record conditions : Type := Conditions {
  serial : bool;      (** every world sees some world *)
  reflexive : bool;   (** every world sees itself *)
  symmetric : bool;   (** a world seen sees back *)
  transitive : bool;  (** a world sees what the worlds it sees see *)
  euclidean : bool;   (** two worlds seen from one see each other *)
}.

(** The fifteen systems. Each holds every condition that follows, on
    every frame, from those it is named after: a reflexive relation is
    serial, and a reflexive and euclidean one is symmetric and
    transitive. So two systems with the same frames are the same
    value. *)
Module System.

(** K: every frame. *)
Definition K : conditions :=
  {| serial := false; reflexive := false; symmetric := false;
     transitive := false; euclidean := false |}.

(** D, also written KD: the serial frames. *)
Definition D : conditions :=
  {| serial := true; reflexive := false; symmetric := false;
     transitive := false; euclidean := false |}.

(** T: the reflexive frames. *)
Definition T : conditions :=
  {| serial := true; reflexive := true; symmetric := false;
     transitive := false; euclidean := false |}.

(** KB: the symmetric frames. *)
Definition KB : conditions :=
  {| serial := false; reflexive := false; symmetric := true;
     transitive := false; euclidean := false |}.

(** KDB: the serial and symmetric frames. *)
Definition KDB : conditions :=
  {| serial := true; reflexive := false; symmetric := true;
     transitive := false; euclidean := false |}.

(** B: the reflexive and symmetric frames. *)
Definition B : conditions :=
  {| serial := true; reflexive := true; symmetric := true;
     transitive := false; euclidean := false |}.

(** K4: the transitive frames. *)
Definition K4 : conditions :=
  {| serial := false; reflexive := false; symmetric := false;
     transitive := true; euclidean := false |}.

(** KD4: the serial and transitive frames. *)
Definition KD4 : conditions :=
  {| serial := true; reflexive := false; symmetric := false;
     transitive := true; euclidean := false |}.

(** S4: the reflexive and transitive frames. *)
Definition S4 : conditions :=
  {| serial := true; reflexive := true; symmetric := false;
     transitive := true; euclidean := false |}.

(** K5: the euclidean frames. *)
Definition K5 : conditions :=
  {| serial := false; reflexive := false; symmetric := false;
     transitive := false; euclidean := true |}.

(** KD5: the serial and euclidean frames. *)
Definition KD5 : conditions :=
  {| serial := true; reflexive := false; symmetric := false;
     transitive := false; euclidean := true |}.

(** K45: the transitive and euclidean frames. *)
Definition K45 : conditions :=
  {| serial := false; reflexive := false; symmetric := false;
     transitive := true; euclidean := true |}.

(** KD45: the serial, transitive and euclidean frames. *)
Definition KD45 : conditions :=
  {| serial := true; reflexive := false; symmetric := false;
     transitive := true; euclidean := true |}.

(** KB5, also written KB4: the symmetric and transitive frames, which
    are euclidean too. *)
Definition KB5 : conditions :=
  {| serial := false; reflexive := false; symmetric := true;
     transitive := true; euclidean := true |}.

(** S5: the frames whose relation is an equivalence. *)
Definition S5 : conditions :=
  {| serial := true; reflexive := true; symmetric := true;
     transitive := true; euclidean := true |}.

End System.

Section Kripke.

Context {atom : Type}.
Local Notation formula := (formula atom).

Variable world : Type.
Variable R : world -> world -> Prop.
Variable V : world -> atom -> Prop.

(** The relation [R] meets every condition of [C]. *)
Record frame (C : conditions) : Prop := {
  frame_serial : serial C = true -> forall x, exists y, R x y;
  frame_reflexive : reflexive C = true -> forall x, R x x;
  frame_symmetric : symmetric C = true -> forall x y, R x y -> R y x;
  frame_transitive : transitive C = true ->
    forall x y z, R x y -> R y z -> R x z;
  frame_euclidean : euclidean C = true ->
    forall x y z, R x y -> R x z -> R y z;
}.

(** The world [w] forces the formula [A]: [A] is true there. *)
Fixpoint forces (w : world) (A : formula) : Prop :=
  match A with
  | var a => V w a
  | top => True
  | bot => False
  | neg A => ~ forces w A
  | wedge A B => forces w A /\ forces w B
  | vee A B => forces w A \/ forces w B
  | imp A B => forces w A -> forces w B
  | equiv A B => forces w A <-> forces w B
  | box A => forall v, R w v -> forces v A
  | dia A => exists v, R w v /\ forces v A
  end.

(** Forcing is stable under double negation: a formula that is not
    false at a world is true there. *)
Definition stable : Prop := forall w A, ~ ~ forces w A -> forces w A.

End Kripke.

Arguments frame {world} R C.
Arguments forces {atom world} R V w A.
Arguments stable {atom world} R V.

(** The sequent [Γ ⊢ Δ] is valid in the system of [C]: in every model
    with stable forcing whose frame meets [C], a world that forces every
    formula of [Γ] forces one of [Δ]. *)
Definition valid {atom : Type} (C : conditions) (Γ Δ : list (formula atom)) : Prop :=
  forall (world : Type) (R : world -> world -> Prop) (V : world -> atom -> Prop),
    frame R C -> stable R V ->
    forall w, Forall (forces R V w) Γ -> Exists (forces R V w) Δ.
