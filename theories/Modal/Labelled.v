(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * Labelled sequents and their validity

    A labelled sequent speaks of several worlds at once. A label names a
    world; a sequent holds labelled formulas [x : A], "[A] is true at
    [x]", and relational atoms [x R y], "[x] sees [y]".

    With [Formulas.v] and [Kripke.v], this file is what a certificate of
    a labelled sequent rests on. [lvalid C L Rt] says that the sequent
    [L ⊢ Rt] holds in every model of the system of [C], wherever its
    labels are placed: when every item of [L] is true, the items of [Rt]
    are not all false. With the law of excluded middle that is "one item
    of [Rt] is true". The two items may be at different worlds, and
    without that law stable forcing does not give one of them from "not
    both false"; for a sequent at one label it does, which is [valid].

    The file derives nothing and assumes nothing. *)

From Stdlib Require Import List String.
From Deduxit.Modal Require Export Kripke.
Import ListNotations.

(** A label: the name of a world. *)
Definition label : Type := string.

Section Labelled.

Context {atom : Type}.

(** What a labelled sequent holds. *)
Inductive item : Type :=
| lab : label -> formula atom -> item   (** [x : A]: [A] is true at [x] *)
| rel : label -> label -> item.    (** [x R y]: [x] sees [y] *)

Variable world : Type.
Variable R : world -> world -> Prop.
Variable V : world -> atom -> Prop.

(** The item [i] is true when each label [x] names the world [ρ x]. *)
Definition holds (ρ : label -> world) (i : item) : Prop :=
  match i with
  | lab x A => forces R V (ρ x) A
  | rel x y => R (ρ x) (ρ y)
  end.

End Labelled.

Arguments item atom : clear implicits.
Arguments holds {atom world} R V ρ i.

(** The labelled sequent [L ⊢ Rt] is valid in the system of [C]: in
    every model with stable forcing whose frame meets [C], and for every
    placing [ρ] of the labels, when every item of [L] is true the items
    of [Rt] are not all false. *)
Definition lvalid {atom : Type} (C : conditions) (L Rt : list (item atom)) : Prop :=
  forall (world : Type) (R : world -> world -> Prop) (V : world -> atom -> Prop),
    frame R C -> stable R V ->
    forall ρ : label -> world,
      Forall (holds R V ρ) L -> ~ Forall (fun i => ~ holds R V ρ i) Rt.
