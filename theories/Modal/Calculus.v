(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * The labelled sequent calculus G3K and its frame rules

    [g3 C L Rt] says that the labelled sequent [L ⊢ Rt] has a derivation
    in the labelled calculus of the system of [C]: Negri's G3K ("Proof
    analysis in modal logic", Journal of Philosophical Logic 34, 2005,
    Table II) with the frame rule of every condition of [C] (Ref, Ser,
    Sym, Trans and Eucl, p. 515 there). These are the rules of deduxit's
    calculi [G3K] to [G3S5], rule for rule.

    The calculus differs from Negri's table in these points:
    - every rule keeps its principal formula in its premises, so a
      premise is its conclusion with the rule's new items added;
    - the axiom [ax] closes on any formula, not only an atom;
    - [¬], [⊤] and [↔] have rules of their own;
    - a relational atom is never principal on the right.

    A sequent is two lists read as sets: a rule asks only which items a
    list holds, never where or how often. The rules [box_r], [dia_l] and
    [ser] bring in a label [y] that the conclusion does not mention
    ([fresh]). In [ser] the label [x] that sees it is any label, as in
    deduxit's rule: also one the conclusion does not mention, and [y]
    itself. [g3 C L Rt] is a [Prop]: it says that a derivation
    exists. *)

From Stdlib Require Import List String.
From Deduxit.Modal Require Export Labelled.
Import ListNotations.

Section Calculus.

Context {atom : Type}.
Local Notation formula := (formula atom).
Local Notation item := (item atom).

(** The item [i] mentions the label [y]. *)
Definition mentions (y : label) (i : item) : Prop :=
  match i with
  | lab x _ => x = y
  | rel x z => x = y \/ z = y
  end.

(** No item of the sequent [L ⊢ Rt] mentions the label [y]. *)
Definition fresh (y : label) (L Rt : list item) : Prop :=
  forall i, In i (L ++ Rt) -> ~ mentions y i.

(** The derivable labelled sequents [L ⊢ Rt] of the system of [C]. *)
Inductive g3 (C : conditions) : list item -> list item -> Prop :=
| ax : forall x A L Rt,
    In (lab x A) L -> In (lab x A) Rt -> g3 C L Rt
| bot_l : forall x L Rt,
    In (lab x bot) L -> g3 C L Rt
| top_r : forall x L Rt,
    In (lab x top) Rt -> g3 C L Rt
| neg_l : forall x A L Rt,
    In (lab x (neg A)) L ->
    g3 C L (lab x A :: Rt) -> g3 C L Rt
| neg_r : forall x A L Rt,
    In (lab x (neg A)) Rt ->
    g3 C (lab x A :: L) Rt -> g3 C L Rt
| wedge_l : forall x A B L Rt,
    In (lab x (wedge A B)) L ->
    g3 C (lab x A :: lab x B :: L) Rt -> g3 C L Rt
| wedge_r : forall x A B L Rt,
    In (lab x (wedge A B)) Rt ->
    g3 C L (lab x A :: Rt) -> g3 C L (lab x B :: Rt) -> g3 C L Rt
| vee_l : forall x A B L Rt,
    In (lab x (vee A B)) L ->
    g3 C (lab x A :: L) Rt -> g3 C (lab x B :: L) Rt -> g3 C L Rt
| vee_r : forall x A B L Rt,
    In (lab x (vee A B)) Rt ->
    g3 C L (lab x A :: lab x B :: Rt) -> g3 C L Rt
| imp_l : forall x A B L Rt,
    In (lab x (imp A B)) L ->
    g3 C L (lab x A :: Rt) -> g3 C (lab x B :: L) Rt -> g3 C L Rt
| imp_r : forall x A B L Rt,
    In (lab x (imp A B)) Rt ->
    g3 C (lab x A :: L) (lab x B :: Rt) -> g3 C L Rt
| equiv_l : forall x A B L Rt,
    In (lab x (equiv A B)) L ->
    g3 C (lab x A :: lab x B :: L) Rt ->
    g3 C L (lab x A :: lab x B :: Rt) -> g3 C L Rt
| equiv_r : forall x A B L Rt,
    In (lab x (equiv A B)) Rt ->
    g3 C (lab x A :: L) (lab x B :: Rt) ->
    g3 C (lab x B :: L) (lab x A :: Rt) -> g3 C L Rt
| box_l : forall x y A L Rt,
    In (lab x (box A)) L -> In (rel x y) L ->
    g3 C (lab y A :: L) Rt -> g3 C L Rt
| box_r : forall x y A L Rt,
    In (lab x (box A)) Rt -> fresh y L Rt ->
    g3 C (rel x y :: L) (lab y A :: Rt) -> g3 C L Rt
| dia_l : forall x y A L Rt,
    In (lab x (dia A)) L -> fresh y L Rt ->
    g3 C (rel x y :: lab y A :: L) Rt -> g3 C L Rt
| dia_r : forall x y A L Rt,
    In (lab x (dia A)) Rt -> In (rel x y) L ->
    g3 C L (lab y A :: Rt) -> g3 C L Rt
| ref : reflexive C = true -> forall x L Rt,
    g3 C (rel x x :: L) Rt -> g3 C L Rt
| ser : serial C = true -> forall x y L Rt,
    fresh y L Rt ->
    g3 C (rel x y :: L) Rt -> g3 C L Rt
| sym : symmetric C = true -> forall x y L Rt,
    In (rel x y) L ->
    g3 C (rel y x :: L) Rt -> g3 C L Rt
| trans : transitive C = true -> forall x y z L Rt,
    In (rel x y) L -> In (rel y z) L ->
    g3 C (rel x z :: L) Rt -> g3 C L Rt
| eucl : euclidean C = true -> forall x y z L Rt,
    In (rel x y) L -> In (rel x z) L ->
    g3 C (rel y z :: L) Rt -> g3 C L Rt.

End Calculus.
