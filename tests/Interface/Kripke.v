(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** The interface of deduxit's certificates that a sequent of
    intuitionistic or minimal logic is not valid, by a finite Kripke
    model: under the prelude deduxit writes, every name a certificate
    uses, at the type and with the arguments it is used with. *)

From Stdlib Require Import List String.
From Deduxit.Intuitionistic Require Import KripkeCheck.
Import ListNotations.
Open Scope string_scope.

(** The formulas, every constructor, and the connectives defined from
    them. *)
Definition formulas (a : string) A B :=
  [var a; bot; wedge A B; vee A B; imp A B; top; neg A; equiv A B].

Definition calculi := [intuitionistic; minimal].

Definition a_model : finite_model string :=
  {| later := [[1]; []]; atoms := [[]; ["a"]]; absurd := [] |}.

(** The theorem, applied as a certificate applies it. *)
Definition by_model R M w Γ C :
  _ = true -> ~ lj (atom := string) R Γ C :=
  kripke_refutation String.eqb String.eqb_spec R M w Γ C.
