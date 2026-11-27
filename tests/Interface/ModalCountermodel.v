(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** The interface of deduxit's certificates that a modal sequent is not
    valid, by a finite model: under the prelude deduxit writes, every
    name a certificate uses, at the type and with the arguments it is
    used with. *)

From Stdlib Require Import List String.
From Deduxit.Modal Require Import Countermodel.
Import ListNotations.
Open Scope string_scope.

Definition formulas (a : string) A B :=
  [var a; top; bot; neg A; wedge A B; vee A B; imp A B; equiv A B; box A;
   dia A].

Definition conditions_of serial reflexive symmetric transitive euclidean :=
  {| serial := serial; reflexive := reflexive; symmetric := symmetric;
     transitive := transitive; euclidean := euclidean |}.

Definition a_model : model string := {| arrows := [[0]]; atoms := [[]] |}.

(** The theorem, applied as a certificate applies it. *)
Definition by_model M C w Γ Δ :
  _ = true -> ~ valid (atom := string) C Γ Δ :=
  modal_refutation String.eqb M C w Γ Δ.
