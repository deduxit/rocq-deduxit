(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** The interface of deduxit's certificates that a sequent of linear
    logic has no proof: under the prelude deduxit writes, every name a
    certificate uses, at the type and with the arguments it is used
    with. The formulas and calculi are those of the one-sided and
    two-sided certificates (OneSided.v, TwoSided.v). *)

From Stdlib Require Import List String ZArith.
From Deduxit.Linear Require Import Weights.
Import ListNotations.
Open Scope string_scope.

Definition formulas (a : string) A B :=
  [var a; covar a; one; bot; top; zero; tens A B; parr A B; awith A B;
   aplus A B; oc A; wn A].

Definition iformulas (a : string) A B :=
  [ivar a; ione; itens A B; ilmap A B; itop; iwith A B; izero; iplus A B;
   ioc A].

Definition statements mix weakening l Γ C :=
  [~ ll (atom := string) classical l;
   ~ ll (atom := string) {| mix := mix; weakening := weakening; cut := false |} l;
   ~ ill (atom := string) intuitionistic Γ C;
   ~ ill (atom := string) affine Γ C].

(** The theorems, one-sided, applied as a certificate applies them: the
    calculus left to [apply], then the sequent. *)
Definition by_valuation (truths : list string) l :
  _ = true -> ~ ll (atom := string) classical l :=
  classical_refutation _ (fun a => existsb (String.eqb a) truths) l.

Definition by_balance (a : string) l :
  _ = true -> ~ ll (atom := string) classical l :=
  unbalanced_refutation String.eqb a _ l.

Definition by_equation l :
  _ = true -> ~ ll (atom := string) classical l :=
  equation_refutation _ l.

Definition by_weights (weights : list (string * Z)) (dead : list string) positive l :
  _ = true -> ~ ll (atom := string) classical l :=
  weighted_refutation (weight_of String.eqb weights)
    (fun a => existsb (String.eqb a) dead) positive _ l.

Definition by_affine_weights (weights : list (string * Z)) (dead : list string) positive l :
  _ = true ->
  ~ ll (atom := string) {| mix := false; weakening := true; cut := false |} l :=
  affine_refutation (weight_of String.eqb weights)
    (fun a => existsb (String.eqb a) dead) positive _ l.

(** And two-sided. *)
Definition by_ivaluation (truths : list string) Γ C :
  _ = true -> ~ ill (atom := string) intuitionistic Γ C :=
  iclassical_refutation _ (fun a => existsb (String.eqb a) truths) Γ C.

Definition by_ibalance (a : string) Γ C :
  _ = true -> ~ ill (atom := string) intuitionistic Γ C :=
  iunbalanced_refutation String.eqb a _ Γ C.

Definition by_iequation Γ C :
  _ = true -> ~ ill (atom := string) intuitionistic Γ C :=
  iequation_refutation _ Γ C.

Definition by_iweights (weights : list (string * Z)) (dead : list string) positive Γ C :
  _ = true -> ~ ill (atom := string) intuitionistic Γ C :=
  iweighted_refutation (weight_of String.eqb weights)
    (fun a => existsb (String.eqb a) dead) positive _ Γ C.

Definition by_iaffine_weights (weights : list (string * Z)) (dead : list string) positive Γ C :
  _ = true -> ~ ill (atom := string) affine Γ C :=
  iaffine_refutation (weight_of String.eqb weights)
    (fun a => existsb (String.eqb a) dead) positive _ Γ C.
