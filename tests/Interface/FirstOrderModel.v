(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** The interface of deduxit's certificates that a first-order sequent
    of ordinary logic is not valid, by a finite structure or a Kripke
    model with growing domains: under the prelude deduxit writes, every
    name a certificate uses, at the type and with the arguments it is
    used with. The record of the rules of LJ stays qualified. *)

From Stdlib Require Import List String.
From Deduxit.Intuitionistic Require Import FirstOrderCheck.
Import ListNotations.
Open Scope string_scope.

Definition terms (f : string) n ts := [bound n; tapp f ts].

(** The formulas, every constructor, and the connectives defined from
    them. *)
Definition formulas (p : string) ts A B :=
  [var p ts; bot; wedge A B; vee A B; imp A B; fall A; fex A; top; neg A;
   equiv A B].

(** A finite structure: each function's table rows are its name, its
    argument count and its values; each predicate holds of a tuple. *)
Definition structure_of size functions predicates : structure string :=
  {| size := size; functions := functions; predicates := predicates |}.

Definition a_structure : structure string :=
  {| size := 2; functions := [("a", 0, [0]); ("f", 1, [1; 1])];
     predicates := [("p", [0])] |}.

(** A Kripke model with growing domains. *)
Definition a_kripke_model : kripke_model string :=
  {| later := [[1]; []]; sizes := [1; 2];
     tables := [[("a", 0, [0])]; [("a", 0, [0])]];
     facts := [[]; [("p", [0])]]; absurd := [] |}.

(** The theorems, applied as a certificate applies them. *)
Definition by_structure S Γ Δ :
  _ = true -> ~ lk (symbol := string) true Γ Δ :=
  fo_classical_refutation String.eqb true S Γ Δ.

Definition by_kripke_model explosion M w Γ C :
  _ = true ->
  ~ lj (symbol := string) {| Calculus.explosion := explosion; Calculus.cut := true |} Γ C :=
  fo_kripke_refutation String.eqb String.eqb_spec _ M w Γ C.
