(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** The interface of deduxit's one-sided certificates: under the prelude
    deduxit writes, every name a certificate uses, at the type and with
    the arguments it is used with. A change that breaks this file breaks
    certificates deduxit has written; README's "The certificates'
    interface" lists the same names. *)

From Stdlib Require Import List String.
From Deduxit.Linear Require Import Soundness.
Import ListNotations.
Open Scope string_scope.

(** The formulas, every constructor. *)
Definition formulas (a : string) A B :=
  [var a; covar a; one; bot; top; zero; tens A B; parr A B; awith A B;
   aplus A B; oc A; wn A].

(** The proof terms, every constructor, with the branches of [⊕]. *)
Definition proofs (a : string) A B p q :=
  [Ax a; Tensor A B p q; Par A B p; One; Bot p; With A B p q;
   Plus A B Left p; Plus A B Right p; Top; Bang A p; Quest A p; Copy A p;
   Weaken A p; Mix p q; Cut A p q].

(** The statement, with the calculus by its name or as a record of its
    optional rules. *)
Definition statements l :=
  [ll (atom := string) classical l;
   ll (atom := string) {| mix := true; weakening := false; cut := false |} l].

(** The theorems, applied as a certificate applies them: the term, then
    the sequent, which [apply] finds. *)
Definition by_classical p l :
  _ = true -> ll (atom := string) classical l :=
  soundness_classical String.eqb String.eqb_spec p l.

Definition by_mix p l :
  _ = true -> ll (atom := string) {| mix := true; weakening := false; cut := false |} l :=
  soundness_mix String.eqb String.eqb_spec p l.

Definition by_affine p l :
  _ = true -> ll (atom := string) {| mix := false; weakening := true; cut := false |} l :=
  soundness_affine String.eqb String.eqb_spec p l.

Definition by_any mix weakening cut p l :
  _ = true ->
  ll (atom := string) {| mix := mix; weakening := weakening; cut := cut |} l :=
  soundness String.eqb String.eqb_spec
    {| mix := mix; weakening := weakening; cut := cut |} p l.
