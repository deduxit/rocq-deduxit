(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** The interface of deduxit's one-sided first-order certificates: under
    the prelude deduxit writes, every name a certificate uses, at the
    type and with the arguments it is used with. The propositional
    calculus's module is required, not imported, so its names are
    written with it. *)

From Stdlib Require Import List String.
From Deduxit.Linear Require Calculus.
From Deduxit.Linear Require Import FirstOrderSoundness.
Import ListNotations.
Open Scope string_scope.

(** The terms and the formulas, every constructor. *)
Definition terms (f : string) n ts := [bound n; eigen n; tapp f ts].

Definition formulas (p : string) ts A B :=
  [var p ts; covar p ts; one; bot; top; zero; tens A B; parr A B;
   awith A B; aplus A B; oc A; wn A; fall A; fex A].

(** The proof terms, every constructor. *)
Definition proofs (p : string) ts A B n t q r :=
  [Ax p ts; Tensor A B q r; Par A B q; One; Bot q; With A B q r;
   Plus A B Left q; Plus A B Right q; Top; Bang A q; Quest A q; Copy A q;
   Weaken A q; Mix q r; Cut A q r; Forall A n q; Exists A t q].

(** The statement, with the calculus qualified by its module. *)
Definition statements l :=
  [ll (symbol := string) Calculus.classical l;
   ll (symbol := string)
     {| Calculus.mix := false; Calculus.weakening := true; Calculus.cut := false |} l].

(** The theorems, applied as a certificate applies them. *)
Definition by_classical p l :
  _ = true -> ll (symbol := string) Calculus.classical l :=
  soundness_classical String.eqb String.eqb_spec p l.

Definition by_mix p l :
  _ = true ->
  ll (symbol := string)
    {| Calculus.mix := true; Calculus.weakening := false; Calculus.cut := false |} l :=
  soundness_mix String.eqb String.eqb_spec p l.

Definition by_affine p l :
  _ = true ->
  ll (symbol := string)
    {| Calculus.mix := false; Calculus.weakening := true; Calculus.cut := false |} l :=
  soundness_affine String.eqb String.eqb_spec p l.

Definition by_any mix weakening cut p l :
  _ = true ->
  ll (symbol := string)
    {| Calculus.mix := mix; Calculus.weakening := weakening; Calculus.cut := cut |} l :=
  soundness String.eqb String.eqb_spec
    {| Calculus.mix := mix; Calculus.weakening := weakening; Calculus.cut := cut |} p l.
