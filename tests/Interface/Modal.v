(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** The interface of deduxit's certificates of valid modal sequents:
    under the prelude deduxit writes, every name a certificate uses, at
    the type and with the arguments it is used with. *)

From Stdlib Require Import List String.
From Deduxit.Modal Require Import Check.
Import ListNotations.
Open Scope string_scope.

(** The formulas, every constructor. *)
Definition formulas (a : string) A B :=
  [var a; top; bot; neg A; wedge A B; vee A B; imp A B; equiv A B; box A;
   dia A].

(** The labelled formulas and relational atoms. *)
Definition items (x y : string) (A : formula string) := [lab x A; rel x y].

(** The frame conditions, as the record of all five. *)
Definition conditions_of serial reflexive symmetric transitive euclidean :=
  {| serial := serial; reflexive := reflexive; symmetric := symmetric;
     transitive := transitive; euclidean := euclidean |}.

(** The proof terms, every constructor. *)
Definition proofs (x y z : string) (A B : formula string) p q :=
  [Ax x A; LBot x; RTop x; LNeg x A p; RNeg x A p; LAnd x A B p;
   RAnd x A B p q; LOr x A B p q; ROr x A B p; LImp x A B p q; RImp x A B p;
   LIff x A B p q; RIff x A B p q; LBox x y A p; RBox x y A p; LDia x y A p;
   RDia x y A p; Ref x p; Ser x y p; Sym x y p; Trans x y z p;
   Eucl x y z p].

(** The theorems, applied as a certificate applies them: a sequent at one
    label, or a labelled sequent. *)
Definition by_term C (x : string) p Γ Δ :
  _ = true -> valid (atom := string) C Γ Δ :=
  modal_soundness String.eqb String.eqb_spec C x p Γ Δ.

Definition by_labelled_term C p L R :
  _ = true -> lvalid (atom := string) C L R :=
  labelled_soundness String.eqb String.eqb_spec C p L R.
