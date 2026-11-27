(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** The interface of deduxit's two-sided certificates of intuitionistic
    linear logic and its affine variant: under the prelude deduxit
    writes, every name a certificate uses, at the type and with the
    arguments it is used with. *)

From Stdlib Require Import List String.
From Deduxit.Linear Require Import IntuitionisticCheck.
Import ListNotations.
Open Scope string_scope.

(** The formulas, every constructor. *)
Definition formulas (a : string) A B :=
  [ivar a; ione; itens A B; ilmap A B; itop; iwith A B; izero; iplus A B;
   ioc A].

(** The proof terms, every constructor. *)
Definition proofs (a : string) A B Γ p q :=
  [IAx a; IOneR; IOneL p; ITensR A B p q; ITensL A B p; ILmapR A B p;
   ILmapL A B p q; ITopR Γ; IWithR A B p q; IWithL1 A B p; IWithL2 A B p;
   IZeroL Γ A; IPlusR1 A B p; IPlusR2 A B p; IPlusL A B p q; IOcR A p;
   IDe A p; IWk A p; ICo A p; IWeaken A p; ICut A p q].

(** The calculi by their names, or as a record of the optional rules
    when the derivation has a cut. *)
Definition calculi :=
  [intuitionistic; affine; {| iweakening := false; icut := true |}].

(** The theorem, applied as a certificate applies it. *)
Definition by_term R p Γ C :
  _ = true -> ill (atom := string) R Γ C :=
  soundness_ill String.eqb String.eqb_spec R p Γ C.
