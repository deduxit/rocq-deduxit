(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** The interface of deduxit's two-sided first-order certificates: under
    the prelude deduxit writes, every name a certificate uses, at the
    type and with the arguments it is used with. The propositional
    two-sided calculus's module is required, not imported, so its names
    are written with it. *)

From Stdlib Require Import List String.
From Deduxit.Linear Require Intuitionistic.
From Deduxit.Linear Require Import FirstOrderIntuitionisticCheck.
Import ListNotations.
Open Scope string_scope.

(** The terms and the formulas, every constructor. *)
Definition terms (f : string) n ts := [bound n; eigen n; tapp f ts].

Definition formulas (p : string) ts A B :=
  [ivar p ts; ione; itens A B; ilmap A B; itop; iwith A B; izero;
   iplus A B; ioc A; iall A; iex A].

(** The proof terms, every constructor. *)
Definition proofs (p : string) ts A B Γ n t q r :=
  [IAx p ts; IOneR; IOneL q; ITensR A B q r; ITensL A B q; ILmapR A B q;
   ILmapL A B q r; ITopR Γ; IWithR A B q r; IWithL1 A B q; IWithL2 A B q;
   IZeroL Γ A; IPlusR1 A B q; IPlusR2 A B q; IPlusL A B q r; IOcR A q;
   IDe A q; IWk A q; ICo A q; IWeaken A q; ICut A q r; IAllR A n q;
   IExL A n q; IExR A t q; IAllL A t q].

(** The calculi, qualified by their module. *)
Definition calculi :=
  [Intuitionistic.intuitionistic; Intuitionistic.affine;
   {| Intuitionistic.iweakening := false; Intuitionistic.icut := true |}].

(** The theorem, applied as a certificate applies it. *)
Definition by_term R p Γ C :
  _ = true -> ill (symbol := string) R Γ C :=
  soundness_ill String.eqb String.eqb_spec R p Γ C.
