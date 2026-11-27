(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** The interface of deduxit's certificates that a first-order sequent
    of linear logic has no proof: under the prelude deduxit writes,
    every name a certificate uses, at the type and with the arguments it
    is used with. *)

From Stdlib Require Import Bool List String ZArith.
From Deduxit.Linear Require Calculus Intuitionistic TermsCheck.
From Deduxit.Linear Require Import FirstOrderCalculus FirstOrderIntuitionistic FirstOrderWeights.
Import ListNotations.
Open Scope string_scope.

Definition terms (f : string) n ts := [bound n; eigen n; tapp f ts].

Definition formulas (p : string) ts A B :=
  [var p ts; covar p ts; one; bot; top; zero; tens A B; parr A B;
   awith A B; aplus A B; oc A; wn A; fall A; fex A].

Definition iformulas (p : string) ts A B :=
  [ivar p ts; ione; itens A B; ilmap A B; itop; iwith A B; izero;
   iplus A B; ioc A; iall A; iex A].

Definition statements mix weakening l Γ C :=
  [~ ll (symbol := string) Calculus.classical l;
   ~ ll (symbol := string)
       {| Calculus.mix := mix; Calculus.weakening := weakening; Calculus.cut := false |} l;
   ~ ill (symbol := string) Intuitionistic.intuitionistic Γ C;
   ~ ill (symbol := string) Intuitionistic.affine Γ C].

(** The theorems, applied as a certificate applies them, with a weight
    per atom of a predicate (its arguments compared by [terms_eqb]) or
    per predicate. *)
Definition by_atom (fixed : list string) (p : string) ts (w : Z) l :
  _ = true -> ~ ll (symbol := string) Calculus.classical l :=
  FirstOrderWeights.weighted_refutation (fun q => existsb (String.eqb q) fixed)
    (fun q us => if String.eqb q p && TermsCheck.terms_eqb String.eqb us ts then w else 0%Z)
    (fun _ => 0%Z) _ l.

Definition by_predicate (fixed : list string) (p : string) (w : Z) l :
  _ = true -> ~ ll (symbol := string) Calculus.classical l :=
  FirstOrderWeights.weighted_refutation (fun q => existsb (String.eqb q) fixed)
    (fun q _ => if String.eqb q p then w else 0%Z)
    (fun q => if String.eqb q p then w else 0%Z) _ l.

Definition by_iatom (fixed : list string) (p : string) ts (w : Z) Γ C :
  _ = true -> ~ ill (symbol := string) Intuitionistic.intuitionistic Γ C :=
  FirstOrderWeights.iweighted_refutation (fun q => existsb (String.eqb q) fixed)
    (fun q us => if String.eqb q p && TermsCheck.terms_eqb String.eqb us ts then w else 0%Z)
    (fun _ => 0%Z) _ Γ C.

Definition by_ipredicate (fixed : list string) (p : string) (w : Z) Γ C :
  _ = true -> ~ ill (symbol := string) Intuitionistic.intuitionistic Γ C :=
  FirstOrderWeights.iweighted_refutation (fun q => existsb (String.eqb q) fixed)
    (fun q _ => if String.eqb q p then w else 0%Z)
    (fun q => if String.eqb q p then w else 0%Z) _ Γ C.
