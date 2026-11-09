(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * First-order terms

    The terms that the predicates of first-order formulas
    ([FirstOrderFormulas], [FirstOrderIntuitionistic]) apply to. Symbols
    have any type you choose. A term is one of:
    - a symbol applied to a list of terms (a constant is a symbol
      applied to none);
    - a variable bound by a quantifier;
    - an eigenvariable.

    Bound variables are de Bruijn indices: [bound 0] is the variable of
    the innermost quantifier around it. So formulas that differ only in
    the names of their bound variables are equal. An eigenvariable is a
    constant outside every signature, named by a natural number: the
    fresh constant a [∀] rule introduces, or any other constant a
    witness may use. Arities are not checked: a symbol applied to lists
    of different lengths gives different terms. *)

From Stdlib Require Import Bool List.
Import ListNotations.

Section Terms.

Context {symbol : Type}.

(** A term. *)
Inductive term : Type :=
| bound : nat -> term                  (** a bound variable, a de Bruijn index *)
| eigen : nat -> term                  (** an eigenvariable *)
| tapp : symbol -> list term -> term.  (** [f(t₁, …, tₙ)] *)

(** Substitutes [u] for the bound variable [k] of [t]. *)
Fixpoint tsubst (k : nat) (u : term) (t : term) : term :=
  match t with
  | bound n => if Nat.eqb n k then u else bound n
  | eigen a => eigen a
  | tapp f l => tapp f (map (tsubst k u) l)
  end.

(** Whether the eigenvariable [a] occurs in [t]. *)
Fixpoint toccurs (a : nat) (t : term) : bool :=
  match t with
  | bound _ => false
  | eigen b => Nat.eqb a b
  | tapp _ l => existsb (toccurs a) l
  end.

(** Whether [t] is closed: no bound variable occurs in it, so it can be
    substituted under any number of quantifiers without being
    captured. *)
Fixpoint tclosed (t : term) : bool :=
  match t with
  | bound _ => false
  | eigen _ => true
  | tapp _ l => forallb tclosed l
  end.

End Terms.

Arguments term symbol : clear implicits.
