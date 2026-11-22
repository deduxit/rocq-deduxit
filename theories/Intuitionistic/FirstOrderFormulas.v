(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * The formulas of ordinary first-order logic

    The formulas of [Formulas] with predicates applied to terms in place
    of atoms, and the quantifiers [∀] and [∃]. The terms are those of
    [Deduxit.Linear.Terms]: a symbol applied to terms, a bound variable
    (a de Bruijn index) or an eigenvariable. Symbols have any type you
    choose; predicate and function symbols share it, as in deduxit's
    sequents, and a propositional atom is a predicate applied to no
    term. A quantifier binds the bound variable [0] of its body; the
    variables of the quantifiers around it are [1] and up. [⊤], [¬A] and
    [A ↔ B] are defined as in [Formulas].

    This file and [FirstOrderCalculus.v] are what a first-order
    certificate's statement rests on, with [Deduxit.Linear.Terms] and
    [Calculus.v] for the record of rules. They derive nothing and assume
    nothing. The names repeat those of [Formulas] ([formula], [var],
    [bot], ...): a file that needs both requires them without importing
    one of them. *)

From Stdlib Require Import List.
From Deduxit.Linear Require Export Terms.
Import ListNotations.

Section Formulas.

Context {symbol : Type}.
Local Notation term := (term symbol).

(** A first-order formula. *)
Inductive formula : Type :=
| var : symbol -> list term -> formula     (** a predicate [p(t₁, …, tₙ)] *)
| bot : formula                            (** [⊥] *)
| wedge : formula -> formula -> formula    (** [A ∧ B] *)
| vee : formula -> formula -> formula      (** [A ∨ B] *)
| imp : formula -> formula -> formula      (** [A → B] *)
| fall : formula -> formula                (** [∀x. A], [x] the bound variable [0] of [A] *)
| fex : formula -> formula.                (** [∃x. A] *)

(** [⊤], true: [⊥ → ⊥]. *)
Definition top : formula := imp bot bot.

(** [¬A]: [A → ⊥]. *)
Definition neg (A : formula) : formula := imp A bot.

(** [A ↔ B]: [(A → B) ∧ (B → A)]. *)
Definition equiv (A B : formula) : formula := wedge (imp A B) (imp B A).

(** Substitutes the closed term [u] for the bound variable [k] of [A];
    that variable is [k] at the top and one more under each quantifier.
    [subst 0 u A] is the instance at [u] of the body [A] of [∀x. A] or
    [∃x. A]. *)
Fixpoint subst (k : nat) (u : term) (A : formula) : formula :=
  match A with
  | var p l => var p (map (tsubst k u) l)
  | bot => bot
  | wedge A B => wedge (subst k u A) (subst k u B)
  | vee A B => vee (subst k u A) (subst k u B)
  | imp A B => imp (subst k u A) (subst k u B)
  | fall A => fall (subst (S k) u A)
  | fex A => fex (subst (S k) u A)
  end.

(** Whether the eigenvariable [a] occurs in [A]. *)
Fixpoint occurs (a : nat) (A : formula) : bool :=
  match A with
  | var _ l => existsb (toccurs a) l
  | bot => false
  | wedge A B | vee A B | imp A B => occurs a A || occurs a B
  | fall A | fex A => occurs a A
  end.

(** The eigenvariable [a] occurs in no formula of [l]. *)
Definition fresh (a : nat) (l : list formula) : Prop :=
  forall A, In A l -> occurs a A = false.

End Formulas.

Arguments formula symbol : clear implicits.
