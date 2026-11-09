(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * The one-sided sequent calculus of first-order classical linear logic

    This file is what a certificate's first-order one-sided statement
    rests on: read it to know what such a certificate claims. [ll R Γ]
    says that the sequent [⊢ Γ] has a derivation in first-order linear
    logic with the optional rules [R]; without cut when
    [Calculus.cut R = false]. [R] is the record [Calculus.rules] of the
    propositional calculus: Mix, weakening and cut.

    The rules are those of [Calculus] over first-order formulas, with
    the axiom on a predicate and its negation with equal arguments, and
    two quantifier rules:
    - [∃], with any closed term as its witness, eigenvariables included
      (they are constants outside the signature);
    - [∀], with an eigenvariable that occurs nowhere in its conclusion.
      This includes the context of a [⊤] above, since that context is
      written in the sequent.

    A sequent is a list of formulas read as a multiset: the exchange
    rule [ex_r] allows any permutation. Every other rule except Mix and
    cut acts on the first formula. The file derives nothing and assumes
    nothing. [ll R Γ] is a [Prop]: it says that a derivation exists. *)

From Stdlib Require Import List Permutation.
From Deduxit.Linear Require Calculus.
From Deduxit.Linear Require Export FirstOrderFormulas.
Import ListNotations.

Section Calculus.

Context {symbol : Type}.
Local Notation formula := (formula symbol).

(** The eigenvariable [a] occurs in no formula of [l]. *)
Definition fresh (a : nat) (l : list formula) : Prop :=
  forall A, In A l -> occurs a A = false.

(** The derivable sequents, where [R] gives the optional rules. *)
Inductive ll (R : Calculus.rules) : list formula -> Prop :=
| ax_r : forall p l,
    ll R [covar p l; var p l]
| ex_r : forall l1 l2,
    ll R l1 -> Permutation l1 l2 -> ll R l2
| one_r :
    ll R [one]
| bot_r : forall l,
    ll R l -> ll R (bot :: l)
| top_r : forall l,
    ll R (top :: l)
| tens_r : forall A B l1 l2,
    ll R (A :: l1) -> ll R (B :: l2) -> ll R (tens A B :: l1 ++ l2)
| parr_r : forall A B l,
    ll R (A :: B :: l) -> ll R (parr A B :: l)
| with_r : forall A B l,
    ll R (A :: l) -> ll R (B :: l) -> ll R (awith A B :: l)
| plus_r1 : forall A B l,
    ll R (A :: l) -> ll R (aplus A B :: l)
| plus_r2 : forall A B l,
    ll R (B :: l) -> ll R (aplus A B :: l)
| oc_r : forall A l,
    ll R (A :: map wn l) -> ll R (oc A :: map wn l)
| de_r : forall A l,
    ll R (A :: l) -> ll R (wn A :: l)
| wk_r : forall A l,
    ll R l -> ll R (wn A :: l)
| co_r : forall A l,
    ll R (wn A :: wn A :: l) -> ll R (wn A :: l)
| mix_r : Calculus.mix R = true -> forall l1 l2,
    ll R l1 -> ll R l2 -> ll R (l1 ++ l2)
| weakening_r : Calculus.weakening R = true -> forall A l,
    ll R l -> ll R (A :: l)
| cut_r : Calculus.cut R = true -> forall A l1 l2,
    ll R (A :: l1) -> ll R (dual A :: l2) -> ll R (l1 ++ l2)
| fall_r : forall A a l,
    fresh a (fall A :: l) -> ll R (subst 0 (eigen a) A :: l) -> ll R (fall A :: l)
| fex_r : forall A t l,
    tclosed t = true -> ll R (subst 0 t A :: l) -> ll R (fex A :: l).

End Calculus.
