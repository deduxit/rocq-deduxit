(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * The first-order sequent calculi LJ, LM and LK

    This file is what a first-order certificate's statement rests on:
    read it to know what such a certificate claims.

    [lj R Γ C] says that the sequent [Γ ⊢ C] has a derivation in
    first-order intuitionistic logic (LJ) when
    [Calculus.explosion R = true], or in minimal logic (LM) when it is
    false; without cut when [Calculus.cut R = false]. Its propositional
    rules are those of [Calculus.lj]. [lk c Γ Δ] says that [Γ ⊢ Δ], with
    any number of formulas on either side, has a derivation in
    first-order classical logic (LK); without cut when [c = false].

    The rules are those of Troelstra and Schwichtenberg's G1i and G1c,
    with the contexts of the two-premise rules shared, and two rules per
    quantifier:
    - [∀R] and [∃L], with an eigenvariable that occurs nowhere in their
      conclusion;
    - [∀L] and [∃R], with any closed term as the witness, eigenvariables
      included (they are constants outside the signature).

    G3's rules, which keep the principal formula of [∀L] and [∃R], are
    these with a contraction. Both sides are lists read as multisets: the
    exchange rules allow any permutation. Every left rule acts on the
    first hypothesis and every right rule on the first conclusion. The
    file derives nothing and assumes nothing. *)

From Stdlib Require Import List Permutation.
From Deduxit.Intuitionistic Require Calculus.
From Deduxit.Intuitionistic Require Export FirstOrderFormulas.
Import ListNotations.

Section Calculus.

Context {symbol : Type}.
Local Notation formula := (formula symbol).

(** The derivable sequents [Γ ⊢ C] of LJ and LM, where [R] gives the
    optional rules. *)
Inductive lj (R : Calculus.rules) : list formula -> formula -> Prop :=
| ax : forall A,
    lj R [A] A
| ex : forall l1 l2 C,
    lj R l1 C -> Permutation l1 l2 -> lj R l2 C
| wk : forall A l C,
    lj R l C -> lj R (A :: l) C
| co : forall A l C,
    lj R (A :: A :: l) C -> lj R (A :: l) C
| bot_l : Calculus.explosion R = true -> forall C,
    lj R [bot] C
| wedge_r : forall A B l,
    lj R l A -> lj R l B -> lj R l (wedge A B)
| wedge_l : forall A B l C,
    lj R (A :: B :: l) C -> lj R (wedge A B :: l) C
| vee_r1 : forall A B l,
    lj R l A -> lj R l (vee A B)
| vee_r2 : forall A B l,
    lj R l B -> lj R l (vee A B)
| vee_l : forall A B l C,
    lj R (A :: l) C -> lj R (B :: l) C -> lj R (vee A B :: l) C
| imp_r : forall A B l,
    lj R (A :: l) B -> lj R l (imp A B)
| imp_l : forall A B l C,
    lj R l A -> lj R (B :: l) C -> lj R (imp A B :: l) C
| cut_r : Calculus.cut R = true -> forall A l C,
    lj R l A -> lj R (A :: l) C -> lj R l C
| fall_r : forall A a l,
    fresh a (fall A :: l) -> lj R l (subst 0 (eigen a) A) -> lj R l (fall A)
| fall_l : forall A t l C,
    tclosed t = true -> lj R (subst 0 t A :: l) C -> lj R (fall A :: l) C
| fex_r : forall A t l,
    tclosed t = true -> lj R l (subst 0 t A) -> lj R l (fex A)
| fex_l : forall A a l C,
    fresh a (fex A :: C :: l) -> lj R (subst 0 (eigen a) A :: l) C -> lj R (fex A :: l) C.

(** The derivable sequents [Γ ⊢ Δ] of LK, with cut when [c = true]. *)
Inductive lk (c : bool) : list formula -> list formula -> Prop :=
| kax : forall A,
    lk c [A] [A]
| kex_l : forall l1 l2 d,
    lk c l1 d -> Permutation l1 l2 -> lk c l2 d
| kex_r : forall l d1 d2,
    lk c l d1 -> Permutation d1 d2 -> lk c l d2
| kwk_l : forall A l d,
    lk c l d -> lk c (A :: l) d
| kwk_r : forall A l d,
    lk c l d -> lk c l (A :: d)
| kco_l : forall A l d,
    lk c (A :: A :: l) d -> lk c (A :: l) d
| kco_r : forall A l d,
    lk c l (A :: A :: d) -> lk c l (A :: d)
| kbot_l :
    lk c [bot] []
| kwedge_r : forall A B l d,
    lk c l (A :: d) -> lk c l (B :: d) -> lk c l (wedge A B :: d)
| kwedge_l : forall A B l d,
    lk c (A :: B :: l) d -> lk c (wedge A B :: l) d
| kvee_r : forall A B l d,
    lk c l (A :: B :: d) -> lk c l (vee A B :: d)
| kvee_l : forall A B l d,
    lk c (A :: l) d -> lk c (B :: l) d -> lk c (vee A B :: l) d
| kimp_r : forall A B l d,
    lk c (A :: l) (B :: d) -> lk c l (imp A B :: d)
| kimp_l : forall A B l d,
    lk c l (A :: d) -> lk c (B :: l) d -> lk c (imp A B :: l) d
| kcut : c = true -> forall A l d,
    lk c l (A :: d) -> lk c (A :: l) d -> lk c l d
| kfall_r : forall A a l d,
    fresh a (fall A :: l ++ d) -> lk c l (subst 0 (eigen a) A :: d) -> lk c l (fall A :: d)
| kfall_l : forall A t l d,
    tclosed t = true -> lk c (subst 0 t A :: l) d -> lk c (fall A :: l) d
| kfex_r : forall A t l d,
    tclosed t = true -> lk c l (subst 0 t A :: d) -> lk c l (fex A :: d)
| kfex_l : forall A a l d,
    fresh a (fex A :: l ++ d) -> lk c (subst 0 (eigen a) A :: l) d -> lk c (fex A :: l) d.

End Calculus.
