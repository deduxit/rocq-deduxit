(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * The sequent calculi LJ and LM

    This file is what a certificate's statement rests on: read it to
    know what such a certificate claims. [lj R Γ C] says that the
    sequent [Γ ⊢ C], with the hypotheses [Γ] and exactly one conclusion
    [C], has a derivation in intuitionistic logic (LJ) when
    [explosion R = true], or in minimal logic (LM) when it is false;
    without cut when [cut R = false].

    The rules are those of Troelstra and Schwichtenberg's G1i, with the
    contexts of the two-premise rules shared: the axiom on any formula,
    weakening and contraction of a hypothesis, and one left and one or
    two right rules per connective. A sequent with nothing right of [⊢]
    is written [Γ ⊢ ⊥]: G1i's weakening on the right is then [⊥]'s left
    rule, which LJ has and LM lacks. Shared contexts and G1i's split
    ones derive the same sequents, by weakening and contraction.

    The hypotheses are a list read as a multiset: the exchange rule
    [ex] allows any permutation. Every left rule acts on the first
    hypothesis, and the cut on the first hypothesis of its second
    premise. The file derives nothing and assumes nothing. [lj R Γ C] is
    a [Prop]: it says that a derivation exists. *)

From Stdlib Require Import List Permutation.
From Deduxit.Intuitionistic Require Export Formulas.
Import ListNotations.

(** The rules a calculus may add. *)
Record rules : Type := Rules {
  explosion : bool;  (** [⊥ ⊢ C] for every [C], ex falso: LJ has it, LM not *)
  cut : bool;        (** cut: [Γ ⊢ C] from [Γ ⊢ A] and [A, Γ ⊢ C] *)
}.

(** Intuitionistic logic, LJ: ex falso, no cut. *)
Definition intuitionistic : rules := {| explosion := true; cut := false |}.

(** Minimal logic, LM: neither ex falso nor cut. *)
Definition minimal : rules := {| explosion := false; cut := false |}.

Section Calculus.

Context {atom : Type}.
Local Notation formula := (formula atom).

(** The derivable sequents [Γ ⊢ C], where [R] gives the optional
    rules. *)
Inductive lj (R : rules) : list formula -> formula -> Prop :=
| ax : forall A,
    lj R [A] A
| ex : forall l1 l2 C,
    lj R l1 C -> Permutation l1 l2 -> lj R l2 C
| wk : forall A l C,
    lj R l C -> lj R (A :: l) C
| co : forall A l C,
    lj R (A :: A :: l) C -> lj R (A :: l) C
| bot_l : explosion R = true -> forall C,
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
| cut_r : cut R = true -> forall A l C,
    lj R l A -> lj R (A :: l) C -> lj R l C.

End Calculus.
