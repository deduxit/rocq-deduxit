(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * The formulas of ordinary propositional logic

    The formulas of intuitionistic and minimal logic: atoms, [⊥], [∧],
    [∨] and [→]. [⊤], [¬A] and [A ↔ B] are defined from them, as in
    Troelstra and Schwichtenberg's _Basic Proof Theory_: [⊤] is
    [⊥ → ⊥], [¬A] is [A → ⊥] and [A ↔ B] is [(A → B) ∧ (B → A)]. In
    minimal logic [⊥] has no rule of its own, so it is one more atom
    and [¬A] says that [A] leads to it.

    This file and [Calculus.v] are what a certificate's statement rests
    on. They derive nothing and assume nothing. *)

Section Formulas.

Context {atom : Type}.

(** A formula. *)
Inductive formula : Type :=
| var : atom -> formula                    (** an atom [a] *)
| bot : formula                            (** [⊥] *)
| wedge : formula -> formula -> formula    (** [A ∧ B] *)
| vee : formula -> formula -> formula      (** [A ∨ B] *)
| imp : formula -> formula -> formula.     (** [A → B] *)

(** [⊤], true: [⊥ → ⊥]. *)
Definition top : formula := imp bot bot.

(** [¬A]: [A → ⊥]. *)
Definition neg (A : formula) : formula := imp A bot.

(** [A ↔ B]: [(A → B) ∧ (B → A)]. *)
Definition equiv (A B : formula) : formula := wedge (imp A B) (imp B A).

End Formulas.

Arguments formula atom : clear implicits.
