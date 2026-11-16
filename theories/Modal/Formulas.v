(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * The formulas of propositional modal logic

    Atoms, [⊤], [⊥], [¬], [∧], [∨], [→], [↔], and the two modalities
    [□] ("in every world this one sees") and [◇] ("in some world this
    one sees"). Every connective is a constructor, so a formula reads
    here as it is written.

    This file and [Kripke.v] are what a certificate's statement rests
    on. They derive nothing and assume nothing. *)

Section Formulas.

Context {atom : Type}.

(** A formula. *)
Inductive formula : Type :=
| var : atom -> formula                    (** an atom [a] *)
| top : formula                            (** [⊤] *)
| bot : formula                            (** [⊥] *)
| neg : formula -> formula                 (** [¬A] *)
| wedge : formula -> formula -> formula    (** [A ∧ B] *)
| vee : formula -> formula -> formula      (** [A ∨ B] *)
| imp : formula -> formula -> formula      (** [A → B] *)
| equiv : formula -> formula -> formula    (** [A ↔ B] *)
| box : formula -> formula                 (** [□A] *)
| dia : formula -> formula.                (** [◇A] *)

End Formulas.

Arguments formula atom : clear implicits.
