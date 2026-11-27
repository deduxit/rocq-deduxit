(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** The theorems deduxit's messages name by their path: no finite Kripke
    model refutes these two, and deduxit's refusal of the negative
    translation's first-order shift points to them. *)

From Deduxit.Intuitionistic Require FirstOrderKripke.

Definition excluded_middle := @Deduxit.Intuitionistic.FirstOrderKripke.chain_excluded_middle.

Definition double_negation_shift :=
  @Deduxit.Intuitionistic.FirstOrderKripke.chain_double_negation_shift.
