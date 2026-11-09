(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** What the soundness theorems, the first-order ones among them, the
    reduction of Mix and the refutations rest on: nothing beyond the
    definitions. Rocq answers "Closed under the global context" for
    each, which the flake's check requires. Every theorem is
    named by its full path, since the first-order ones share their names
    with the propositional ones. *)

From Deduxit.Linear Require Soundness IntuitionisticCheck Mix Refutations Weights.
From Deduxit.Linear Require FirstOrderSoundness FirstOrderIntuitionisticCheck FirstOrderWeights.

Print Assumptions Deduxit.Linear.Soundness.soundness.
Print Assumptions Deduxit.Linear.Soundness.soundness_classical.
Print Assumptions Deduxit.Linear.Soundness.soundness_mix.
Print Assumptions Deduxit.Linear.Soundness.soundness_affine.
Print Assumptions Deduxit.Linear.IntuitionisticCheck.soundness_ill.
Print Assumptions Deduxit.Linear.Mix.mix_to_ll.
Print Assumptions Deduxit.Linear.Mix.mix_to_classical.
Print Assumptions Deduxit.Linear.Refutations.ll_tautology.
Print Assumptions Deduxit.Linear.Refutations.classical_refutation.
Print Assumptions Deduxit.Linear.Refutations.balance.
Print Assumptions Deduxit.Linear.Refutations.unbalanced_refutation.
Print Assumptions Deduxit.Linear.Refutations.count_equation.
Print Assumptions Deduxit.Linear.Refutations.equation_refutation.
Print Assumptions Deduxit.Linear.Refutations.ill_ll.
Print Assumptions Deduxit.Linear.Refutations.ill_tautology.
Print Assumptions Deduxit.Linear.Refutations.iclassical_refutation.
Print Assumptions Deduxit.Linear.Refutations.iunbalanced_refutation.
Print Assumptions Deduxit.Linear.Refutations.iequation_refutation.
Print Assumptions Deduxit.Linear.Weights.weighted_balance.
Print Assumptions Deduxit.Linear.Weights.weighted_refutation.
Print Assumptions Deduxit.Linear.Weights.iweighted_refutation.
Print Assumptions Deduxit.Linear.Weights.affine_balance.
Print Assumptions Deduxit.Linear.Weights.affine_refutation.
Print Assumptions Deduxit.Linear.Weights.iaffine_refutation.
Print Assumptions Deduxit.Linear.FirstOrderSoundness.soundness.
Print Assumptions Deduxit.Linear.FirstOrderSoundness.soundness_classical.
Print Assumptions Deduxit.Linear.FirstOrderSoundness.soundness_mix.
Print Assumptions Deduxit.Linear.FirstOrderSoundness.soundness_affine.
Print Assumptions Deduxit.Linear.FirstOrderIntuitionisticCheck.soundness_ill.
Print Assumptions Deduxit.Linear.FirstOrderWeights.weighted_balance.
Print Assumptions Deduxit.Linear.FirstOrderWeights.weighted_refutation.
Print Assumptions Deduxit.Linear.FirstOrderWeights.ill_ll.
Print Assumptions Deduxit.Linear.FirstOrderWeights.iweighted_refutation.
