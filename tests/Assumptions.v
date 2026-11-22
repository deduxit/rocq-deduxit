(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** The soundness theorems (the first-order ones included), the
    reduction of Mix, the refutations, the Kripke semantics of
    intuitionistic and minimal logic and the labelled calculus of modal
    logic rest on no axiom: Rocq answers
    "Closed under the global context" for each, and the flake's check
    requires that answer. Every theorem is named by its full path,
    since the first-order ones share their names with the propositional
    ones. *)

From Deduxit.Linear Require Soundness IntuitionisticCheck Mix Refutations Weights.
From Deduxit.Linear Require FirstOrderSoundness FirstOrderIntuitionisticCheck FirstOrderWeights.
From Deduxit.Intuitionistic Require Kripke KripkeCheck.
From Deduxit.Intuitionistic Require FirstOrderKripke FirstOrderClassical FirstOrderCheck.
From Deduxit.Modal Require Soundness Check Countermodel.

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
Print Assumptions Deduxit.Intuitionistic.Kripke.kripke_soundness.
Print Assumptions Deduxit.Intuitionistic.Kripke.kripke_countermodel.
Print Assumptions Deduxit.Intuitionistic.Kripke.classical_refutation.
Print Assumptions Deduxit.Intuitionistic.KripkeCheck.kripke_refutation.
Print Assumptions Deduxit.Intuitionistic.FirstOrderKripke.kripke_soundness.
Print Assumptions Deduxit.Intuitionistic.FirstOrderKripke.kripke_countermodel.
Print Assumptions Deduxit.Intuitionistic.FirstOrderKripke.chain_excluded_middle.
Print Assumptions Deduxit.Intuitionistic.FirstOrderKripke.chain_double_negation_shift.
Print Assumptions Deduxit.Intuitionistic.FirstOrderClassical.classical_soundness.
Print Assumptions Deduxit.Intuitionistic.FirstOrderClassical.classical_countermodel.
Print Assumptions Deduxit.Intuitionistic.FirstOrderCheck.fo_classical_refutation.
Print Assumptions Deduxit.Intuitionistic.FirstOrderCheck.fo_kripke_refutation.
Print Assumptions Deduxit.Modal.Soundness.g3_sound.
Print Assumptions Deduxit.Modal.Soundness.lvalid_valid.
Print Assumptions Deduxit.Modal.Soundness.g3_valid.
Print Assumptions Deduxit.Modal.Soundness.excluded_middle_stable.
Print Assumptions Deduxit.Modal.Check.mcheck_sound.
Print Assumptions Deduxit.Modal.Check.labelled_soundness.
Print Assumptions Deduxit.Modal.Check.modal_soundness.
Print Assumptions Deduxit.Modal.Countermodel.modal_refutation.
