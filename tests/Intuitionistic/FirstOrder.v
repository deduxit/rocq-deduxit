(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** Certificates of non-derivability at first order, in the form deduxit
    writes them: in LJ and LM by finite Kripke models with growing
    domains and [fo_kripke_refutation], in LK by finite structures and
    [fo_classical_refutation]. The last lemmas check what [krefutes] and
    [srefutes] reject, and that the infinite chain's theorems apply to
    any predicate. *)

From Stdlib Require Import List String.
From Deduxit.Intuitionistic Require Import FirstOrderCheck.
Import ListNotations.
Open Scope string_scope.

(** The terms and atoms of the tests. *)
Definition a : term string := tapp "a" [].
Definition p (t : term string) : formula string := var "p" [t].
Definition q (t : term string) : formula string := var "q" [t].
Definition r : formula string := var "r" [].
Definition x : term string := bound 0.

(** [¬∀x. p(x) ⊢ ∃x. ¬p(x)]: the root has one element, [0], and its later
    world adds [1] and makes [p(0)] true, so no world forces [∀x. p(x)]
    and the root has no element of which [p] fails for good. *)
Lemma not_forall :
  ~ lj (symbol := string) {| Calculus.explosion := true; Calculus.cut := true |}
      [neg (fall (p x))] (fex (neg (p x))).
Proof.
  apply (fo_kripke_refutation String.eqb String.eqb_spec _
           {| later := [[1]; []]; sizes := [1; 2]; tables := [[]; []];
              facts := [[]; [("p", [0])]]; absurd := [] |} 0).
  vm_compute. reflexivity.
Qed.

(** [∀x. (r ∨ q(x)) ⊢ r ∨ ∀x. q(x)], the constant domain principle, with
    cut. *)
Lemma constant_domain :
  ~ lj {| Calculus.explosion := true; Calculus.cut := true |}
      [fall (vee r (q x))] (vee r (fall (q x))).
Proof.
  apply (fo_kripke_refutation String.eqb String.eqb_spec _
           {| later := [[1]; []]; sizes := [1; 2]; tables := [[]; []];
              facts := [[("q", [0])]; [("q", [0]); ("r", [])]]; absurd := [] |} 0).
  vm_compute. reflexivity.
Qed.

(** [⊢ ¬¬p(f(a)) → p(f(a))], with a function table at each world that
    keeps the root's values. *)
Lemma function_table :
  ~ lj Calculus.intuitionistic [] (imp (neg (neg (p (tapp "f" [a])))) (p (tapp "f" [a]))).
Proof.
  apply (fo_kripke_refutation String.eqb String.eqb_spec Calculus.intuitionistic
           {| later := [[1]; []]; sizes := [1; 2];
              tables := [[("a", 0, [0]); ("f", 1, [0])]; [("a", 0, [0]); ("f", 1, [0; 1])]];
              facts := [[]; [("p", [0])]]; absurd := [] |} 0).
  vm_compute. reflexivity.
Qed.

(** [⊢ ¬¬(⊥ → p(a))] in LM: the later world forces [⊥] and not [p(a)]. *)
Lemma minimal_falsity :
  ~ lj (symbol := string) {| Calculus.explosion := false; Calculus.cut := true |}
      [] (neg (neg (imp bot (p a)))).
Proof.
  apply (fo_kripke_refutation String.eqb String.eqb_spec _
           {| later := [[1]; []]; sizes := [1; 1]; tables := [[("a", 0, [0])]; [("a", 0, [0])]];
              facts := [[]; []]; absurd := [1] |} 0).
  vm_compute. reflexivity.
Qed.

(** [∃x. p(x) ⊢ ∀x. p(x)] in cut-free LK, by two elements. *)
Lemma exists_forall :
  ~ lk false [fex (p x)] [fall (p x)].
Proof.
  apply (fo_classical_refutation String.eqb false
           {| size := 2; functions := []; predicates := [("p", [0])] |}).
  vm_compute. reflexivity.
Qed.

(** [p(a) ⊢ p(f(a)), r] in LK, with cut: [f] swaps the two elements. *)
Lemma classical_function :
  ~ lk true [p a] [p (tapp "f" [a]); r].
Proof.
  apply (fo_classical_refutation String.eqb true
           {| size := 2; functions := [("a", 0, [0]); ("f", 1, [1; 0])]; predicates := [("p", [0])] |}).
  vm_compute. reflexivity.
Qed.

(** The infinite chain refutes both formulas for any predicate. *)
Lemma chain_p : ~ lj Calculus.intuitionistic [] (neg (neg (fall (vee (p x) (neg (p x)))))).
Proof. exact (chain_excluded_middle _ "p"). Qed.

(** And the double-negation shift, in LM. *)
Lemma chain_shift_p : ~ lj Calculus.minimal [] (imp (fall (neg (neg (p x)))) (neg (neg (fall (p x))))).
Proof. exact (chain_double_negation_shift _ "p"). Qed.

(** The model of [not_forall], to break one condition at a time. *)
Definition good : kripke_model string :=
  {| later := [[1]; []]; sizes := [1; 2]; tables := [[]; []];
     facts := [[]; [("p", [0])]]; absurd := [] |}.

Lemma good_refutes :
  krefutes String.eqb good Calculus.intuitionistic 0 [neg (fall (p x))] (fex (neg (p x))) = true.
Proof. vm_compute. reflexivity. Qed.

(** A domain that shrinks along the order. *)
Lemma shrinking_domain :
  krefutes String.eqb {| later := [[1]; []]; sizes := [2; 1]; tables := [[]; []];
                         facts := [[]; [("p", [0])]]; absurd := [] |}
    Calculus.intuitionistic 0 [neg (fall (p x))] (fex (neg (p x))) = false.
Proof. vm_compute. reflexivity. Qed.

(** An empty domain. *)
Lemma empty_domain :
  krefutes String.eqb {| later := [[1]; []]; sizes := [0; 2]; tables := [[]; []];
                         facts := [[]; [("p", [0])]]; absurd := [] |}
    Calculus.intuitionistic 0 [neg (fall (p x))] (fex (neg (p x))) = false.
Proof. vm_compute. reflexivity. Qed.

(** A fact that a later world drops. *)
Lemma dropped_fact :
  krefutes String.eqb {| later := [[1]; []]; sizes := [1; 2]; tables := [[]; []];
                         facts := [[("p", [0])]; []]; absurd := [] |}
    Calculus.intuitionistic 0 [] (fex (neg (p x))) = false.
Proof. vm_compute. reflexivity. Qed.

(** An order that is not transitive. *)
Lemma not_transitive :
  krefutes String.eqb {| later := [[1]; [2]; []]; sizes := [1; 1; 1]; tables := [[]; []; []];
                         facts := [[]; []; [("p", [0])]]; absurd := [] |}
    Calculus.intuitionistic 0 [] (fex (neg (p x))) = false.
Proof. vm_compute. reflexivity. Qed.

(** A later world past the model's worlds. *)
Lemma world_past :
  krefutes String.eqb {| later := [[2]; []]; sizes := [1; 1]; tables := [[]; []];
                         facts := [[]; []]; absurd := [] |}
    Calculus.intuitionistic 0 [] (p a) = false.
Proof. vm_compute. reflexivity. Qed.

(** A table value outside its world's domain. *)
Lemma value_outside :
  krefutes String.eqb {| later := [[1]; []]; sizes := [1; 2];
                         tables := [[("a", 0, [1])]; [("a", 0, [1])]];
                         facts := [[]; [("p", [1])]]; absurd := [] |}
    Calculus.intuitionistic 0 [] (p a) = false.
Proof. vm_compute. reflexivity. Qed.

(** A later world that changes a value on the earlier world's
    elements. *)
Lemma disagreeing_function :
  krefutes String.eqb {| later := [[1]; []]; sizes := [1; 2];
                         tables := [[("a", 0, [0])]; [("a", 0, [1])]];
                         facts := [[]; [("p", [1])]]; absurd := [] |}
    Calculus.intuitionistic 0 [] (neg (neg (p a))) = false.
Proof. vm_compute. reflexivity. Qed.

(** A table that only the later world has, with a value other than the
    earlier world's default [0]. *)
Lemma table_only_later :
  krefutes String.eqb {| later := [[1]; []]; sizes := [1; 2];
                         tables := [[]; [("a", 0, [1])]];
                         facts := [[]; [("p", [1])]]; absurd := [] |}
    Calculus.intuitionistic 0 [] (neg (neg (p a))) = false.
Proof. vm_compute. reflexivity. Qed.

(** A world that forces [⊥] in LJ. *)
Lemma absurd_in_lj :
  krefutes String.eqb {| later := [[1]; []]; sizes := [1; 1]; tables := [[("a", 0, [0])]; [("a", 0, [0])]];
                         facts := [[]; []]; absurd := [1] |}
    Calculus.intuitionistic 0 [] (neg (neg (imp bot (p a)))) = false.
Proof. vm_compute. reflexivity. Qed.

(** [⊥] that a later world drops, in LM. *)
Lemma dropped_absurd :
  krefutes String.eqb {| later := [[1]; []]; sizes := [1; 1]; tables := [[]; []];
                         facts := [[]; []]; absurd := [0] |}
    Calculus.minimal 0 [] (p a) = false.
Proof. vm_compute. reflexivity. Qed.

(** A size missing from the list. *)
Lemma missing_size :
  krefutes String.eqb {| later := [[1]; []]; sizes := [1]; tables := [[]; []];
                         facts := [[]; [("p", [0])]]; absurd := [] |}
    Calculus.intuitionistic 0 [neg (fall (p x))] (fex (neg (p x))) = false.
Proof. vm_compute. reflexivity. Qed.

(** A world that forces the conclusion. *)
Lemma forces_conclusion :
  krefutes String.eqb good Calculus.intuitionistic 1 [] (fex (p x)) = false.
Proof. vm_compute. reflexivity. Qed.

(** A world past the model. *)
Lemma refuting_world_past :
  krefutes String.eqb good Calculus.intuitionistic 2 [] (p a) = false.
Proof. vm_compute. reflexivity. Qed.

(** A structure without elements. *)
Lemma empty_structure :
  srefutes String.eqb {| size := 0; functions := []; predicates := [] |} [] [fex (p x)] = false.
Proof. vm_compute. reflexivity. Qed.

(** A structure's value outside its domain. *)
Lemma structure_value_outside :
  srefutes String.eqb {| size := 1; functions := [("a", 0, [1])]; predicates := [] |} [] [p a] = false.
Proof. vm_compute. reflexivity. Qed.

(** A structure that makes a formula of the right side true. *)
Lemma structure_makes_true :
  srefutes String.eqb {| size := 2; functions := []; predicates := [("p", [0])] |} [] [fex (p x)] = false.
Proof. vm_compute. reflexivity. Qed.

(** A quantifier is decided at its first element that settles it: eight
    nested [∀] over eleven elements, false at the first, compile at
    once. *)
Lemma stops_early :
  ~ lk true [] [fall (fall (fall (fall (fall (fall (fall (fall r)))))))].
Proof.
  apply (fo_classical_refutation String.eqb true
           {| size := 11; functions := []; predicates := [] |}).
  vm_compute. reflexivity.
Qed.

(** The same through a Kripke model of one world. *)
Lemma kripke_stops_early :
  ~ lj Calculus.intuitionistic [] (fall (fall (fall (fall (fall (fall (fall (fall r)))))))).
Proof.
  apply (fo_kripke_refutation String.eqb String.eqb_spec _
           {| later := [[]]; sizes := [11]; tables := [[]]; facts := [[]]; absurd := [] |} 0).
  vm_compute. reflexivity.
Qed.
