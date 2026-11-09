(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** Certificates of non-derivability of first-order sequents by
    weighted counts: weights per predicate, or per closed atom of a
    fixed predicate, which a test accepts by computation. The last
    lemmas check what the test rejects. *)

From Stdlib Require Import List String ZArith.
From Deduxit.Linear Require Calculus Intuitionistic TermsCheck.
From Deduxit.Linear Require Import FirstOrderCalculus FirstOrderIntuitionistic FirstOrderWeights.
Import ListNotations.
Open Scope string_scope.

(** The constant [c]. *)
Definition c : term string := tapp "c" [].

(** The constant [d]. *)
Definition d : term string := tapp "d" [].

(** Counted over all atoms of [p]:
    [!(∀x. q(x)), !(∀x. (p(x) ⊗ q(x) ⊗ q(x)) ⊸ 1) ⊢ ∃x. p(x) ⊗ p(x)].
    Every copy adds a positive [p], and the goal needs two more outside
    the copies. *)
Lemma one_sided_symbol :
  ~ ill (symbol := string) Intuitionistic.intuitionistic
      [ioc (iall (ivar "q" [bound 0]));
       ioc (iall (ilmap (itens (ivar "p" [bound 0])
         (itens (ivar "q" [bound 0]) (ivar "q" [bound 0]))) ione))]
      (iex (itens (ivar "p" [bound 0]) (ivar "p" [bound 0]))).
Proof.
  apply (iweighted_refutation (fun _ => false) (fun _ _ => 0%Z)
    (fun p => if String.eqb p "p" then 1%Z else 0%Z) Intuitionistic.intuitionistic).
  vm_compute. reflexivity.
Qed.

(** Counted over the atom [p(c)] alone, its predicate fixed: [⊢ p(c) ⊗
    p(c), ?p(c), p(d)⊥, p(d)⊥, p(d)⊥, ∃x. q(x)], which the count over
    all of [p] does not refute. *)
Lemma one_sided_atom :
  ~ ll (symbol := string) Calculus.classical
      [tens (var "p" [c]) (var "p" [c]); wn (var "p" [c]);
       covar "p" [d]; covar "p" [d]; covar "p" [d]; fex (var "q" [bound 0])].
Proof.
  apply (weighted_refutation (fun p => String.eqb p "p")
    (fun p ts => if TermsCheck.terms_eqb String.eqb ts [c] then 1%Z else 0%Z)
    (fun _ => 0%Z) Calculus.classical).
  vm_compute. reflexivity.
Qed.

(** Counted over all of [p], the same sequent is not refuted. *)
Lemma one_sided_atom_needs_fixed :
  overweight (symbol := string) (fun _ => false) (fun _ _ => 0%Z)
    (fun p => if String.eqb p "p" then 1%Z else 0%Z) Calculus.classical
    [tens (var "p" [c]) (var "p" [c]); wn (var "p" [c]);
     covar "p" [d]; covar "p" [d]; covar "p" [d]; fex (var "q" [bound 0])] = false.
Proof. vm_compute. reflexivity. Qed.

(** The test refuses a fixed predicate with a literal under a
    quantifier, since an instance may turn it into the atom
    weighed. *)
Lemma unpinned_not_overweight :
  overweight (symbol := string) (fun p => String.eqb p "p")
    (fun p ts => if TermsCheck.terms_eqb String.eqb ts [c] then 1%Z else 0%Z)
    (fun _ => 0%Z) Calculus.classical
    [tens (var "p" [c]) (var "p" [c]); fall (covar "p" [bound 0])] = false.
Proof. vm_compute. reflexivity. Qed.
