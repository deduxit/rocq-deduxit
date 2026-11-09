(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** Certificates of non-derivability by weighted counts, in the form the
    exporter writes: the sequent stated not derivable over [ll] or [ill],
    proved by a refutation theorem from weights, dead atoms and, with
    weakening, the sign of the outputs, which a test accepts by
    computation. The classical reading, the balance and the count
    equation refute none of them but [one_sided_negative]. The last
    lemmas pin what the tests reject. *)

From Stdlib Require Import List String ZArith.
From Deduxit.Linear Require Import Weights.
Import ListNotations.
Open Scope string_scope.

(** The one-sided count: [!d, !((c ⊗ d ⊗ d) ⊸ 1) ⊢ c ⊗ c], where every
    copy adds a positive [c] and two are wanted outside the copies. *)
Lemma one_sided_two_sided :
  ~ ill (atom := string) intuitionistic
      [ioc (ivar "d"); ioc (ilmap (itens (ivar "c") (itens (ivar "d") (ivar "d"))) ione)]
      (itens (ivar "c") (ivar "c")).
Proof.
  apply (iweighted_refutation (weight_of String.eqb [("c", 1%Z)])
    (fun a => existsb (String.eqb a) []) true intuitionistic).
  vm_compute. reflexivity.
Qed.

(** The same one-sided, with Mix. *)
Lemma one_sided_mix :
  ~ ll (atom := string) {| mix := true; weakening := false; cut := false |}
      [tens (var "c") (var "c"); wn (covar "d");
       wn (tens (tens (var "c") (tens (var "d") (var "d"))) bot)].
Proof.
  apply (weighted_refutation (weight_of String.eqb [("c", 1%Z)])
    (fun a => existsb (String.eqb a) []) true _).
  vm_compute. reflexivity.
Qed.

(** Copies of the negative literal: [⊢ ~a ⊗ ~a, ?(~a ⊗ b), ~b], the
    weight [-1] on [a]. *)
Lemma one_sided_negative :
  ~ ll (atom := string) classical
      [tens (covar "a") (covar "a"); wn (tens (covar "a") (var "b")); covar "b"].
Proof.
  apply (weighted_refutation (weight_of String.eqb [("a", (-1)%Z)])
    (fun a => existsb (String.eqb a) []) true classical).
  vm_compute. reflexivity.
Qed.

(** The state equation: [a, !(a ⊗ a ⊸ b), !(c ⊸ c ⊗ a) ⊢ a ⊗ b], where
    a [b] costs two [a]s and the second clause never fires, since nothing
    makes a [c]. With it, the equation has a solution. *)
Lemma state_equation_dead :
  ~ ill (atom := string) intuitionistic
      [ivar "a"; ioc (ilmap (itens (ivar "a") (ivar "a")) (ivar "b"));
       ioc (ilmap (ivar "c") (itens (ivar "c") (ivar "a")))]
      (itens (ivar "a") (ivar "b")).
Proof.
  apply (iweighted_refutation (weight_of String.eqb [("a", 1%Z); ("b", 2%Z)])
    (fun a => existsb (String.eqb a) ["c"]) true intuitionistic).
  vm_compute. reflexivity.
Qed.

(** The same with the bodies negative, as a classical one-sided Horn
    program may write them: [⊢ a, ?(~a ⊗ (a ⅋ a)), ?((~a ⊗ ~c) ⊗ b), ~b],
    the weights negated and [c] dead in the negative sign, so that the
    clause that never fires contributes nothing. *)
Lemma state_equation_negative_bodies :
  ~ ll (atom := string) classical
      [var "a"; wn (tens (covar "a") (parr (var "a") (var "a")));
       wn (tens (tens (covar "a") (covar "c")) (var "b")); covar "b"].
Proof.
  apply (weighted_refutation (weight_of String.eqb [("b", (-1)%Z)])
    (fun a => existsb (String.eqb a) ["c"]) false classical).
  vm_compute. reflexivity.
Qed.

(** Coverability with weakening: [a, a ⊸ b ⊗ b ⊢ b ⊗ b ⊗ b], three [b]s
    from two. *)
Lemma state_equation_affine :
  ~ ill (atom := string) affine
      [ivar "a"; ilmap (ivar "a") (itens (ivar "b") (ivar "b"))]
      (itens (ivar "b") (itens (ivar "b") (ivar "b"))).
Proof.
  apply (iaffine_refutation (weight_of String.eqb [("a", 2%Z); ("b", 1%Z)])
    (fun a => existsb (String.eqb a) []) true affine).
  vm_compute. reflexivity.
Qed.

(** The same one-sided with the outputs negative, as a Horn program
    whose bodies are negative literals writes it. *)
Lemma state_equation_affine_negative :
  ~ ll (atom := string) {| mix := false; weakening := true; cut := false |}
      [var "a"; tens (covar "a") (parr (var "b") (var "b"));
       tens (covar "b") (tens (covar "b") (covar "b"))].
Proof.
  apply (affine_refutation (weight_of String.eqb [("a", (-2)%Z); ("b", (-1)%Z)])
    (fun a => existsb (String.eqb a) []) false _).
  vm_compute. reflexivity.
Qed.

(** Without the dead atom the copies of the second clause lower the
    count without bound. *)
Lemma state_equation_needs_dead :
  overweight (atom := string) (weight_of String.eqb [("a", 1%Z); ("b", 2%Z)]) (fun _ => false) true
    (lrules intuitionistic)
    (one_sided
      [ivar "a"; ioc (ilmap (itens (ivar "a") (ivar "a")) (ivar "b"));
       ioc (ilmap (ivar "c") (itens (ivar "c") (ivar "a")))]
      (itens (ivar "a") (ivar "b"))) = false.
Proof. vm_compute. reflexivity. Qed.

(** With the dead sign wrong, the clause that never fires absorbs and
    the test refuses. *)
Lemma negative_bodies_wrong_sign :
  overweight (atom := string) (weight_of String.eqb [("b", (-1)%Z)])
    (fun a => existsb (String.eqb a) ["c"]) true classical
    [var "a"; wn (tens (covar "a") (parr (var "a") (var "a")));
     wn (tens (tens (covar "a") (covar "c")) (var "b")); covar "b"] = false.
Proof. vm_compute. reflexivity. Qed.

(** A derivable sequent, [a, !(a ⊸ b) ⊢ b], is refuted by no weights. *)
Lemma derivable_not_overweight :
  overweight (atom := string) (weight_of String.eqb [("a", 1%Z); ("b", 1%Z)]) (fun _ => false) true
    (lrules intuitionistic)
    (one_sided [ivar "a"; ioc (ilmap (ivar "a") (ivar "b"))] (ivar "b")) = false.
Proof. vm_compute. reflexivity. Qed.

(** A [⊤] absorbs: [⊢ ⊤, c ⊗ c] is derivable. *)
Lemma top_not_overweight :
  overweight (atom := string) (weight_of String.eqb [("c", 1%Z)]) (fun _ => false) true classical
    [top; tens (var "c") (var "c")] = false.
Proof. vm_compute. reflexivity. Qed.

(** The test without drops refuses a calculus with weakening. *)
Lemma weakening_not_overweight :
  overweight (atom := string) (weight_of String.eqb [("a", 2%Z); ("b", 1%Z)]) (fun _ => false) true
    (lrules affine)
    (one_sided [ivar "a"; ilmap (ivar "a") (itens (ivar "b") (ivar "b"))]
      (itens (ivar "b") (itens (ivar "b") (ivar "b")))) = false.
Proof. vm_compute. reflexivity. Qed.

(** With the outputs' sign wrong the affine test refuses: the goal has
    no output then. *)
Lemma affine_wrong_sign :
  overweight_affine (atom := string) (weight_of String.eqb [("a", 2%Z); ("b", 1%Z)])
    (fun _ => false) false (lrules affine)
    (one_sided [ivar "a"; ilmap (ivar "a") (itens (ivar "b") (ivar "b"))]
      (itens (ivar "b") (itens (ivar "b") (ivar "b")))) = false.
Proof. vm_compute. reflexivity. Qed.

(** Affine and derivable: [a, b ⊢ a], which weakens [b]. *)
Lemma affine_derivable_not_overweight :
  overweight_affine (atom := string) (weight_of String.eqb [("a", 1%Z); ("b", 1%Z)])
    (fun _ => false) true (lrules affine) (one_sided [ivar "a"; ivar "b"] (ivar "a")) = false.
Proof. vm_compute. reflexivity. Qed.
