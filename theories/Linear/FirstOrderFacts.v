(* deduxit © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** * Facts of first-order formulas

    [FirstOrderFormulas] holds definitions alone, as the files a
    certificate's statement rests on do. These are the facts of its
    definitions that the soundness proof and the weighted counts both
    need. Each of those keeps its name for them, as an instance. *)

From Stdlib Require Import Bool List.
From Deduxit.Linear Require Import FirstOrderFormulas.

Section Facts.

Context {symbol : Type}.

Lemma dual_dual : forall A : formula symbol, dual (dual A) = A.
Proof. intros A; induction A; cbn; congruence. Qed.

Lemma dual_subst : forall (A : formula symbol) k u, dual (subst k u A) = subst k u (dual A).
Proof. intros A; induction A; intros k u; cbn; congruence. Qed.

Lemma occurs_dual : forall b (A : formula symbol), occurs b (dual A) = occurs b A.
Proof. intros b A; induction A; cbn; congruence. Qed.

End Facts.
