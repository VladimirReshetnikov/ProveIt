(** True arithmetic as the complete theory of the standard natural model. *)

From FoundationModal Require Import GenericAdjunctiveSet GenericEntailment.
From Foundation.Syntax.Predicate Require Import Language.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Soundness.
From Foundation.FirstOrder.Basic.Semantics Require Import ModelTheory.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Model Hierarchy.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition first_order_true_arithmetic : theory oring_language :=
  first_order_model_theory nat_standard_model.

Lemma first_order_true_arithmetic_models :
  first_order_models_theory nat_standard_model first_order_true_arithmetic.
Proof. apply first_order_model_models_own_theory. Qed.

Theorem first_order_true_arithmetic_provable_iff :
  forall sigma : sentence oring_language,
    first_order_theory_provable first_order_true_arithmetic sigma <->
    first_order_model_realize nat_standard_model sigma.
Proof.
  intro sigma; split.
  - apply first_order_models_of_provable.
    exact first_order_true_arithmetic_models.
  - intro Hsigma.
    exact (@generic_axiomatized_by_axiom
      (theory oring_language) (sentence oring_language)
      (first_order_theory_entailment oring_language)
      (generic_predicate_adjunctive_set (sentence oring_language))
      (first_order_theory_axiomatized oring_language)
      first_order_true_arithmetic sigma Hsigma).
Qed.

Theorem arithmetic_theory_weaker_than_true_arithmetic :
  forall T : theory oring_language,
    first_order_models_theory nat_standard_model T ->
    generic_weaker_than
      (first_order_theory_entailment oring_language)
      (first_order_theory_entailment oring_language)
      T first_order_true_arithmetic.
Proof.
  intros T Hmodels. constructor. intros sigma Hproof.
  apply (proj2 (first_order_true_arithmetic_provable_iff sigma)).
  exact (first_order_models_of_provable Hmodels Hproof).
Qed.
