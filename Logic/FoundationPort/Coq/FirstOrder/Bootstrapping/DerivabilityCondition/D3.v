(**
  Standard-natural Sigma-one completeness for executable proof codes.

  This is the standard-model core of Hilbert--Bernays D3 from the source.  It
  composes R0 Sigma-one completeness with checked proof serialization.  The
  hypotheses are weakened from a fixed PA-minus extension to any theory
  proof-theoretically weaker than R0, or merely containing each R0 axiom.
*)

From FoundationModal Require Import GenericEntailment.
From Foundation.Syntax.Predicate Require Import Language.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Coding Calculus.
From Foundation.FirstOrder.Basic.Semantics Require Import ModelTheory.
From Foundation.FirstOrder.Arithmetic.Basic Require Import
  Misc Syntax Model Hierarchy.
From Foundation.FirstOrder.Arithmetic.R0 Require Import Basic.
From Foundation.FirstOrder.Bootstrapping.Syntax Require Import Theory.
From Foundation.FirstOrder.Bootstrapping.DerivabilityCondition Require Import D1.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Theorem boot_r0_sigma_one_complete : forall
    (T : theory oring_language)
    (EL : language_encodable oring_language)
    (ET : boot_theory_encoding EL T)
    (sigma : sentence oring_language),
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language) r0_axiom T ->
  arithmetic_hierarchy Empty_set arithmetic_sigma 1 0 sigma ->
  first_order_model_realize nat_standard_model sigma ->
  @boot_sentence_provable oring_language EL T ET sigma.
Proof.
  intros T EL ET sigma Hweak Hsigma Htrue.
  apply boot_internalize_provability.
  exact (r0_sigma_one_proof_complete Hweak Hsigma Htrue).
Qed.

Corollary boot_r0_sigma_one_complete_of_subset : forall
    (T : theory oring_language)
    (EL : language_encodable oring_language)
    (ET : boot_theory_encoding EL T)
    (sigma : sentence oring_language),
  (forall axiom, r0_axiom axiom -> T axiom) ->
  arithmetic_hierarchy Empty_set arithmetic_sigma 1 0 sigma ->
  first_order_model_realize nat_standard_model sigma ->
  @boot_sentence_provable oring_language EL T ET sigma.
Proof.
  intros T EL ET sigma Hsub Hsigma Htrue.
  apply (@boot_r0_sigma_one_complete T EL ET sigma); try assumption.
  now apply first_order_theory_weaker_of_subset.
Qed.

(** With Sigma-one soundness the standard result is exact, not merely a
    completeness implication. *)
Theorem boot_r0_sigma_one_provable_iff : forall
    (T : theory oring_language)
    (EL : language_encodable oring_language)
    (ET : boot_theory_encoding EL T),
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language) r0_axiom T ->
  arithmetic_theory_sound_on_hierarchy T arithmetic_sigma 1 ->
  forall sigma : sentence oring_language,
    arithmetic_hierarchy Empty_set arithmetic_sigma 1 0 sigma ->
    (first_order_model_realize nat_standard_model sigma <->
     @boot_sentence_provable oring_language EL T ET sigma).
Proof.
  intros T EL ET Hweak Hsound sigma Hsigma.
  rewrite (@boot_sentence_provable_iff_theory
    oring_language T EL ET sigma).
  exact (r0_sigma_one_provable_iff Hweak Hsound Hsigma).
Qed.
