(**
  Provability representation for arithmetically semidecidable predicates.

  This is the proof-theoretic endpoint of the R0 representation layer.  A
  certified semidecision procedure first supplies a Sigma-one formula whose
  standard-natural interpretation is the predicate.  Sigma-one completeness
  for numeral parameters then identifies that interpretation with provability
  in every Sigma-one-sound extension of R0.
*)

From Stdlib Require Import Vectors.Fin.
From FoundationModal Require Import GenericEntailment.
From Foundation.Syntax.Predicate Require Import Language.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import
  Hierarchy Misc Model.
From Foundation.FirstOrder.Arithmetic.R0 Require Import Basic Representation.
From Foundation.FirstOrder.Arithmetic.Definability Require Import
  Absoluteness.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Source theorem [re_complete], stated for the constructive arithmetic
    semidecidability certificate used by the Coq representation compiler. *)
Theorem r0_arithmetically_semidecidable_provability_representation : forall
    (T : theory oring_language),
  generic_weaker_than
    (first_order_theory_entailment oring_language)
    (first_order_theory_entailment oring_language) r0_axiom T ->
  arithmetic_theory_sound_on_hierarchy T arithmetic_sigma 1 ->
  forall n (P : (Fin.t n -> nat) -> Prop),
    arithmetically_semidecidable P ->
    exists p : arithmetic_semisentence n,
      arithmetic_hierarchy Empty_set arithmetic_sigma 1 n p /\
      forall v,
        (P v <->
         first_order_theory_provable T
           (arithmetic_numeral_instance p v)).
Proof.
  intros T Hweak Hsound n P Hsemi.
  destruct (r0_arithmetically_semidecidable_representation Hsemi)
    as [p [Hp Hrep]].
  exists p. split; [exact Hp |].
  intro v.
  transitivity
    (semiformula_eval nat_standard_structure v
       (@r0_empty_free_env nat) p).
  - symmetry. apply Hrep.
  - exact
      (arithmetic_sigma_one_provable_iff_with_numeral_parameters
        Hweak Hsound Hp v).
Qed.
