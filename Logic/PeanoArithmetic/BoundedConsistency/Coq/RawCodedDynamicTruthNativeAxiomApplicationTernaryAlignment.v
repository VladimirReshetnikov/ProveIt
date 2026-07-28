(**
  Identify the native PA-axiom application with generic ternary application.

  The native axiom-soundness graph specializes a graph-selected global
  truth predicate at [(axiom, 0, 0)] by three represented single
  substitutions.  The generic template application instead starts with the
  three unshifted argument terms and explicitly shifts the first two before
  performing those substitutions.

  This module proves that the two relations are exactly equivalent.  The
  reverse direction is not a definitional unpacking: its shift witnesses can
  be arbitrary represented outputs.  Term-shift functionality identifies
  them with the standard quotations of [#2] and [0], after which the three
  substitution traces are literally the native traces.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedTermShiftSyntaxRealization
  RawCodedTermOperationsStandardAdequacy
  RawCodedTermOperationCrossTraceFunctionality
  RawCodedTemplateTernaryApplication
  RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.

Module
  PABoundedRawCodedDynamicTruthNativeAxiomApplicationTernaryAlignment.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermShiftSyntaxRealization.
Import PABoundedRawCodedTermOperationsStandardAdequacy.
Import PABoundedRawCodedTermOperationCrossTraceFunctionality.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.

(** The first generic argument is the surviving axiom variable.  Generic
    ternary application shifts it by two before the first opening; the two
    zero arguments are closed and therefore unchanged by their shifts. *)
Theorem raw_dynamicTruthNativeAxiomApplication_ternary_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall predicate output,
  RawDynamicTruthNativeAxiomApplication M predicate output <->
  RawCodedTernaryApplication M predicate
    (rawQuotedTermCode M (tVar 0))
    (rawQuotedTermCode M tZero)
    (rawQuotedTermCode M tZero)
    output.
Proof.
  intros M hPA predicate output.
  split.
  - intros (firstResult & secondResult &
      hfirstSubstitution & hsecondSubstitution & hthirdSubstitution).
    exists (rawQuotedTermCode M (tVar 2)),
      (rawQuotedTermCode M tZero), firstResult, secondResult.
    repeat split.
    + change (RawCodedTermShift M
        (rawNumeralValue M 0) (rawNumeralValue M 2)
        (rawQuotedTermCode M (tVar 0))
        (rawQuotedTermCode M
          (standardTermShift 0 2 (tVar 0)))).
      exact (raw_codedTermShift_standard M hPA 0 2 (tVar 0)).
    + change (RawCodedTermShift M
        (rawNumeralValue M 0) (rawNumeralValue M 1)
        (rawQuotedTermCode M tZero)
        (rawQuotedTermCode M
          (standardTermShift 0 1 tZero))).
      exact (raw_codedTermShift_standard M hPA 0 1 tZero).
    + rewrite rawQuotedTermCode_standard by exact hPA.
      exact hfirstSubstitution.
    + rewrite rawQuotedTermCode_standard by exact hPA.
      exact hsecondSubstitution.
    + rewrite rawQuotedTermCode_standard by exact hPA.
      exact hthirdSubstitution.
  - intros (firstLifted & secondLifted & firstResult & secondResult &
      hfirstShift & hsecondShift & hfirstSubstitution &
      hsecondSubstitution & hthirdSubstitution).
    assert (hfirstStandard : RawCodedTermShift M
        (rawNumeralValue M 0) (rawNumeralValue M 2)
        (rawQuotedTermCode M (tVar 0))
        (rawQuotedTermCode M (tVar 2))).
    {
      change (RawCodedTermShift M
        (rawNumeralValue M 0) (rawNumeralValue M 2)
        (rawQuotedTermCode M (tVar 0))
        (rawQuotedTermCode M
          (standardTermShift 0 2 (tVar 0)))).
      exact (raw_codedTermShift_standard M hPA 0 2 (tVar 0)).
    }
    assert (hsecondStandard : RawCodedTermShift M
        (rawNumeralValue M 0) (rawNumeralValue M 1)
        (rawQuotedTermCode M tZero)
        (rawQuotedTermCode M tZero)).
    {
      change (RawCodedTermShift M
        (rawNumeralValue M 0) (rawNumeralValue M 1)
        (rawQuotedTermCode M tZero)
        (rawQuotedTermCode M
          (standardTermShift 0 1 tZero))).
      exact (raw_codedTermShift_standard M hPA 0 1 tZero).
    }
    pose proof (raw_codedTermShift_functional M hPA
      (rawNumeralValue M 0) (rawNumeralValue M 2)
      (rawQuotedTermCode M (tVar 0))
      firstLifted (rawQuotedTermCode M (tVar 2))
      hfirstShift hfirstStandard) as hfirstLifted.
    pose proof (raw_codedTermShift_functional M hPA
      (rawNumeralValue M 0) (rawNumeralValue M 1)
      (rawQuotedTermCode M tZero)
      secondLifted (rawQuotedTermCode M tZero)
      hsecondShift hsecondStandard) as hsecondLifted.
    subst firstLifted. subst secondLifted.
    exists firstResult, secondResult.
    repeat split.
    + rewrite rawQuotedTermCode_standard in hfirstSubstitution by exact hPA.
      exact hfirstSubstitution.
    + rewrite rawQuotedTermCode_standard in hsecondSubstitution by exact hPA.
      exact hsecondSubstitution.
    + rewrite rawQuotedTermCode_standard in hthirdSubstitution by exact hPA.
      exact hthirdSubstitution.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeAxiomApplicationTernaryAlignment.
