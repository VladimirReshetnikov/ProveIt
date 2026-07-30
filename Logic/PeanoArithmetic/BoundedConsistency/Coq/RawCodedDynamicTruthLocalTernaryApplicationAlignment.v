(**
  Align the native local three-opening relation with generic ternary
  application.

  The local dynamic-truth field historically spells its application out as
  three substitutions by the fixed term codes [#4], [#2], and [#0].  The
  reusable ternary interface instead starts from arguments [#2], [#1], and
  [#0] and records the two protective shifts explicitly.  Represented term-
  shift functionality proves that these are exactly the same relation.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedTermOperationsStandardAdequacy
  RawCodedTermOperationCrossTraceFunctionality
  RawCodedTemplateTernaryApplication
  RawCodedDynamicTruthNativeLocalPositiveGraph.

Module PABoundedRawCodedDynamicTruthLocalTernaryApplicationAlignment.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermOperationsStandardAdequacy.
Import PABoundedRawCodedTermOperationCrossTraceFunctionality.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.

(** The equivalence is completely predicate- and output-generic.  It can be
    reused for the standard rank-zero base as well as nonstandard successor
    predicates selected by the native orbit. *)
Theorem raw_dynamicTruthLocalTernaryApplication_ternary_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall predicate output,
  RawDynamicTruthLocalTernaryApplication M predicate output <->
  RawCodedTernaryApplication M predicate
    (rawQuotedTermCode M (tVar 2))
    (rawQuotedTermCode M (tVar 1))
    (rawQuotedTermCode M (tVar 0)) output.
Proof.
  intros M hPA predicate output.
  split.
  - intros (firstResult & secondResult & hfirstSubstitution &
      hsecondSubstitution & hthirdSubstitution).
    exists (rawQuotedTermCode M (tVar 4)),
      (rawQuotedTermCode M (tVar 2)), firstResult, secondResult.
    repeat split.
    + change (RawCodedTermShift M
        (rawNumeralValue M 0) (rawNumeralValue M 2)
        (rawQuotedTermCode M (tVar 2))
        (rawQuotedTermCode M
          (standardTermShift 0 2 (tVar 2)))).
      exact (raw_codedTermShift_standard M hPA 0 2 (tVar 2)).
    + change (RawCodedTermShift M
        (rawNumeralValue M 0) (rawNumeralValue M 1)
        (rawQuotedTermCode M (tVar 1))
        (rawQuotedTermCode M
          (standardTermShift 0 1 (tVar 1)))).
      exact (raw_codedTermShift_standard M hPA 0 1 (tVar 1)).
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
        (rawQuotedTermCode M (tVar 2))
        (rawQuotedTermCode M (tVar 4))).
    {
      change (RawCodedTermShift M
        (rawNumeralValue M 0) (rawNumeralValue M 2)
        (rawQuotedTermCode M (tVar 2))
        (rawQuotedTermCode M
          (standardTermShift 0 2 (tVar 2)))).
      exact (raw_codedTermShift_standard M hPA 0 2 (tVar 2)).
    }
    assert (hsecondStandard : RawCodedTermShift M
        (rawNumeralValue M 0) (rawNumeralValue M 1)
        (rawQuotedTermCode M (tVar 1))
        (rawQuotedTermCode M (tVar 2))).
    {
      change (RawCodedTermShift M
        (rawNumeralValue M 0) (rawNumeralValue M 1)
        (rawQuotedTermCode M (tVar 1))
        (rawQuotedTermCode M
          (standardTermShift 0 1 (tVar 1)))).
      exact (raw_codedTermShift_standard M hPA 0 1 (tVar 1)).
    }
    pose proof (raw_codedTermShift_functional M hPA
      (rawNumeralValue M 0) (rawNumeralValue M 2)
      (rawQuotedTermCode M (tVar 2)) firstLifted
      (rawQuotedTermCode M (tVar 4))
      hfirstShift hfirstStandard) as hfirstLifted.
    pose proof (raw_codedTermShift_functional M hPA
      (rawNumeralValue M 0) (rawNumeralValue M 1)
      (rawQuotedTermCode M (tVar 1)) secondLifted
      (rawQuotedTermCode M (tVar 2))
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

End PABoundedRawCodedDynamicTruthLocalTernaryApplicationAlignment.
