(** Project a growing represented conjunction into a synchronized pair.

    Both projections reuse the target context already selected by the
    conjunction producer.  Consequently this adapter allocates no witnesses,
    performs no context merge, and preserves the source inclusion verbatim.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
  RawCodedLtSuccCasesProofCompilation
  RawCodedPAGrowingTemplateConjunction
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail.

Module PABoundedRawCodedPAGrowingTemplateConjunctionProjection.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedPAGrowingTemplateConjunction.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.

Theorem raw_codedPAGrowingTemplateLocalProofPairAt_of_and : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext prefix left right,
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext prefix
    (rawFormulaAndCode M left right) ->
  RawCodedPAGrowingTemplateLocalProofPairAt M translation
    sourceContext prefix left right.
Proof.
  intros M hPA translation sourceWitnessList sourceContext prefix
    left right
    (targetWitnessList & targetContext & conjunctionRoot &
      htargetWitnessed & hsourceTargetIncluded & hconjunction).
  pose proof
    (raw_codedPALocalProofOf_andE1 M hPA
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      left right conjunctionRoot hconjunction) as hleft.
  pose proof
    (raw_codedPALocalProofOf_andE2 M hPA
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      left right conjunctionRoot hconjunction) as hright.
  lazymatch type of hleft with
  | RawCodedPALocalProofOf _ _ _ ?leftRoot =>
      lazymatch type of hright with
      | RawCodedPALocalProofOf _ _ _ ?rightRoot =>
          exists targetWitnessList, targetContext, leftRoot, rightRoot;
          split; [exact htargetWitnessed |];
          split; [exact hsourceTargetIncluded |];
          split; assumption
      end
  end.
Qed.

End PABoundedRawCodedPAGrowingTemplateConjunctionProjection.
