(**
  Selection of one synchronized witnessed tail for both And-I child roots.

  The represented source producer supplies a common witness prefix.  Context
  alignment then transports its root into the opened-coverage compiler, so
  both recursive child interfaces are selected on exactly that same tail.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  PolynomialPairInjectivity
  RawModelCompleteness
  RawCodedAssignment
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedContextLists
  RawCodedProofConstructors
  RawCodedProofDescent
  RawCodedProofTraversal
  RawCodedProofEndpoints
  RawCodedProofRules
  RawCodedProofAndIConstructor
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedRestrictedPAProof
  RawCodedRestrictedProofAdmissibility
  RawCodedCarrierRestrictedProofReroot
  RawCodedRestrictedPADerivationSoundnessRecursiveChildInterface
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedTargetTemplateSemantics
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedPALocalProofUniversalSourceInstance
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplateParameterAbstraction
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildInterfaceSemanticCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildCoreExtraction
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildTailContextAlignment
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildTailSourceProduction.

Import ListNotations.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildTailSelection.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedProofAdmissibility.
Import PABoundedRawCodedCarrierRestrictedProofReroot.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildInterface.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedTargetTemplateSemantics.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedPALocalProofUniversalSourceInstance.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixInductionShell.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildInterfaceSemanticCompilation.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceCompilation.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildCoreExtraction.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildTailContextAlignment.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildTailSourceProduction.

Definition RawCoqRestrictedPADirectSelectedAndIntroductionChildCoreTail
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectAndIntroductionChildCoreRoots
      M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Arguments RawCoqRestrictedPADirectSelectedAndIntroductionChildCoreTail
  M hPA inputs : clear implicits.

Theorem raw_selectedAndIntroductionChildCoreTail : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedAndIntroductionChildCoreTail
    M hPA inputs.
Proof.
  intros M hPA inputs.
  assert (hempty : RawCodedPAAxiomWitnessContext M
      (raw_zero M) (raw_zero M)).
  {
    pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
    cbn [rawQuotedPAAxiomWitnessList rawListCode map] in h.
    exact h.
  }
  destruct
    (raw_codedPALocalProof_andIntroductionOpenedCoverageLaw_on_witnessed_base
      M hPA inputs (raw_zero M) (raw_zero M) hempty)
    as (witnesses & root & hwitnessed & hroot).
  exists witnesses. split.
  - rewrite rawTemplateContextCode_as_on_tail.
    rewrite (raw_templateContextCodeOnTail_embedPAAxiomWitnesses M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      witnesses (raw_zero M)).
    exact hwitnessed.
  - apply raw_andIntroductionChildCoreRoots_of_openedCoverageCompiler.
    exists root.
    rewrite (raw_andIntroductionCoverageEigenContext_witnessed_code M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      witnesses).
    exact hroot.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildTailSelection.
