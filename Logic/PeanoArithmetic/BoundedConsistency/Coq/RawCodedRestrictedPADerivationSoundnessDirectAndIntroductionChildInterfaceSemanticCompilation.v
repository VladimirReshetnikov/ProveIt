(**
  Semantic recursive-child descent for the literal conjunction-introduction row.

  This is one acyclic strict-check boundary of the And-I child compiler.
  Later stages import this module opaquely so Rocq need not recheck its proof
  terms while validating the next represented-proof construction.
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
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.

Import ListNotations.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildInterfaceSemanticCompilation.

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
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.

(** ------------------------------------------------------------------
    Instantiate the published constructor-generic interface at the literal
    And-I recursive row. *)

Lemma raw_andIntroduction_recursive_child_data : forall
    (M : RawPAModel) root context leftFormula rightFormula
      leftChild rightChild child,
  root = rawProofAndIRoot M
    context leftFormula rightFormula leftChild rightChild ->
  In child [leftChild; rightChild] ->
  RawProofConstructorCode M
      root context leftFormula rightFormula
      (raw_zero M) (raw_zero M) leftChild rightChild (raw_zero M) /\
  In
    ([rawNumeralValue M 5; context; leftFormula; rightFormula;
        leftChild; rightChild],
      [leftChild; rightChild])
    (rawProofRecursiveCases M
      context leftFormula rightFormula
      (raw_zero M) (raw_zero M) leftChild rightChild (raw_zero M)) /\
  root = rawListCode M
    [rawNumeralValue M 5; context; leftFormula; rightFormula;
      leftChild; rightChild] /\
  In child [leftChild; rightChild].
Proof.
  intros M root context leftFormula rightFormula leftChild rightChild child
    hcode hchild.
  repeat split.
  - rewrite hcode. unfold RawProofConstructorCode, rawProofAndIRoot.
    do 5 right. left. reflexivity.
  - unfold rawProofRecursiveCases. cbn. tauto.
  - exact hcode.
  - exact hchild.
Qed.

Theorem raw_carrierRestrictedProofAt_andIntroduction_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level root context leftFormula rightFormula
      leftChild rightChild child,
  RawCarrierRestrictedProofAt M tail level root ->
  root = rawProofAndIRoot M
    context leftFormula rightFormula leftChild rightChild ->
  In child [leftChild; rightChild] ->
  RawCarrierRestrictedProofAt M tail level child.
Proof.
  intros M hPA tail level root context leftFormula rightFormula
    leftChild rightChild child hrestricted hcode hchild.
  destruct (raw_andIntroduction_recursive_child_data M root context
    leftFormula rightFormula leftChild rightChild child hcode hchild)
    as [hconstructor [hentry [hfields hin]]].
  exact (raw_carrierRestrictedProofAt_recursive_constructor_child
    M hPA tail level root context leftFormula rightFormula
    (raw_zero M) (raw_zero M) leftChild rightChild (raw_zero M)
    [rawNumeralValue M 5; context; leftFormula; rightFormula;
      leftChild; rightChild]
    [leftChild; rightChild] child hrestricted hconstructor hentry
    hfields hin).
Qed.

(** All proof-wide certificates and endpoint-local admissibility descend for
    either member of the two-child row.  The conjunction order is exactly the
    represented [ChildInterfaceResultTemplate] order. *)
Theorem raw_andIntroduction_child_interface : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level root coverageBound context leftFormula rightFormula
      leftChild rightChild child childConclusion
      assignmentCode assignmentStep,
  RawCarrierRestrictedProofAt M tail level root ->
  RawProofAtomicallyAdequate M root ->
  RawProofFormulaCoverage M root coverageBound ->
  RawProofRuleCoverage M root ->
  root = rawProofAndIRoot M
    context leftFormula rightFormula leftChild rightChild ->
  In child [leftChild; rightChild] ->
  RawProofEndpoint M child context childConclusion ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep coverageBound ->
  rawLt M child root /\
  RawCarrierRestrictedProofAt M tail level child /\
  RawProofAtomicallyAdequate M child /\
  RawProofFormulaCoverage M child coverageBound /\
  RawProofRuleCoverage M child /\
  RawProofRuleValid M child context childConclusion /\
  RawCodedFormulaAtomicallyAdequate M childConclusion /\
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep childConclusion /\
  RawCarrierFormulaQuantifierBounded M level childConclusion.
Proof.
  intros M hPA tail level root coverageBound context leftFormula
    rightFormula leftChild rightChild child childConclusion
    assignmentCode assignmentStep
    hrestricted hatomic hformulaCoverage hruleCoverage hcode hchild
    hendpoint hassignmentCoverage.
  destruct (raw_andIntroduction_recursive_child_data M root context
    leftFormula rightFormula leftChild rightChild child hcode hchild)
    as [hconstructor [hentry [hfields hin]]].
  exact (raw_recursive_constructor_child_interface
    M hPA tail level root coverageBound context
    leftFormula rightFormula (raw_zero M) (raw_zero M)
    leftChild rightChild (raw_zero M)
    [rawNumeralValue M 5; context; leftFormula; rightFormula;
      leftChild; rightChild]
    [leftChild; rightChild] child childConclusion
    assignmentCode assignmentStep
    hrestricted hatomic hformulaCoverage hruleCoverage
    hconstructor hentry hfields hin hendpoint hassignmentCoverage).
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildInterfaceSemanticCompilation.
