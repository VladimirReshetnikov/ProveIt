(**
  Direct rule-case integration after conjunction introduction.

  The And-I semantic slot contains three represented roots: structural
  interfaces for its left and right recursive children, followed by the
  dynamic conjunction truth law.  This module does not assume that bundle.
  Instead it selects the exact post-application outputs of those operations:

  - the left child interface result,
  - the right child interface result, and
  - truth of the displayed conjunction.

  Each output is an actual local-proof root in the literal And-I ready
  context.  Checked finite K-chains reintroduce exactly the antecedents of
  the corresponding public law.  The three promoted laws reconstruct the
  bundled target, which can consequently be removed from the successor
  continuation.  Selection and transport use one synchronized certified
  standard-PA witness tail.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateNumeralParameters
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpElimination
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterBottomElimination
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterExcludedMiddle
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpElimination.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterBottomElimination.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterExcludedMiddle.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.

(** ------------------------------------------------------------------
    Generic promotion of one post-application child-interface result. *)

Definition coqRestrictedPADirectAndIntroductionChildAfterEndpointCoreTemplate
    child context conclusion : TemplateFormula :=
  tfImp coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
    (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
      child context conclusion).

Definition coqRestrictedPADirectAndIntroductionChildAfterFormulaCoreTemplate
    child context conclusion displayedEndpoint : TemplateFormula :=
  tfImp displayedEndpoint
    (coqRestrictedPADirectAndIntroductionChildAfterEndpointCoreTemplate
      child context conclusion).

Definition coqRestrictedPADirectAndIntroductionChildAfterCodeCoreTemplate
    child context conclusion displayedEndpoint : TemplateFormula :=
  tfImp coqRestrictedPADirectAndIntroductionFormulaAndTemplate
    (coqRestrictedPADirectAndIntroductionChildAfterFormulaCoreTemplate
      child context conclusion displayedEndpoint).

Definition
    coqRestrictedPADirectAndIntroductionChildAfterRestrictedCoreTemplate
    child context conclusion displayedEndpoint : TemplateFormula :=
  tfImp coqRestrictedPADirectAndIntroductionCodeEqualityTemplate
    (coqRestrictedPADirectAndIntroductionChildAfterCodeCoreTemplate
      child context conclusion displayedEndpoint).

Definition coqRestrictedPADirectAndIntroductionChildCorePromotionContext0
    ambient child context conclusion :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
      child context conclusion :: ambient.

Definition coqRestrictedPADirectAndIntroductionChildCorePromotionContext1
    ambient child context conclusion :=
  coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate ::
    coqRestrictedPADirectAndIntroductionChildCorePromotionContext0
      ambient child context conclusion.

Definition coqRestrictedPADirectAndIntroductionChildCorePromotionContext2
    ambient child context conclusion :=
  coqRestrictedPADirectAndIntroductionCodeEqualityTemplate ::
    coqRestrictedPADirectAndIntroductionChildCorePromotionContext1
      ambient child context conclusion.

Definition coqRestrictedPADirectAndIntroductionChildCorePromotionContext3
    ambient child context conclusion :=
  coqRestrictedPADirectAndIntroductionFormulaAndTemplate ::
    coqRestrictedPADirectAndIntroductionChildCorePromotionContext2
      ambient child context conclusion.

Definition coqRestrictedPADirectAndIntroductionChildCorePromotionContext4
    ambient child context conclusion displayedEndpoint :=
  displayedEndpoint ::
    coqRestrictedPADirectAndIntroductionChildCorePromotionContext3
      ambient child context conclusion.

Definition coqRestrictedPADirectAndIntroductionChildCorePromotionContext5
    ambient child context conclusion displayedEndpoint :=
  coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate ::
    coqRestrictedPADirectAndIntroductionChildCorePromotionContext4
      ambient child context conclusion displayedEndpoint.

Definition coqRestrictedPADirectAndIntroductionChildCoreAssumptionRoot
    ambient child context conclusion displayedEndpoint : TemplateRawProof :=
  trpAss
    (coqRestrictedPADirectAndIntroductionChildCorePromotionContext5
      ambient child context conclusion displayedEndpoint)
    (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
      child context conclusion).

Definition coqRestrictedPADirectAndIntroductionChildCoreAfterAdmissibleRoot
    ambient child context conclusion displayedEndpoint : TemplateRawProof :=
  trpImpI
    (coqRestrictedPADirectAndIntroductionChildCorePromotionContext4
      ambient child context conclusion displayedEndpoint)
    coqRestrictedPADirectAndIntroductionDeepAdmissibleTemplate
    (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
      child context conclusion)
    (coqRestrictedPADirectAndIntroductionChildCoreAssumptionRoot
      ambient child context conclusion displayedEndpoint).

Definition coqRestrictedPADirectAndIntroductionChildCoreAfterEndpointRoot
    ambient child context conclusion displayedEndpoint : TemplateRawProof :=
  trpImpI
    (coqRestrictedPADirectAndIntroductionChildCorePromotionContext3
      ambient child context conclusion)
    displayedEndpoint
    (coqRestrictedPADirectAndIntroductionChildAfterEndpointCoreTemplate
      child context conclusion)
    (coqRestrictedPADirectAndIntroductionChildCoreAfterAdmissibleRoot
      ambient child context conclusion displayedEndpoint).

Definition coqRestrictedPADirectAndIntroductionChildCoreAfterFormulaRoot
    ambient child context conclusion displayedEndpoint : TemplateRawProof :=
  trpImpI
    (coqRestrictedPADirectAndIntroductionChildCorePromotionContext2
      ambient child context conclusion)
    coqRestrictedPADirectAndIntroductionFormulaAndTemplate
    (coqRestrictedPADirectAndIntroductionChildAfterFormulaCoreTemplate
      child context conclusion displayedEndpoint)
    (coqRestrictedPADirectAndIntroductionChildCoreAfterEndpointRoot
      ambient child context conclusion displayedEndpoint).

Definition coqRestrictedPADirectAndIntroductionChildCoreAfterCodeRoot
    ambient child context conclusion displayedEndpoint : TemplateRawProof :=
  trpImpI
    (coqRestrictedPADirectAndIntroductionChildCorePromotionContext1
      ambient child context conclusion)
    coqRestrictedPADirectAndIntroductionCodeEqualityTemplate
    (coqRestrictedPADirectAndIntroductionChildAfterCodeCoreTemplate
      child context conclusion displayedEndpoint)
    (coqRestrictedPADirectAndIntroductionChildCoreAfterFormulaRoot
      ambient child context conclusion displayedEndpoint).

Definition coqRestrictedPADirectAndIntroductionChildCoreTargetRoot
    ambient child context conclusion displayedEndpoint : TemplateRawProof :=
  trpImpI
    (coqRestrictedPADirectAndIntroductionChildCorePromotionContext0
      ambient child context conclusion)
    coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate
    (coqRestrictedPADirectAndIntroductionChildAfterRestrictedCoreTemplate
      child context conclusion displayedEndpoint)
    (coqRestrictedPADirectAndIntroductionChildCoreAfterCodeRoot
      ambient child context conclusion displayedEndpoint).

Definition coqRestrictedPADirectAndIntroductionChildCorePromotionRoot
    ambient child context conclusion displayedEndpoint : TemplateRawProof :=
  trpImpI ambient
    (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
      child context conclusion)
    (coqRestrictedPADirectAndIntroductionChildInterfaceLawTemplate
      child context conclusion displayedEndpoint)
    (coqRestrictedPADirectAndIntroductionChildCoreTargetRoot
      ambient child context conclusion displayedEndpoint).

Lemma coqRestrictedPADirectAndIntroductionChildCoreAssumptionRoot_valid :
    forall ambient child context conclusion displayedEndpoint,
  TemplateRawDerives
    (coqRestrictedPADirectAndIntroductionChildCorePromotionContext5
      ambient child context conclusion displayedEndpoint)
    (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
      child context conclusion)
    (coqRestrictedPADirectAndIntroductionChildCoreAssumptionRoot
      ambient child context conclusion displayedEndpoint).
Proof.
  intros. apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectAndIntroductionChildCorePromotionContext5,
    coqRestrictedPADirectAndIntroductionChildCorePromotionContext4,
    coqRestrictedPADirectAndIntroductionChildCorePromotionContext3,
    coqRestrictedPADirectAndIntroductionChildCorePromotionContext2,
    coqRestrictedPADirectAndIntroductionChildCorePromotionContext1,
    coqRestrictedPADirectAndIntroductionChildCorePromotionContext0.
  do 5 right. left. reflexivity.
Qed.

Lemma
    coqRestrictedPADirectAndIntroductionChildCoreAfterAdmissibleRoot_valid :
    forall ambient child context conclusion displayedEndpoint,
  TemplateRawDerives
    (coqRestrictedPADirectAndIntroductionChildCorePromotionContext4
      ambient child context conclusion displayedEndpoint)
    (coqRestrictedPADirectAndIntroductionChildAfterEndpointCoreTemplate
      child context conclusion)
    (coqRestrictedPADirectAndIntroductionChildCoreAfterAdmissibleRoot
      ambient child context conclusion displayedEndpoint).
Proof.
  intros. unfold
    coqRestrictedPADirectAndIntroductionChildCoreAfterAdmissibleRoot,
    coqRestrictedPADirectAndIntroductionChildAfterEndpointCoreTemplate.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  apply coqRestrictedPADirectAndIntroductionChildCoreAssumptionRoot_valid.
Qed.

Lemma coqRestrictedPADirectAndIntroductionChildCoreAfterEndpointRoot_valid :
    forall ambient child context conclusion displayedEndpoint,
  TemplateRawDerives
    (coqRestrictedPADirectAndIntroductionChildCorePromotionContext3
      ambient child context conclusion)
    (coqRestrictedPADirectAndIntroductionChildAfterFormulaCoreTemplate
      child context conclusion displayedEndpoint)
    (coqRestrictedPADirectAndIntroductionChildCoreAfterEndpointRoot
      ambient child context conclusion displayedEndpoint).
Proof.
  intros. unfold
    coqRestrictedPADirectAndIntroductionChildCoreAfterEndpointRoot,
    coqRestrictedPADirectAndIntroductionChildAfterFormulaCoreTemplate.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  apply
    coqRestrictedPADirectAndIntroductionChildCoreAfterAdmissibleRoot_valid.
Qed.

Lemma coqRestrictedPADirectAndIntroductionChildCoreAfterFormulaRoot_valid :
    forall ambient child context conclusion displayedEndpoint,
  TemplateRawDerives
    (coqRestrictedPADirectAndIntroductionChildCorePromotionContext2
      ambient child context conclusion)
    (coqRestrictedPADirectAndIntroductionChildAfterCodeCoreTemplate
      child context conclusion displayedEndpoint)
    (coqRestrictedPADirectAndIntroductionChildCoreAfterFormulaRoot
      ambient child context conclusion displayedEndpoint).
Proof.
  intros. unfold
    coqRestrictedPADirectAndIntroductionChildCoreAfterFormulaRoot,
    coqRestrictedPADirectAndIntroductionChildAfterCodeCoreTemplate.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  apply coqRestrictedPADirectAndIntroductionChildCoreAfterEndpointRoot_valid.
Qed.

Lemma coqRestrictedPADirectAndIntroductionChildCoreAfterCodeRoot_valid :
    forall ambient child context conclusion displayedEndpoint,
  TemplateRawDerives
    (coqRestrictedPADirectAndIntroductionChildCorePromotionContext1
      ambient child context conclusion)
    (coqRestrictedPADirectAndIntroductionChildAfterRestrictedCoreTemplate
      child context conclusion displayedEndpoint)
    (coqRestrictedPADirectAndIntroductionChildCoreAfterCodeRoot
      ambient child context conclusion displayedEndpoint).
Proof.
  intros. unfold
    coqRestrictedPADirectAndIntroductionChildCoreAfterCodeRoot,
    coqRestrictedPADirectAndIntroductionChildAfterRestrictedCoreTemplate.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  apply coqRestrictedPADirectAndIntroductionChildCoreAfterFormulaRoot_valid.
Qed.

Lemma coqRestrictedPADirectAndIntroductionChildCoreTargetRoot_valid :
    forall ambient child context conclusion displayedEndpoint,
  TemplateRawDerives
    (coqRestrictedPADirectAndIntroductionChildCorePromotionContext0
      ambient child context conclusion)
    (coqRestrictedPADirectAndIntroductionChildInterfaceLawTemplate
      child context conclusion displayedEndpoint)
    (coqRestrictedPADirectAndIntroductionChildCoreTargetRoot
      ambient child context conclusion displayedEndpoint).
Proof.
  intros. unfold
    coqRestrictedPADirectAndIntroductionChildCoreTargetRoot,
    coqRestrictedPADirectAndIntroductionChildInterfaceLawTemplate.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  apply coqRestrictedPADirectAndIntroductionChildCoreAfterCodeRoot_valid.
Qed.

Lemma coqRestrictedPADirectAndIntroductionChildCorePromotionRoot_valid :
    forall ambient child context conclusion displayedEndpoint,
  TemplateRawDerives ambient
    (tfImp
      (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
        child context conclusion)
      (coqRestrictedPADirectAndIntroductionChildInterfaceLawTemplate
        child context conclusion displayedEndpoint))
    (coqRestrictedPADirectAndIntroductionChildCorePromotionRoot
      ambient child context conclusion displayedEndpoint).
Proof.
  intros. unfold
    coqRestrictedPADirectAndIntroductionChildCorePromotionRoot.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  apply coqRestrictedPADirectAndIntroductionChildCoreTargetRoot_valid.
Qed.

Theorem raw_andIntroductionChildInterfaceLawRoot_of_coreRoot : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (translation : RawCodedTemplateTranslation M)
      ambient child context conclusion displayedEndpoint coreRoot,
  RawCodedPALocalProofOf M (rawTemplateContextCode translation ambient)
    (rawTemplateFormula translation
      (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
        child context conclusion)) coreRoot ->
  exists lawRoot,
    RawCodedPALocalProofOf M (rawTemplateContextCode translation ambient)
      (rawTemplateFormula translation
        (coqRestrictedPADirectAndIntroductionChildInterfaceLawTemplate
          child context conclusion displayedEndpoint)) lawRoot.
Proof.
  intros M hPA translation ambient child context conclusion
    displayedEndpoint coreRoot hcore.
  pose proof
    (raw_templateProof_localProof M hPA translation
      (coqRestrictedPADirectAndIntroductionChildCorePromotionRoot
        ambient child context conclusion displayedEndpoint)
      (proj1
        (coqRestrictedPADirectAndIntroductionChildCorePromotionRoot_valid
          ambient child context conclusion displayedEndpoint)))
    as hpromotion.
  eexists.
  exact
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation ambient _ _ _ coreRoot hpromotion hcore).
Qed.

(** ------------------------------------------------------------------
    Promotion of the post-application conjunction truth output. *)

Definition coqRestrictedPADirectAndIntroductionTruthAfterLeftCoreTemplate :=
  tfImp coqRestrictedPADirectAndIntroductionRightTruthTemplate
    coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate.

Definition coqRestrictedPADirectAndIntroductionTruthAfterFormulaCoreTemplate :=
  tfImp coqRestrictedPADirectAndIntroductionLeftTruthTemplate
    coqRestrictedPADirectAndIntroductionTruthAfterLeftCoreTemplate.

Definition coqRestrictedPADirectAndIntroductionTruthCorePromotionContext0
    ambient :=
  coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate :: ambient.

Definition coqRestrictedPADirectAndIntroductionTruthCorePromotionContext1
    ambient :=
  coqRestrictedPADirectAndIntroductionFormulaAndTemplate ::
    coqRestrictedPADirectAndIntroductionTruthCorePromotionContext0 ambient.

Definition coqRestrictedPADirectAndIntroductionTruthCorePromotionContext2
    ambient :=
  coqRestrictedPADirectAndIntroductionLeftTruthTemplate ::
    coqRestrictedPADirectAndIntroductionTruthCorePromotionContext1 ambient.

Definition coqRestrictedPADirectAndIntroductionTruthCorePromotionContext3
    ambient :=
  coqRestrictedPADirectAndIntroductionRightTruthTemplate ::
    coqRestrictedPADirectAndIntroductionTruthCorePromotionContext2 ambient.

Definition coqRestrictedPADirectAndIntroductionTruthCoreAssumptionRoot ambient
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectAndIntroductionTruthCorePromotionContext3
    ambient) coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate.

Definition coqRestrictedPADirectAndIntroductionTruthCoreAfterRightRoot ambient
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectAndIntroductionTruthCorePromotionContext2
    ambient) coqRestrictedPADirectAndIntroductionRightTruthTemplate
    coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate
    (coqRestrictedPADirectAndIntroductionTruthCoreAssumptionRoot ambient).

Definition coqRestrictedPADirectAndIntroductionTruthCoreAfterLeftRoot ambient
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectAndIntroductionTruthCorePromotionContext1
    ambient) coqRestrictedPADirectAndIntroductionLeftTruthTemplate
    coqRestrictedPADirectAndIntroductionTruthAfterLeftCoreTemplate
    (coqRestrictedPADirectAndIntroductionTruthCoreAfterRightRoot ambient).

Definition coqRestrictedPADirectAndIntroductionTruthCoreTargetRoot ambient
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectAndIntroductionTruthCorePromotionContext0
    ambient) coqRestrictedPADirectAndIntroductionFormulaAndTemplate
    coqRestrictedPADirectAndIntroductionTruthAfterFormulaCoreTemplate
    (coqRestrictedPADirectAndIntroductionTruthCoreAfterLeftRoot ambient).

Definition coqRestrictedPADirectAndIntroductionTruthCorePromotionRoot ambient
    : TemplateRawProof :=
  trpImpI ambient
    coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate
    coqRestrictedPADirectAndIntroductionTruthLawTemplate
    (coqRestrictedPADirectAndIntroductionTruthCoreTargetRoot ambient).

Lemma coqRestrictedPADirectAndIntroductionTruthCoreAssumptionRoot_valid :
    forall ambient,
  TemplateRawDerives
    (coqRestrictedPADirectAndIntroductionTruthCorePromotionContext3 ambient)
    coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate
    (coqRestrictedPADirectAndIntroductionTruthCoreAssumptionRoot ambient).
Proof.
  intro. apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectAndIntroductionTruthCorePromotionContext3,
    coqRestrictedPADirectAndIntroductionTruthCorePromotionContext2,
    coqRestrictedPADirectAndIntroductionTruthCorePromotionContext1,
    coqRestrictedPADirectAndIntroductionTruthCorePromotionContext0.
  do 3 right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectAndIntroductionTruthCoreAfterRightRoot_valid :
    forall ambient,
  TemplateRawDerives
    (coqRestrictedPADirectAndIntroductionTruthCorePromotionContext2 ambient)
    coqRestrictedPADirectAndIntroductionTruthAfterLeftCoreTemplate
    (coqRestrictedPADirectAndIntroductionTruthCoreAfterRightRoot ambient).
Proof.
  intro. unfold
    coqRestrictedPADirectAndIntroductionTruthCoreAfterRightRoot,
    coqRestrictedPADirectAndIntroductionTruthAfterLeftCoreTemplate.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  apply coqRestrictedPADirectAndIntroductionTruthCoreAssumptionRoot_valid.
Qed.

Lemma coqRestrictedPADirectAndIntroductionTruthCoreAfterLeftRoot_valid :
    forall ambient,
  TemplateRawDerives
    (coqRestrictedPADirectAndIntroductionTruthCorePromotionContext1 ambient)
    coqRestrictedPADirectAndIntroductionTruthAfterFormulaCoreTemplate
    (coqRestrictedPADirectAndIntroductionTruthCoreAfterLeftRoot ambient).
Proof.
  intro. unfold
    coqRestrictedPADirectAndIntroductionTruthCoreAfterLeftRoot,
    coqRestrictedPADirectAndIntroductionTruthAfterFormulaCoreTemplate.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  apply coqRestrictedPADirectAndIntroductionTruthCoreAfterRightRoot_valid.
Qed.

Lemma coqRestrictedPADirectAndIntroductionTruthCoreTargetRoot_valid :
    forall ambient,
  TemplateRawDerives
    (coqRestrictedPADirectAndIntroductionTruthCorePromotionContext0 ambient)
    coqRestrictedPADirectAndIntroductionTruthLawTemplate
    (coqRestrictedPADirectAndIntroductionTruthCoreTargetRoot ambient).
Proof.
  intro. unfold coqRestrictedPADirectAndIntroductionTruthCoreTargetRoot,
    coqRestrictedPADirectAndIntroductionTruthLawTemplate.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  apply coqRestrictedPADirectAndIntroductionTruthCoreAfterLeftRoot_valid.
Qed.

Lemma coqRestrictedPADirectAndIntroductionTruthCorePromotionRoot_valid :
    forall ambient,
  TemplateRawDerives ambient
    (tfImp coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate
      coqRestrictedPADirectAndIntroductionTruthLawTemplate)
    (coqRestrictedPADirectAndIntroductionTruthCorePromotionRoot ambient).
Proof.
  intro. unfold coqRestrictedPADirectAndIntroductionTruthCorePromotionRoot.
  apply coqRestrictedPADirect_templateRawDerives_impI.
  apply coqRestrictedPADirectAndIntroductionTruthCoreTargetRoot_valid.
Qed.

Theorem raw_andIntroductionTruthLawRoot_of_coreRoot : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (translation : RawCodedTemplateTranslation M) ambient coreRoot,
  RawCodedPALocalProofOf M (rawTemplateContextCode translation ambient)
    (rawTemplateFormula translation
      coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate)
    coreRoot ->
  exists lawRoot,
    RawCodedPALocalProofOf M (rawTemplateContextCode translation ambient)
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionTruthLawTemplate) lawRoot.
Proof.
  intros M hPA translation ambient coreRoot hcore.
  pose proof
    (raw_templateProof_localProof M hPA translation
      (coqRestrictedPADirectAndIntroductionTruthCorePromotionRoot ambient)
      (proj1
        (coqRestrictedPADirectAndIntroductionTruthCorePromotionRoot_valid
          ambient))) as hpromotion.
  eexists.
  exact
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation ambient _ _ _ coreRoot hpromotion hcore).
Qed.

(** ------------------------------------------------------------------
    Three-root boundary and reconstruction of the public bundle. *)

Definition RawCoqRestrictedPADirectAndIntroductionSemanticCoreRootsAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (ambient : TemplateContext) : Prop :=
  (exists leftRoot,
    RawCodedPALocalProofOf M (rawTemplateContextCode translation ambient)
      (rawTemplateFormula translation
        (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
          coqRestrictedPADirectAndIntroductionLeftChildTerm
          coqRestrictedPADirectAndIntroductionWitnessContextTerm
          coqRestrictedPADirectAndIntroductionLeftFormulaTerm)) leftRoot) /\
  (exists rightRoot,
    RawCodedPALocalProofOf M (rawTemplateContextCode translation ambient)
      (rawTemplateFormula translation
        (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
          coqRestrictedPADirectAndIntroductionRightChildTerm
          coqRestrictedPADirectAndIntroductionWitnessContextTerm
          coqRestrictedPADirectAndIntroductionRightFormulaTerm)) rightRoot) /\
  (exists truthRoot,
    RawCodedPALocalProofOf M (rawTemplateContextCode translation ambient)
      (rawTemplateFormula translation
        coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate)
      truthRoot).

Arguments RawCoqRestrictedPADirectAndIntroductionSemanticCoreRootsAt
  M translation ambient : clear implicits.

Definition RawCoqRestrictedPADirectAndIntroductionSemanticCoreRoots
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  RawCoqRestrictedPADirectAndIntroductionSemanticCoreRootsAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail).

Arguments RawCoqRestrictedPADirectAndIntroductionSemanticCoreRoots
  M hPA inputs tail : clear implicits.

Theorem raw_andIntroductionSemanticRoots_of_coreRoots : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectAndIntroductionSemanticCoreRoots
    M hPA inputs tail ->
  RawCoqRestrictedPADirectStrongStepAndIntroductionSemanticRoots
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail
    [(leftRoot & hleft) [(rightRoot & hright) (truthRoot & htruth)]].
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  set (ready :=
    coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail).
  destruct
    (raw_andIntroductionChildInterfaceLawRoot_of_coreRoot
      M hPA translation ready
      coqRestrictedPADirectAndIntroductionLeftChildTerm
      coqRestrictedPADirectAndIntroductionWitnessContextTerm
      coqRestrictedPADirectAndIntroductionLeftFormulaTerm
      coqRestrictedPADirectAndIntroductionLeftEndpointTemplate
      leftRoot hleft) as [leftLawRoot hleftLaw].
  destruct
    (raw_andIntroductionChildInterfaceLawRoot_of_coreRoot
      M hPA translation ready
      coqRestrictedPADirectAndIntroductionRightChildTerm
      coqRestrictedPADirectAndIntroductionWitnessContextTerm
      coqRestrictedPADirectAndIntroductionRightFormulaTerm
      coqRestrictedPADirectAndIntroductionRightEndpointTemplate
      rightRoot hright) as [rightLawRoot hrightLaw].
  destruct (raw_andIntroductionTruthLawRoot_of_coreRoot
    M hPA translation ready truthRoot htruth)
    as [truthLawRoot htruthLaw].
  unfold RawCoqRestrictedPADirectStrongStepAndIntroductionSemanticRoots.
  cbn zeta. split.
  - split.
    + exists leftLawRoot. exact hleftLaw.
    + exists rightLawRoot. exact hrightLaw.
  - exists truthLawRoot. exact htruthLaw.
Qed.

(** ------------------------------------------------------------------
    Exact fourteen-field continuation after deleting And-I. *)

Record RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroduction
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectAfterAndI_andEliminationLeftRecursive :
    RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndI_andEliminationLeftTruth :
    RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndI_andEliminationRightRecursive :
    RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndI_andEliminationRightTruth :
    RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndI_orIntroductionRightRecursive :
    RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndI_orIntroductionRightTruth :
    RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndI_orElimination :
    RawCoqRestrictedPADirectOrEliminationSemanticRoots M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndI_universalIntroduction :
    RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndI_universalEliminationRecursive :
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndI_universalEliminationTruth :
    RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndI_existentialIntroduction :
    RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndI_existentialElimination :
    RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndI_equalityReflexivity :
    RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterAndI_equalityElimination :
    RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
      M hPA inputs tail
}.

Arguments RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroduction
  M hPA inputs tail : clear implicits.

Theorem raw_afterExcludedMiddle_of_afterAndIntroduction : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectStrongStepAndIntroductionSemanticRoots
    M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroduction
    M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterExcludedMiddle
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail handI hremaining.
  destruct hremaining. constructor; assumption.
Qed.

(** ------------------------------------------------------------------
    Certified selection and common-tail transport of all three cores. *)

Definition RawCoqRestrictedPADirectSelectedAndIntroductionCoreTail
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectAndIntroductionSemanticCoreRoots
      M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Arguments RawCoqRestrictedPADirectSelectedAndIntroductionCoreTail
  M hPA inputs : clear implicits.

Lemma coqRestrictedPADirectAndIntroductionReadyContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectStrongStepAndIntroductionReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepAndIntroductionReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  pose proof
    (coqRestrictedPADirectExcludedMiddleCaseContext_app_witnesses witnesses)
    as hexcluded.
  unfold coqRestrictedPADirectExcludedMiddleCaseContext in hexcluded.
  cbn [List.app] in hexcluded.
  pose proof (f_equal (skipn 1) hexcluded) as hdeep.
  cbn [skipn] in hdeep.
  unfold coqRestrictedPADirectExcludedMiddleDeepContext in hdeep.
  unfold coqRestrictedPADirectStrongStepAndIntroductionReadyContext,
    coqRestrictedPADirectStrongStepAndIntroductionAdmissibleContext,
    coqRestrictedPADirectStrongStepAndIntroductionCaseContext,
    coqRestrictedPADirectStrongStepAndIntroductionBaseContext.
  repeat rewrite <- raw_coqRestrictedPADirectEndpointDeepContext_shape.
  cbn [List.app]. now rewrite hdeep.
Qed.

Theorem raw_andIntroductionReadyRoot_surround_witnessed_tail : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      prefix witnesses suffix formula root,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqRestrictedPADirectStrongStepAndIntroductionReadyContext
        (embedPAContext (map witnessedAxiom witnesses))))
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs) formula) root ->
  exists transportedRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepAndIntroductionReadyContext
          (embedPAContext
            (map witnessedAxiom (prefix ++ (witnesses ++ suffix))))))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs) formula)
      transportedRoot.
Proof.
  intros M hPA inputs prefix witnesses suffix formula root hroot.
  rewrite coqRestrictedPADirectAndIntroductionReadyContext_app_witnesses
    in hroot.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (coqRestrictedPADirectStrongStepAndIntroductionReadyContext [])
      prefix witnesses suffix
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs) formula)
      root hroot) as [transportedRoot htransported].
  exists transportedRoot.
  rewrite coqRestrictedPADirectAndIntroductionReadyContext_app_witnesses.
  exact htransported.
Qed.

Theorem raw_andIntroductionSemanticCoreRoots_surround_witnessed_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    prefix witnesses suffix,
  RawCoqRestrictedPADirectAndIntroductionSemanticCoreRoots M hPA inputs
    (embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqRestrictedPADirectAndIntroductionSemanticCoreRoots M hPA inputs
    (embedPAContext
      (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))).
Proof.
  intros M hPA inputs prefix witnesses suffix
    [(leftRoot & hleft) [(rightRoot & hright) (truthRoot & htruth)]].
  destruct (raw_andIntroductionReadyRoot_surround_witnessed_tail
    M hPA inputs prefix witnesses suffix
    (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
      coqRestrictedPADirectAndIntroductionLeftChildTerm
      coqRestrictedPADirectAndIntroductionWitnessContextTerm
      coqRestrictedPADirectAndIntroductionLeftFormulaTerm)
    leftRoot hleft) as [leftTransported hleftTransported].
  destruct (raw_andIntroductionReadyRoot_surround_witnessed_tail
    M hPA inputs prefix witnesses suffix
    (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
      coqRestrictedPADirectAndIntroductionRightChildTerm
      coqRestrictedPADirectAndIntroductionWitnessContextTerm
      coqRestrictedPADirectAndIntroductionRightFormulaTerm)
    rightRoot hright) as [rightTransported hrightTransported].
  destruct (raw_andIntroductionReadyRoot_surround_witnessed_tail
    M hPA inputs prefix witnesses suffix
    coqRestrictedPADirectAndIntroductionOuterConclusionTruthTemplate
    truthRoot htruth) as [truthTransported htruthTransported].
  split; [eexists; exact hleftTransported |].
  split; [eexists; exact hrightTransported |].
  eexists; exact htruthTransported.
Qed.

Definition
    RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroduction
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Arguments
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem raw_remainingAfterExcludedMiddleCompiler_of_selectedAndICores :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedAndIntroductionCoreTail M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterExcludedMiddleStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs
    (coreWitnesses & _ & hcores) hremaining baseWitnesses.
  destruct (hremaining (baseWitnesses ++ coreWitnesses))
    as [suffix hremainingTail].
  exists (coreWitnesses ++ suffix).
  apply raw_afterExcludedMiddle_of_afterAndIntroduction.
  - apply raw_andIntroductionSemanticRoots_of_coreRoots.
    exact (raw_andIntroductionSemanticCoreRoots_surround_witnessed_tail
      M hPA inputs baseWitnesses coreWitnesses suffix hcores).
  - replace ((baseWitnesses ++ coreWitnesses) ++ suffix)
      with (baseWitnesses ++ (coreWitnesses ++ suffix))
      in hremainingTail by apply app_assoc.
    exact hremainingTail.
Qed.

(** Native endpoint with the bundled And-I target removed. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeInputs_afterAndIntroduction
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence,
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt M hPA parameters
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence ->
  (forall contextTruth conclusionTruth,
    let inputs :=
      rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth in
    RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail
      M hPA inputs /\
    (RawCoqRestrictedPADirectSelectedImpIntroductionRecursiveTail
      M hPA inputs /\
     (RawCoqRestrictedPADirectSelectedImpIntroductionFixedRowSplitTail
        M hPA inputs /\
      (RawCoqRestrictedPADirectSelectedImpECoreTail M hPA inputs /\
       (RawCoqRestrictedPADirectSelectedBottomContradictionCoreTail
          M hPA inputs /\
        (RawCoqRestrictedPADirectSelectedExcludedMiddleTruthCoreTail
           M hPA inputs /\
         (RawCoqRestrictedPADirectSelectedAndIntroductionCoreTail
            M hPA inputs /\
          RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
            M hPA inputs))))))) ->
  exists contextTruth conclusionTruth soundnessCertificate,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
        (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth))
      soundnessCertificate.
Proof.
  intros M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence hinputs hcontinuation.
  apply
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeInputs_afterExcludedMiddle
      M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
      nextSigmaEvidence hinputs).
  intros contextTruth conclusionTruth.
  destruct (hcontinuation contextTruth conclusionTruth)
    as [horTruth
      [hrecursive
        [hsplit
          [himpECore
            [hbottomCore
              [hexcludedCore [handICores hremaining]]]]]]].
  split; [exact horTruth |].
  split; [exact hrecursive |].
  split; [exact hsplit |].
  split; [exact himpECore |].
  split; [exact hbottomCore |].
  split; [exact hexcludedCore |].
  exact
    (raw_remainingAfterExcludedMiddleCompiler_of_selectedAndICores
      M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      handICores hremaining).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction.
