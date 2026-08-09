(**
  Direct rule-case integration after implication elimination.

  The public Imp-E residual includes seven structural antecedents before its
  semantic conclusion.  Those antecedents are already compiled by the
  constructor case, but the semantic conclusion itself still combines two
  recursive uses of the strong prefix with the represented fixed-level
  implication modus-ponens law.  No carrier-parametric compiler for that
  combination is currently available.

  This module therefore exposes the exact non-target boundary: an actual PA
  local-proof root for [coqRestrictedPADirectImpECoreTemplate] in the literal
  Imp-E case context.  A finite template derivation promotes that core root
  to the full recursive modus-ponens law; the target law is never assumed.
  The selected root lives on a certified finite standard-PA witness tail and
  the usual growing-tail transport places it between earlier and later
  batches.  The successor continuation consequently has no Imp-E field.
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
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectImpEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectBottomEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpElimination.

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
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionRecursive.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpIntroductionTruth.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.

(** ------------------------------------------------------------------
    Exact semantic-core boundary and its finite promotion. *)

Definition RawCoqRestrictedPADirectImpECoreLawRoot
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADirectImpECaseContext tail))
      (rawTemplateFormula translation coqRestrictedPADirectImpECoreTemplate)
      root.

Arguments RawCoqRestrictedPADirectImpECoreLawRoot
  M translation tail : clear implicits.

(** Contexts used only by the finite K-chain which retains a supplied core
    proof while discharging the seven public structural antecedents. *)
Definition coqRestrictedPADirectImpECorePromotionContext0 tail :=
  coqRestrictedPADirectImpECoreTemplate ::
    coqRestrictedPADirectImpECaseContext tail.

Definition coqRestrictedPADirectImpECorePromotionContext1 tail :=
  coqRestrictedPADirectImpEStrongPrefixTemplate ::
    coqRestrictedPADirectImpECorePromotionContext0 tail.

Definition coqRestrictedPADirectImpECorePromotionContext2 tail :=
  coqRestrictedPADirectImpERestrictedProofTemplate ::
    coqRestrictedPADirectImpECorePromotionContext1 tail.

Definition coqRestrictedPADirectImpECorePromotionContext3 tail :=
  coqRestrictedPADirectImpECodeEqualityTemplate ::
    coqRestrictedPADirectImpECorePromotionContext2 tail.

Definition coqRestrictedPADirectImpECorePromotionContext4 tail :=
  coqRestrictedPADirectImpEConclusionEqualityTemplate ::
    coqRestrictedPADirectImpECorePromotionContext3 tail.

Definition coqRestrictedPADirectImpECorePromotionContext5 tail :=
  coqRestrictedPADirectImpEFormulaCodeTemplate ::
    coqRestrictedPADirectImpECorePromotionContext4 tail.

Definition coqRestrictedPADirectImpECorePromotionContext6 tail :=
  coqRestrictedPADirectImpEFirstEndpointTemplate ::
    coqRestrictedPADirectImpECorePromotionContext5 tail.

Definition coqRestrictedPADirectImpECorePromotionContext7 tail :=
  coqRestrictedPADirectImpESecondEndpointTemplate ::
    coqRestrictedPADirectImpECorePromotionContext6 tail.

Definition coqRestrictedPADirectImpECorePromotionAssumptionRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectImpECorePromotionContext7 tail)
    coqRestrictedPADirectImpECoreTemplate.

Definition coqRestrictedPADirectImpECorePromotionAfterSecondRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectImpECorePromotionContext6 tail)
    coqRestrictedPADirectImpESecondEndpointTemplate
    coqRestrictedPADirectImpECoreTemplate
    (coqRestrictedPADirectImpECorePromotionAssumptionRoot tail).

Definition coqRestrictedPADirectImpECorePromotionAfterFirstRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectImpECorePromotionContext5 tail)
    coqRestrictedPADirectImpEFirstEndpointTemplate
    coqRestrictedPADirectImpEAfterFirstEndpointTemplate
    (coqRestrictedPADirectImpECorePromotionAfterSecondRoot tail).

Definition coqRestrictedPADirectImpECorePromotionAfterFormulaRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectImpECorePromotionContext4 tail)
    coqRestrictedPADirectImpEFormulaCodeTemplate
    coqRestrictedPADirectImpEAfterFormulaTemplate
    (coqRestrictedPADirectImpECorePromotionAfterFirstRoot tail).

Definition coqRestrictedPADirectImpECorePromotionAfterConclusionRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectImpECorePromotionContext3 tail)
    coqRestrictedPADirectImpEConclusionEqualityTemplate
    coqRestrictedPADirectImpEAfterConclusionTemplate
    (coqRestrictedPADirectImpECorePromotionAfterFormulaRoot tail).

Definition coqRestrictedPADirectImpECorePromotionAfterCodeRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectImpECorePromotionContext2 tail)
    coqRestrictedPADirectImpECodeEqualityTemplate
    coqRestrictedPADirectImpEAfterCodeTemplate
    (coqRestrictedPADirectImpECorePromotionAfterConclusionRoot tail).

Definition coqRestrictedPADirectImpECorePromotionAfterRestrictedRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectImpECorePromotionContext1 tail)
    coqRestrictedPADirectImpERestrictedProofTemplate
    coqRestrictedPADirectImpEAfterRestrictedTemplate
    (coqRestrictedPADirectImpECorePromotionAfterCodeRoot tail).

Definition coqRestrictedPADirectImpECorePromotionTargetRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectImpECorePromotionContext0 tail)
    coqRestrictedPADirectImpEStrongPrefixTemplate
    coqRestrictedPADirectImpEAfterStrongPrefixTemplate
    (coqRestrictedPADirectImpECorePromotionAfterRestrictedRoot tail).

Definition coqRestrictedPADirectImpECorePromotionRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectImpECaseContext tail)
    coqRestrictedPADirectImpECoreTemplate
    coqRestrictedPADirectImpERecursiveModusPonensLawTemplate
    (coqRestrictedPADirectImpECorePromotionTargetRoot tail).

Lemma coqRestrictedPADirectImpECorePromotionAssumptionRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectImpECorePromotionContext7 tail)
    coqRestrictedPADirectImpECoreTemplate
    (coqRestrictedPADirectImpECorePromotionAssumptionRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectImpECorePromotionContext7,
    coqRestrictedPADirectImpECorePromotionContext6,
    coqRestrictedPADirectImpECorePromotionContext5,
    coqRestrictedPADirectImpECorePromotionContext4,
    coqRestrictedPADirectImpECorePromotionContext3,
    coqRestrictedPADirectImpECorePromotionContext2,
    coqRestrictedPADirectImpECorePromotionContext1,
    coqRestrictedPADirectImpECorePromotionContext0.
  do 7 right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectImpECorePromotionAfterSecondRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectImpECorePromotionContext6 tail)
    coqRestrictedPADirectImpEAfterFirstEndpointTemplate
    (coqRestrictedPADirectImpECorePromotionAfterSecondRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectImpECorePromotionAfterSecondRoot,
    coqRestrictedPADirectImpEAfterFirstEndpointTemplate,
    coqRestrictedPADirectImpEAfterSecondEndpointTemplate.
  apply coqRestrictedPADirectImpE_templateRawDerives_impI.
  exact (coqRestrictedPADirectImpECorePromotionAssumptionRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpECorePromotionAfterFirstRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectImpECorePromotionContext5 tail)
    coqRestrictedPADirectImpEAfterFormulaTemplate
    (coqRestrictedPADirectImpECorePromotionAfterFirstRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectImpECorePromotionAfterFirstRoot,
    coqRestrictedPADirectImpEAfterFormulaTemplate.
  apply coqRestrictedPADirectImpE_templateRawDerives_impI.
  exact (coqRestrictedPADirectImpECorePromotionAfterSecondRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpECorePromotionAfterFormulaRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectImpECorePromotionContext4 tail)
    coqRestrictedPADirectImpEAfterConclusionTemplate
    (coqRestrictedPADirectImpECorePromotionAfterFormulaRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectImpECorePromotionAfterFormulaRoot,
    coqRestrictedPADirectImpEAfterConclusionTemplate.
  apply coqRestrictedPADirectImpE_templateRawDerives_impI.
  exact (coqRestrictedPADirectImpECorePromotionAfterFirstRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpECorePromotionAfterConclusionRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectImpECorePromotionContext3 tail)
    coqRestrictedPADirectImpEAfterCodeTemplate
    (coqRestrictedPADirectImpECorePromotionAfterConclusionRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectImpECorePromotionAfterConclusionRoot,
    coqRestrictedPADirectImpEAfterCodeTemplate.
  apply coqRestrictedPADirectImpE_templateRawDerives_impI.
  exact (coqRestrictedPADirectImpECorePromotionAfterFormulaRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpECorePromotionAfterCodeRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectImpECorePromotionContext2 tail)
    coqRestrictedPADirectImpEAfterRestrictedTemplate
    (coqRestrictedPADirectImpECorePromotionAfterCodeRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectImpECorePromotionAfterCodeRoot,
    coqRestrictedPADirectImpEAfterRestrictedTemplate.
  apply coqRestrictedPADirectImpE_templateRawDerives_impI.
  exact (coqRestrictedPADirectImpECorePromotionAfterConclusionRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpECorePromotionAfterRestrictedRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectImpECorePromotionContext1 tail)
    coqRestrictedPADirectImpEAfterStrongPrefixTemplate
    (coqRestrictedPADirectImpECorePromotionAfterRestrictedRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectImpECorePromotionAfterRestrictedRoot,
    coqRestrictedPADirectImpEAfterStrongPrefixTemplate.
  apply coqRestrictedPADirectImpE_templateRawDerives_impI.
  exact (coqRestrictedPADirectImpECorePromotionAfterCodeRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpECorePromotionTargetRoot_valid : forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectImpECorePromotionContext0 tail)
    coqRestrictedPADirectImpERecursiveModusPonensLawTemplate
    (coqRestrictedPADirectImpECorePromotionTargetRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectImpECorePromotionTargetRoot,
    coqRestrictedPADirectImpERecursiveModusPonensLawTemplate.
  apply coqRestrictedPADirectImpE_templateRawDerives_impI.
  exact (coqRestrictedPADirectImpECorePromotionAfterRestrictedRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectImpECorePromotionRoot_valid : forall tail,
  TemplateRawDerives (coqRestrictedPADirectImpECaseContext tail)
    (tfImp coqRestrictedPADirectImpECoreTemplate
      coqRestrictedPADirectImpERecursiveModusPonensLawTemplate)
    (coqRestrictedPADirectImpECorePromotionRoot tail).
Proof.
  intro tail. unfold coqRestrictedPADirectImpECorePromotionRoot.
  apply coqRestrictedPADirectImpE_templateRawDerives_impI.
  exact (coqRestrictedPADirectImpECorePromotionTargetRoot_valid tail).
Qed.

Theorem raw_impERecursiveModusPonensLawRoot_of_coreLawRoot : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectImpECoreLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs) tail ->
  RawCoqRestrictedPADirectImpERecursiveModusPonensLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs) tail.
Proof.
  intros M hPA inputs tail (coreRoot & hcore).
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  pose proof
    (raw_templateProof_localProof M hPA translation
      (coqRestrictedPADirectImpECorePromotionRoot tail)
      (proj1 (coqRestrictedPADirectImpECorePromotionRoot_valid tail)))
    as hpromotion.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation (coqRestrictedPADirectImpECaseContext tail)
      coqRestrictedPADirectImpECoreTemplate
      coqRestrictedPADirectImpERecursiveModusPonensLawTemplate
      (rawTemplateProofCode translation
        (coqRestrictedPADirectImpECorePromotionRoot tail))
      coreRoot hpromotion hcore) as htarget.
  eexists. exact htarget.
Qed.

(** ------------------------------------------------------------------
    The exact seventeen-field continuation after deleting Imp-E. *)

Record RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterImpElimination
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectAfterImpE_bottomElimination :
    RawCoqRestrictedPADirectBottomRecursiveContradictionLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterImpE_excludedMiddle :
    RawCoqRestrictedPADirectExcludedMiddleTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterImpE_andIntroduction :
    RawCoqRestrictedPADirectStrongStepAndIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpE_andEliminationLeftRecursive :
    RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpE_andEliminationLeftTruth :
    RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpE_andEliminationRightRecursive :
    RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpE_andEliminationRightTruth :
    RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpE_orIntroductionRightRecursive :
    RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpE_orIntroductionRightTruth :
    RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpE_orElimination :
    RawCoqRestrictedPADirectOrEliminationSemanticRoots M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpE_universalIntroduction :
    RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpE_universalEliminationRecursive :
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpE_universalEliminationTruth :
    RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpE_existentialIntroduction :
    RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpE_existentialElimination :
    RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterImpE_equalityReflexivity :
    RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterImpE_equalityElimination :
    RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
      M hPA inputs tail
}.

Arguments RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterImpElimination
  M hPA inputs tail : clear implicits.

Theorem raw_afterImpIntroductionTruth_of_afterImpElimination : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectImpERecursiveModusPonensLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs) tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterImpElimination
    M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterImpIntroductionTruth
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail himpE hremaining.
  destruct hremaining. constructor; assumption.
Qed.

(** ------------------------------------------------------------------
    Certified selection, affine transport, and growing-tail merge. *)

Definition RawCoqRestrictedPADirectSelectedImpECoreTail
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectImpECoreLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (embedPAContext (map witnessedAxiom witnesses)).

Arguments RawCoqRestrictedPADirectSelectedImpECoreTail
  M hPA inputs : clear implicits.

Lemma coqRestrictedPADirectImpECaseContext_app_witnesses : forall witnesses,
  coqRestrictedPADirectImpECaseContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectImpECaseContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  pose proof
    (coqRestrictedPADirectOrIntroductionLeftReadyContext_app_witnesses
      witnesses) as horReady.
  unfold
    coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftAdmissibleContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftCaseContext
    in horReady.
  cbn [List.app] in horReady.
  pose proof (f_equal (skipn 3) horReady) as hdeep.
  cbn [skipn] in hdeep.
  unfold
    coqRestrictedPADirectStrongStepOrIntroductionLeftDeepEndpointContext
    in hdeep.
  unfold coqRestrictedPADirectImpECaseContext,
    coqRestrictedPADirectImpEDeepContext.
  repeat rewrite raw_coqRestrictedPADirectEndpointDeepContext_shape.
  cbn [List.app]. now rewrite hdeep.
Qed.

Theorem raw_impECoreLawRoot_surround_witnessed_tail : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      prefix witnesses suffix,
  RawCoqRestrictedPADirectImpECoreLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqRestrictedPADirectImpECoreLawRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (embedPAContext
      (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))).
Proof.
  intros M hPA inputs prefix witnesses suffix (root & hroot).
  rewrite coqRestrictedPADirectImpECaseContext_app_witnesses in hroot.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (coqRestrictedPADirectImpECaseContext [])
      prefix witnesses suffix
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqRestrictedPADirectImpECoreTemplate)
      root hroot) as [transportedRoot htransported].
  exists transportedRoot.
  rewrite coqRestrictedPADirectImpECaseContext_app_witnesses.
  exact htransported.
Qed.

Definition
    RawCoqRestrictedPADirectRemainingAfterImpEliminationStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterImpElimination
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Arguments
  RawCoqRestrictedPADirectRemainingAfterImpEliminationStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem
    raw_remainingAfterImpIntroductionTruthCompiler_of_selectedImpECore :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedImpECoreTail M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterImpEliminationStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterImpIntroductionTruthStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs
    (coreWitnesses & _ & hcore) hremaining baseWitnesses.
  destruct (hremaining (baseWitnesses ++ coreWitnesses))
    as [suffix hremainingTail].
  exists (coreWitnesses ++ suffix).
  apply raw_afterImpIntroductionTruth_of_afterImpElimination.
  - apply raw_impERecursiveModusPonensLawRoot_of_coreLawRoot.
    exact (raw_impECoreLawRoot_surround_witnessed_tail
      M hPA inputs baseWitnesses coreWitnesses suffix hcore).
  - replace ((baseWitnesses ++ coreWitnesses) ++ suffix)
      with (baseWitnesses ++ (coreWitnesses ++ suffix))
      in hremainingTail by apply app_assoc.
    exact hremainingTail.
Qed.

(** Native endpoint with Imp-E absent from the final continuation.  The core
    root remains visible as the precise producer boundary. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeInputs_afterImpElimination
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
       RawCoqRestrictedPADirectRemainingAfterImpEliminationStandardTailCompiler
         M hPA inputs)))) ->
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
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeInputs_afterImpIntroductionTruth
      M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
      nextSigmaEvidence hinputs).
  intros contextTruth conclusionTruth.
  destruct (hcontinuation contextTruth conclusionTruth)
    as [horTruth [hrecursive [hsplit [hcore hremaining]]]].
  split; [exact horTruth |].
  split; [exact hrecursive |].
  split; [exact hsplit |].
  exact
    (raw_remainingAfterImpIntroductionTruthCompiler_of_selectedImpECore
      M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      hcore hremaining).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterImpElimination.
