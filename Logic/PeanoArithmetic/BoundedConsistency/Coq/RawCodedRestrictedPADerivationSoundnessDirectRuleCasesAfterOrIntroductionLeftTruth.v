(**
  Direct rule-case integration after the Or-I-left truth field.

  A proof-producing native Or-law compiler may select its own finite batch of
  standard PA axioms.  This module makes that selection compositional: the
  selected root is transported beneath an arbitrary earlier witness prefix
  and an arbitrary later suffix, then inserted into the post-Assumption
  dispatcher.  Consequently the continuation exposes twenty fields and does
  not have to coordinate its witness choices with the Or-law compiler.
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
  RawCodedTemplateSyntax
  RawCodedTemplateNumeralParameters
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase
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
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder
  RawCodedRestrictedPADerivationSoundnessNativeAfterAssumptionCompilation.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase.
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
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeAfterAssumptionCompilation.

(** Exact twenty-field remainder obtained by deleting only the Or-I-left
    dynamic truth field from the post-Assumption record. *)
Record RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterOrIntroductionLeftTruth
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectAfterOrLeftTruth_impIntroductionRecursive :
    RawCoqRestrictedPADirectImpIntroductionRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_impIntroductionTruth :
    RawCoqRestrictedPADirectImpIntroductionDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_impElimination :
    RawCoqRestrictedPADirectImpERecursiveModusPonensLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_bottomElimination :
    RawCoqRestrictedPADirectBottomRecursiveContradictionLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_excludedMiddle :
    RawCoqRestrictedPADirectExcludedMiddleTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_andIntroduction :
    RawCoqRestrictedPADirectStrongStepAndIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_andEliminationLeftRecursive :
    RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_andEliminationLeftTruth :
    RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_andEliminationRightRecursive :
    RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_andEliminationRightTruth :
    RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_orIntroductionRightRecursive :
    RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_orIntroductionRightTruth :
    RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_orElimination :
    RawCoqRestrictedPADirectOrEliminationSemanticRoots M hPA inputs tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_universalIntroduction :
    RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_universalEliminationRecursive :
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_universalEliminationTruth :
    RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_existentialIntroduction :
    RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_existentialElimination :
    RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_equalityReflexivity :
    RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterOrLeftTruth_equalityElimination :
    RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
      M hPA inputs tail
}.

Arguments
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterOrIntroductionLeftTruth
  M hPA inputs tail : clear implicits.

Theorem raw_afterAssumption_of_afterOrIntroductionLeftTruth : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectOrIntroductionLeftDynamicTruthLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterOrIntroductionLeftTruth
    M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAssumption
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail horTruth hremaining.
  destruct hremaining.
  constructor; assumption.
Qed.

(** The native Or-law compiler's selected finite tail. *)
Definition RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectOrIntroductionLeftDynamicTruthLawRoot
      M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Arguments RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail
  M hPA inputs : clear implicits.

(** Generic witness-tail transport applies because the ready context is a
    fixed finite prefix followed by the embedded PA-axiom tail. *)
Theorem raw_orIntroductionLeftTruthLawRoot_surround_witnessed_tail : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    prefix witnesses suffix,
  RawCoqRestrictedPADirectOrIntroductionLeftDynamicTruthLawRoot
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqRestrictedPADirectOrIntroductionLeftDynamicTruthLawRoot
    M hPA inputs
      (embedPAContext
        (map witnessedAxiom (prefix ++ (witnesses ++ suffix)))).
Proof.
  intros M hPA inputs prefix witnesses suffix [root hroot].
  rewrite
    coqRestrictedPADirectOrIntroductionLeftReadyContext_app_witnesses
    in hroot.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext [])
      prefix witnesses suffix
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrIntroductionLeftDynamicTruthLawTemplate)
      root hroot) as [transportedRoot htransported].
  exists transportedRoot.
  rewrite
    coqRestrictedPADirectOrIntroductionLeftReadyContext_app_witnesses.
  exact htransported.
Qed.

Definition
    RawCoqRestrictedPADirectRemainingAfterOrIntroductionLeftTruthStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterOrIntroductionLeftTruth
      M hPA inputs
      (embedPAContext
        (map witnessedAxiom (baseWitnesses ++ suffix))).

Arguments
  RawCoqRestrictedPADirectRemainingAfterOrIntroductionLeftTruthStandardTailCompiler
  M hPA inputs : clear implicits.

(** Merge the Or-law batch between the earlier prefix and the batch chosen by
    the twenty-field continuation. *)
Theorem raw_remainingAfterAssumptionCompiler_of_selectedOrIntroductionLeftTruth
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterOrIntroductionLeftTruthStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAssumptionStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs
    (orTruthWitnesses & _ & horTruth) hremaining baseWitnesses.
  destruct (hremaining (baseWitnesses ++ orTruthWitnesses))
    as [suffix hremainingTail].
  exists (orTruthWitnesses ++ suffix).
  apply raw_afterAssumption_of_afterOrIntroductionLeftTruth.
  - exact
      (raw_orIntroductionLeftTruthLawRoot_surround_witnessed_tail
        M hPA inputs baseWitnesses orTruthWitnesses suffix horTruth).
  - replace ((baseWitnesses ++ orTruthWitnesses) ++ suffix)
      with (baseWitnesses ++ (orTruthWitnesses ++ suffix))
      in hremainingTail by apply app_assoc.
    exact hremainingTail.
Qed.

(** Native package endpoint with the Or-I-left truth field absent from the
    continuation.  The selected Or-law batch and the remaining twenty-field
    compiler may depend on the native package's truth-selector choices, but
    the resulting certificate hides those choices existentially. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeInputs_afterOrIntroductionLeftTruth
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
    RawCoqRestrictedPADirectRemainingAfterOrIntroductionLeftTruthStandardTailCompiler
      M hPA inputs) ->
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
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeInputs_afterAssumption
      M hPA parameters currentGlobalSigma currentGlobalPi predecessorLevel
      nextSigmaEvidence hinputs).
  intros contextTruth conclusionTruth.
  destruct (hcontinuation contextTruth conclusionTruth)
    as [hselected hremaining].
  exact
    (raw_remainingAfterAssumptionCompiler_of_selectedOrIntroductionLeftTruth
      M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      hselected hremaining).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth.
