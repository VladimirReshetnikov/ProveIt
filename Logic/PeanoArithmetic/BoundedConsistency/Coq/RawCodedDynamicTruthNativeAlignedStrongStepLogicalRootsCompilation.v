(**
  Feed the strong-step global-row handoff into the aligned native callback.

  Consecutive native local traces already expose the exact predecessor
  domains and evidence codes.  The strong-step theorem constructs the three
  logical roots required by predecessor closure from restricted/rule roots,
  two generalized global-source roots, and the proof-producing selected-row
  compiler families.  This module performs the remaining alignment once and
  presents that theorem as the witnessed-base callback consumed by native
  successor assembly.

  The resource interface below is intentionally proof-producing.  It does
  not identify a selected opened payload with a shifted conclusion by raw
  code equality; its Sigma and Pi families must transform the selected proof
  under every witnessed extension.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorGlobalRowEvidence
  RawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation
  RawCodedStrongStepPredecessorGlobalRowEvidenceCompilation
  RawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import PABoundedRawCodedDynamicTruthPredecessorGlobalRowEvidence.
Import
  PABoundedRawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.
Import PABoundedRawCodedStrongStepPredecessorGlobalRowEvidenceCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation.

(** Exact proof-producing resources for one aligned predecessor invocation.
    The strong-step translation depends on the ambient proof [hPA].  The
    native trace supplies [inputLevelNumeral] and both domain substitutions;
    this compiler supplies a matching direct structural translation,
    conclusions translating to the native evidence codes, and all six
    strong-step proof inputs. *)
Definition RawDynamicTruthNativeAlignedStrongStepResourcesCompilerWithPA
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi
      (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi)
      sourceWitnessList inputLevelNumeral,
    RawCodedPAAxiomWitnessContext M sourceWitnessList baseContext ->
    RawNumeralTermCodeAt M (raw_succ M predecessorLevel)
      inputLevelNumeral ->
    exists inputs : RawCodedTemplateDirectStructuralInputs M,
    exists localSigma localPi sigmaConclusion piConclusion : TemplateFormula,
    exists restrictedRoot ruleRoot sigmaSourceRoot piSourceRoot : M,
      rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm = inputLevelNumeral /\
      rawTemplateFormula (rawDirectStructuralTemplateTranslation M hPA inputs)
        sigmaConclusion =
        rawDynamicTruthNativeLocalAligned_currentSigmaEvidence M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned /\
      rawTemplateFormula (rawDirectStructuralTemplateTranslation M hPA inputs)
        piConclusion =
        rawDynamicTruthNativeLocalAligned_currentPiEvidence M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned /\
      RawCodedDynamicTruthSelectedPayloadShiftCompilerOnWitnessedExtensions
        M (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext [] 0 localSigma localPi sigmaConclusion /\
      RawCodedDynamicTruthSelectedPayloadShiftCompilerOnWitnessedExtensions
        M (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext [] 1 localSigma localPi piConclusion /\
      RawCodedPALocalProofOf M baseContext
        (rawDirectTemplateFormula inputs
          coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
        restrictedRoot /\
      RawCodedPALocalProofOf M baseContext
        (rawDirectTemplateFormula inputs
          coqStrongStepProofEndpointAtomicAdequacyRulePremise)
        ruleRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M baseContext)
        (rawTemplateFormula (rawDirectStructuralTemplateTranslation M hPA inputs)
          (coqDynamicTruthGlobalExistentialSource 0 localSigma localPi))
        sigmaSourceRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M baseContext)
        (rawTemplateFormula (rawDirectStructuralTemplateTranslation M hPA inputs)
          (coqDynamicTruthGlobalExistentialSource 1 localSigma localPi))
        piSourceRoot.

Arguments RawDynamicTruthNativeAlignedStrongStepResourcesCompilerWithPA
  M hPA : clear implicits.

(** Apply the strong handoff at the empty temporary prefix.  The current
    native trace supplies the exact input-level numeral and both domain
    substitutions; the resource compiler supplies everything genuinely
    proof-producing. *)
Theorem
    raw_dynamicTruthNativeLocalAlignedGrowingLogicalRootsCompilerOnWitnessedBase_of_strong_step_resources
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeAlignedStrongStepResourcesCompilerWithPA M hPA ->
  RawDynamicTruthNativeLocalAlignedGrowingLogicalRootsCompilerOnWitnessedBase
    M.
Proof.
  intros M hPA hresources tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned sourceWitnessList
    hsourceWitnessed.
  pose proof
    (rawDynamicTruthNativeLocalAligned_currentTrace M tail predecessorLevel
      baseContext currentLocal nextInputGlobalSigma nextInputGlobalPi aligned)
    as htrace.
  destruct htrace as
    (_ & inputLevel & evidenceGlobalSigma & evidenceGlobalPi &
      inputLevelNumeral & hinputLevel & hsuccessor & hnumeral &
      hsigmaDomain & hpiDomain & hsigmaApplication & hpiApplication).
  subst inputLevel.
  destruct (hresources tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned sourceWitnessList
    inputLevelNumeral hsourceWitnessed hnumeral) as
    (inputs & localSigma & localPi & sigmaConclusion & piConclusion &
      restrictedRoot & ruleRoot & sigmaSourceRoot & piSourceRoot &
      hlevel & hsigmaConclusion & hpiConclusion &
      hsigmaFamily & hpiFamily & hrestricted & hrule &
      hsigmaSource & hpiSource).
  destruct
    (raw_codedPALocalProof_strongStepPredecessorLogicalRoots_of_restricted_rule_and_global_sources_and_selected_compiler_families_under_prefix
      M hPA inputs sourceWitnessList baseContext [] inputLevelNumeral
      localSigma localPi
      (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      sigmaConclusion piConclusion
      restrictedRoot ruleRoot sigmaSourceRoot piSourceRoot)
    as (targetWitnessList & targetContext & htargetWitnessed &
      hincluded & hlogicalRoots).
  - intros formula hmember. contradiction.
  - exact hsourceWitnessed.
  - exact hlevel.
  - exact hsigmaDomain.
  - exact hpiDomain.
  - exact hsigmaFamily.
  - exact hpiFamily.
  - exact hrestricted.
  - exact hrule.
  - exact hsigmaSource.
  - exact hpiSource.
  - exists targetWitnessList, targetContext.
    split; [exact htargetWitnessed |].
    split; [exact hincluded |].
    cbn [rawTemplateContextCodeOnTail] in hlogicalRoots.
    rewrite hsigmaConclusion, hpiConclusion in hlogicalRoots.
    exact hlogicalRoots.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.
