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
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateNumeralParameters
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedDynamicTruthTemplateNumeralParameters
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessExtendedDirectInputs
  RawCodedRestrictedPADerivationSoundnessExtendedRowIdentification
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalPositiveExactification
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPairedGlobalAdequateOrbitDeepClosure
  RawCodedDynamicTruthPairedSuccessorLocalDeepClosure
  RawCodedDynamicTruthGlobalSuccessorDeepClosure
  RawCodedDynamicTruthLocalExclusiveTemplateDirectInputs
  RawCodedDynamicTruthAlignedPredecessorExtendedRows
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthSharedSuccessorAppendGlobalRoots
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
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedDynamicTruthTemplateNumeralParameters.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedRowIdentification.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveExactification.
Import
  PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import
  PABoundedRawCodedDynamicTruthPairedGlobalAdequateOrbitDeepClosure.
Import PABoundedRawCodedDynamicTruthPairedSuccessorLocalDeepClosure.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorDeepClosure.
Import PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthAlignedPredecessorExtendedRows.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthSharedSuccessorAppendGlobalRoots.
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

(** Adapt a deeply commuting ternary selector to either of the two opaque
    five-argument slots of the direct soundness translation.  The hierarchy
    arguments are already fixed by the aligned successor edge, so this
    structural adapter intentionally ignores them. *)
Definition rawCoqDynamicTruthAlignedEvidenceDirectSelector
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (predicate : M)
    (selector : RawCodedTernaryApplicationSelector M predicate)
    (commuting : RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
      M predicate selector)
    : RawCoqRestrictedPATruthDirectSelector M parameters.
Proof.
  refine
    {| rawCoqRestrictedPATruthDirectOutput :=
         fun _lower _upper first second third =>
           rawTernaryApplicationOutput selector first second third;
       rawCoqRestrictedPATruthDirectShiftAt := _;
       rawCoqRestrictedPATruthDirectOpeningAt := _ |}.
  - intros depth lower upper first second third.
    apply
      (rawCoqDynamicTruthTemplateTernary_shift_commuting_on_syntax
        commuting).
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_shift;
        exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_shift;
        exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_shift;
        exact hPA.
  - intros depth replacement lower upper first second third.
    apply
      (rawCoqDynamicTruthTemplateTernary_opening_commuting_on_syntax
        commuting).
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax;
        exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_opening;
        exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_opening;
        exact hPA.
    + apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_opening;
        exact hPA.
Defined.

Arguments rawCoqDynamicTruthAlignedEvidenceDirectSelector
  M _ _ predicate selector _ : clear implicits.

Lemma rawCoqDynamicTruthAlignedEvidenceDirectSelector_output : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    predicate selector commuting lower upper first second third,
  rawCoqRestrictedPATruthDirectOutput
    (rawCoqDynamicTruthAlignedEvidenceDirectSelector
      M hPA parameters predicate selector commuting)
    lower upper first second third =
  rawTernaryApplicationOutput selector first second third.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Structural alignment of one native predecessor.

    The direct soundness translation reserves opaque predicate one for
    conclusion truth.  We use it for the successor Sigma predicate.  Its
    equally well-formed predicate-zero slot is instantiated by the successor
    Pi predicate, with the same argument order, solely to expose the second
    native evidence code.  This is a structural use of the selector record;
    no context-truth semantic claim is made here. *)

Definition coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate
    : TemplateFormula :=
  coqRestrictedPADerivationSoundnessConclusionTruthTemplate.

Definition coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAContextTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 2; ttVar 1; ttVar 0].

(** Everything in this package is determined by the aligned trace.  The
    local row equations are retained because the global-source compiler will
    consume those exact shared rows at the next stage. *)
Definition RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  exists localSigmaRow localPiRow : M,
    RawDynamicTruthPairedGlobalWrapperAt M
      localSigmaRow localPiRow nextInputGlobalSigma nextInputGlobalPi /\
    rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = inputLevelNumeral /\
    rawDirectTemplateFormula inputs
      coqDynamicTruthSharedSigmaSuccessorRowTemplate = localSigmaRow /\
    rawDirectTemplateFormula inputs
      coqDynamicTruthSharedPiSuccessorRowTemplate = localPiRow /\
    rawDirectTemplateFormula inputs
      coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate =
      rawDynamicTruthNativeLocalAligned_currentSigmaEvidence M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned /\
    rawDirectTemplateFormula inputs
      coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate =
      rawDynamicTruthNativeLocalAligned_currentPiEvidence M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned.

Arguments RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
  M hPA tail predecessorLevel baseContext currentLocal
  nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral inputs
  : clear implicits.

(** The aligned trace constructs the complete structural package without a
    proof-producing callback.  In particular, functionality of represented
    numeral codes and of the native three-substitution application identifies
    the independently selected direct outputs with the trace outputs. *)
Theorem raw_dynamicTruthNativeAlignedStrongStepStructuralInputs_exists :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral,
  RawNumeralTermCodeAt M (raw_succ M predecessorLevel)
    inputLevelNumeral ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs.
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    hinputLevelNumeral.
  destruct
    (raw_dynamicTruthAlignedPredecessor_extended_rows_exists
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned) as
    (traceInputLevelNumeral & upperLevelNumeral &
      localSigmaRow & localPiRow & sigmaRowDomain & piRowDomain &
      sigmaLowerApplication & piLowerApplication & parameters &
      lowerPiSelector & lowerSigmaSelector &
      lowerPiCommuting & lowerSigmaCommuting &
      hlowerBound & hupperBound & hlowerCode & hupperCode &
      htraceInputLevelNumeral & hupperLevelNumeral &
      hsigmaDomain & hpiDomain & hwrapper & hrows).
  pose proof (raw_numeralTermCodeAt_functional M hPA
    (raw_succ M predecessorLevel)
    traceInputLevelNumeral inputLevelNumeral
    htraceInputLevelNumeral hinputLevelNumeral) as hinputNumerals.
  subst traceInputLevelNumeral.

  pose proof
    (rawDynamicTruthNativeLocalAligned_currentTrace M tail predecessorLevel
      baseContext currentLocal nextInputGlobalSigma nextInputGlobalPi aligned)
    as hcurrentTrace.
  destruct hcurrentTrace as [hcurrentOrbit _hcurrentBody].
  destruct
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_deep_closed
      M hPA tail (raw_succ M predecessorLevel)
      (rawDynamicTruthNativeLocalAligned_currentInputGlobalSigma M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentInputGlobalPi M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      hcurrentOrbit) as [hcurrentSigmaDeep hcurrentPiDeep].
  destruct (dynamicTruthPairedGlobalSuccessorAt_deep_closed
    M hPA (raw_dynamicTruthPairedGlobalSuccessorLocalDeepClosure M hPA)
    (rawDynamicTruthNativeLocalAligned_currentInputGlobalSigma M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned)
    (rawDynamicTruthNativeLocalAligned_currentInputGlobalPi M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned)
    (raw_succ M predecessorLevel)
    nextInputGlobalSigma nextInputGlobalPi
    hcurrentSigmaDeep hcurrentPiDeep
    (rawDynamicTruthNativeLocalAligned_successor M tail predecessorLevel
      baseContext currentLocal nextInputGlobalSigma nextInputGlobalPi
      aligned)) as [hnextSigmaDeep hnextPiDeep].
  destruct
    (raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed
      M hPA nextInputGlobalSigma hnextSigmaDeep) as
    [sigmaSelector hsigmaCommuting].
  destruct
    (raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed
      M hPA nextInputGlobalPi hnextPiDeep) as
    [piSelector hpiCommuting].
  set (contextTruth :=
    rawCoqDynamicTruthAlignedEvidenceDirectSelector
      M hPA parameters nextInputGlobalPi piSelector hpiCommuting).
  set (conclusionTruth :=
    rawCoqDynamicTruthAlignedEvidenceDirectSelector
      M hPA parameters nextInputGlobalSigma sigmaSelector hsigmaCommuting).
  set (compatibilityPackage :=
    rawCoqDynamicTruthTemplateNumeralTermPackage M hPA
      (raw_succ M predecessorLevel)
      (raw_succ M (raw_succ M predecessorLevel))
      (rawCoqDynamicTruthLocalExclusiveOpaqueCode
        lowerSigmaSelector lowerPiSelector)
      parameters hlowerBound hupperBound).
  set (inputs := rawCoqRestrictedPAExtendedRowsInputs
    M hPA parameters contextTruth conclusionTruth
    (rawDynamicTruthNativeLocalAligned_currentInputGlobalPi M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned)
    (rawDynamicTruthNativeLocalAligned_currentInputGlobalSigma M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned)
    lowerPiSelector lowerSigmaSelector
    lowerPiCommuting lowerSigmaCommuting).
  destruct (hrows contextTruth conclusionTruth) as
    [hlowerTerm [hsigmaRow hpiRow]].
  exists inputs, localSigmaRow, localPiRow.
  split; [exact hwrapper |].
  split.
  { unfold inputs. rewrite hlowerTerm. exact hinputNumerals. }
  split.
  { unfold inputs, coqDynamicTruthSharedSigmaSuccessorRowTemplate.
    exact hsigmaRow. }
  split.
  { unfold inputs, coqDynamicTruthSharedPiSuccessorRowTemplate.
    exact hpiRow. }
  split.
  - unfold coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate,
      coqRestrictedPADerivationSoundnessConclusionTruthTemplate.
    unfold inputs, rawCoqRestrictedPAExtendedRowsInputs.
    rewrite
      rawCoqRestrictedPADerivationSoundnessExtendedConclusionTruthLeaf_view.
    unfold conclusionTruth.
    rewrite rawCoqDynamicTruthAlignedEvidenceDirectSelector_output.
    cbn [rawCoqRestrictedPADerivationSoundnessTemplateTermView
      rawCoqRestrictedPADerivationSoundnessTermViewSymbols
      rawStructuralTemplateTermWith rawNumeralTemplateSymbols].
    exact (raw_dynamicTruthLocalTernaryApplication_functional M hPA
      nextInputGlobalSigma
      (rawTernaryApplicationOutput sigmaSelector
        (rawTermVarCode M (rawNumeralValue M 2))
        (rawTermVarCode M (rawNumeralValue M 1))
        (rawTermVarCode M (rawNumeralValue M 0)))
      (rawDynamicTruthNativeLocalAligned_currentSigmaEvidence M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawCoqDynamicTruthLocalApplicationCompatibility_holds
        M hPA
        (raw_succ M predecessorLevel)
        (raw_succ M (raw_succ M predecessorLevel))
        (rawDynamicTruthNativeLocalAligned_currentInputGlobalSigma M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        (rawDynamicTruthNativeLocalAligned_currentInputGlobalPi M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        lowerSigmaSelector lowerPiSelector compatibilityPackage
        nextInputGlobalSigma sigmaSelector)
      (rawDynamicTruthNativeLocalAligned_sigmaApplication M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)).
  - unfold coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate.
    unfold inputs, rawCoqRestrictedPAExtendedRowsInputs.
    rewrite
      rawCoqRestrictedPADerivationSoundnessExtendedContextTruthLeaf_view.
    unfold contextTruth.
    rewrite rawCoqDynamicTruthAlignedEvidenceDirectSelector_output.
    cbn [rawCoqRestrictedPADerivationSoundnessTemplateTermView
      rawCoqRestrictedPADerivationSoundnessTermViewSymbols
      rawStructuralTemplateTermWith rawNumeralTemplateSymbols].
    exact (raw_dynamicTruthLocalTernaryApplication_functional M hPA
      nextInputGlobalPi
      (rawTernaryApplicationOutput piSelector
        (rawTermVarCode M (rawNumeralValue M 2))
        (rawTermVarCode M (rawNumeralValue M 1))
        (rawTermVarCode M (rawNumeralValue M 0)))
      (rawDynamicTruthNativeLocalAligned_currentPiEvidence M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawCoqDynamicTruthLocalApplicationCompatibility_holds
        M hPA
        (raw_succ M predecessorLevel)
        (raw_succ M (raw_succ M predecessorLevel))
        (rawDynamicTruthNativeLocalAligned_currentInputGlobalSigma M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        (rawDynamicTruthNativeLocalAligned_currentInputGlobalPi M tail
          predecessorLevel baseContext currentLocal
          nextInputGlobalSigma nextInputGlobalPi aligned)
        lowerSigmaSelector lowerPiSelector compatibilityPackage
        nextInputGlobalPi piSelector)
      (rawDynamicTruthNativeLocalAligned_piApplication M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)).
Qed.

(** Residual proof resources after structural alignment.  Every formula and
    translation in this callback is fixed by the preceding constructor; the
    caller now supplies only represented proofs and the two payload-to-
    evidence proof compilers. *)
Definition
    RawDynamicTruthNativeAlignedStrongStepProofResourcesCompilerWithPA
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi
      (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi)
      sourceWitnessList inputLevelNumeral
      (inputs : RawCodedTemplateDirectStructuralInputs M),
    RawCodedPAAxiomWitnessContext M sourceWitnessList baseContext ->
    RawNumeralTermCodeAt M (raw_succ M predecessorLevel)
      inputLevelNumeral ->
    RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
    exists restrictedRoot ruleRoot sigmaSourceRoot piSourceRoot : M,
      RawCodedDynamicTruthSelectedPayloadShiftCompilerOnWitnessedExtensions
        M (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext [] 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate /\
      RawCodedDynamicTruthSelectedPayloadShiftCompilerOnWitnessedExtensions
        M (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext [] 1
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate /\
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
        (rawDirectTemplateFormula inputs
          (coqDynamicTruthGlobalExistentialSource 0
            coqDynamicTruthSharedSigmaSuccessorRowTemplate
            coqDynamicTruthSharedPiSuccessorRowTemplate))
        sigmaSourceRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M baseContext)
        (rawDirectTemplateFormula inputs
          (coqDynamicTruthGlobalExistentialSource 1
            coqDynamicTruthSharedSigmaSuccessorRowTemplate
            coqDynamicTruthSharedPiSuccessorRowTemplate))
        piSourceRoot.

Arguments
  RawDynamicTruthNativeAlignedStrongStepProofResourcesCompilerWithPA
  M hPA : clear implicits.

(** Further relaxed proof boundary matching append traversal.  The two
    generalized global sources may be produced only after choosing a larger
    witnessed PA context; their package records that context and inclusion
    instead of requiring impossible contraction back to [baseContext]. *)
Definition
    RawDynamicTruthNativeAlignedStrongStepGrowingProofResourcesCompilerWithPA
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi
      (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi)
      sourceWitnessList inputLevelNumeral
      (inputs : RawCodedTemplateDirectStructuralInputs M),
    RawCodedPAAxiomWitnessContext M sourceWitnessList baseContext ->
    RawNumeralTermCodeAt M (raw_succ M predecessorLevel)
      inputLevelNumeral ->
    RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
    exists restrictedRoot ruleRoot : M,
      RawCodedDynamicTruthSelectedPayloadShiftCompilerOnWitnessedExtensions
        M (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext [] 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate /\
      RawCodedDynamicTruthSelectedPayloadShiftCompilerOnWitnessedExtensions
        M (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext [] 1
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate /\
      RawCodedPALocalProofOf M baseContext
        (rawDirectTemplateFormula inputs
          coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
        restrictedRoot /\
      RawCodedPALocalProofOf M baseContext
        (rawDirectTemplateFormula inputs
          coqStrongStepProofEndpointAtomicAdequacyRulePremise)
        ruleRoot /\
      RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
        baseContext
        (rawDirectTemplateFormula inputs
          (coqDynamicTruthGlobalExistentialSource 0
            coqDynamicTruthSharedSigmaSuccessorRowTemplate
            coqDynamicTruthSharedPiSuccessorRowTemplate))
        (rawDirectTemplateFormula inputs
          (coqDynamicTruthGlobalExistentialSource 1
            coqDynamicTruthSharedSigmaSuccessorRowTemplate
            coqDynamicTruthSharedPiSuccessorRowTemplate)).

Arguments
  RawDynamicTruthNativeAlignedStrongStepGrowingProofResourcesCompilerWithPA
  M hPA : clear implicits.

(** Append-facing residual boundary.  Unlike the growing resource package
    above, this interface does not ask a client to synchronize the two
    polarities or transport their roots to the current callback context.
    It exposes the two normalized opaque-row append traces at one standard
    helper prefix; [raw_dynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom_of_shared_successor_append_input_packages]
    performs all subsequent context assembly. *)
Definition
    RawDynamicTruthNativeAlignedStrongStepAppendProofResourcesCompilerWithPA
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (tail : nat -> M) predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi
      (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi)
      sourceWitnessList inputLevelNumeral
      (inputs : RawCodedTemplateDirectStructuralInputs M),
    RawCodedPAAxiomWitnessContext M sourceWitnessList baseContext ->
    RawNumeralTermCodeAt M (raw_succ M predecessorLevel)
      inputLevelNumeral ->
    RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
    exists restrictedRoot ruleRoot : M,
    exists appendWitnesses : StandardPAAxiomWitnessPrefix,
      RawCodedDynamicTruthSelectedPayloadShiftCompilerOnWitnessedExtensions
        M (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext [] 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate /\
      RawCodedDynamicTruthSelectedPayloadShiftCompilerOnWitnessedExtensions
        M (rawDirectStructuralTemplateTranslation M hPA inputs)
        baseContext [] 1
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate /\
      RawCodedPALocalProofOf M baseContext
        (rawDirectTemplateFormula inputs
          coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
        restrictedRoot /\
      RawCodedPALocalProofOf M baseContext
        (rawDirectTemplateFormula inputs
          coqStrongStepProofEndpointAtomicAdequacyRulePremise)
        ruleRoot /\
      RawDynamicTruthSharedSuccessorAppendGlobalInputsAt M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        0 appendWitnesses /\
      RawDynamicTruthSharedSuccessorAppendGlobalInputsAt M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        1 appendWitnesses.

Arguments
  RawDynamicTruthNativeAlignedStrongStepAppendProofResourcesCompilerWithPA
  M hPA : clear implicits.

(** Compile append traces into the growing global-source package expected by
    the strong-step handoff.  The caller's witnessed base is merged with the
    append helper context, so no contraction or context-code equality is
    hidden in this adapter. *)
Theorem
    raw_dynamicTruthNativeAlignedStrongStepGrowingProofResourcesCompilerWithPA_of_append_proof_resources
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeAlignedStrongStepAppendProofResourcesCompilerWithPA
    M hPA ->
  RawDynamicTruthNativeAlignedStrongStepGrowingProofResourcesCompilerWithPA
    M hPA.
Proof.
  intros M hPA happend tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned sourceWitnessList
    inputLevelNumeral inputs hsourceWitnessed hinputNumeral hstructural.
  destruct (happend tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned sourceWitnessList
    inputLevelNumeral inputs hsourceWitnessed hinputNumeral hstructural) as
    (restrictedRoot & ruleRoot & appendWitnesses &
      hsigmaFamily & hpiFamily & hrestricted & hrule &
      hsigmaInputs & hpiInputs).
  exists restrictedRoot, ruleRoot.
  split; [exact hsigmaFamily |].
  split; [exact hpiFamily |].
  split; [exact hrestricted |].
  split; [exact hrule |].
  exact
    (raw_dynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom_of_shared_successor_append_input_packages
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      sourceWitnessList baseContext appendWitnesses
      hsourceWitnessed hsigmaInputs hpiInputs).
Qed.

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

(** The structural constructor discharges every witness and equality in the
    original resource interface.  This adapter is the preferred boundary for
    subsequent work: proving the residual compiler is sufficient for the
    strong-step handoff. *)
Theorem
    raw_dynamicTruthNativeAlignedStrongStepResourcesCompilerWithPA_of_proof_resources
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeAlignedStrongStepProofResourcesCompilerWithPA M hPA ->
  RawDynamicTruthNativeAlignedStrongStepResourcesCompilerWithPA M hPA.
Proof.
  intros M hPA hproofs tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned
    sourceWitnessList inputLevelNumeral hsourceWitnessed hinputNumeral.
  destruct
    (raw_dynamicTruthNativeAlignedStrongStepStructuralInputs_exists
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral hinputNumeral) as [inputs hstructural].
  pose proof hstructural as hstructuralForProofs.
  destruct hstructural as
    (localSigmaRow & localPiRow & hwrapper & hlower &
      hsigmaRow & hpiRow & hsigmaEvidence & hpiEvidence).
  destruct (hproofs tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned
    sourceWitnessList inputLevelNumeral inputs
    hsourceWitnessed hinputNumeral hstructuralForProofs) as
    (restrictedRoot & ruleRoot & sigmaSourceRoot & piSourceRoot &
      hsigmaFamily & hpiFamily & hrestricted & hrule &
      hsigmaSource & hpiSource).
  exists inputs,
    coqDynamicTruthSharedSigmaSuccessorRowTemplate,
    coqDynamicTruthSharedPiSuccessorRowTemplate,
    coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate,
    coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate.
  exists restrictedRoot, ruleRoot, sigmaSourceRoot, piSourceRoot.
  split; [exact hlower |].
  split; [exact hsigmaEvidence |].
  split; [exact hpiEvidence |].
  split; [exact hsigmaFamily |].
  split; [exact hpiFamily |].
  split; [exact hrestricted |].
  split; [exact hrule |].
  split; [exact hsigmaSource | exact hpiSource].
Qed.

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

(** Direct aligned client of the growing global-source handoff.  Structural
    inputs are reconstructed from the trace, append-selected source growth is
    retained, and the final evidence equations are rewritten only after the
    strong-step proof has returned its common witnessed context. *)
Theorem
    raw_dynamicTruthNativeLocalAlignedGrowingLogicalRootsCompilerOnWitnessedBase_of_growing_proof_resources
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeAlignedStrongStepGrowingProofResourcesCompilerWithPA
    M hPA ->
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
  destruct
    (raw_dynamicTruthNativeAlignedStrongStepStructuralInputs_exists
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral hnumeral) as [inputs hstructural].
  pose proof hstructural as hstructuralForResources.
  destruct hstructural as
    (localSigmaRow & localPiRow & hwrapper & hlevel &
      hsigmaRow & hpiRow & hsigmaConclusion & hpiConclusion).
  destruct (hresources tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned sourceWitnessList
    inputLevelNumeral inputs hsourceWitnessed hnumeral
    hstructuralForResources) as
    (restrictedRoot & ruleRoot & hsigmaFamily & hpiFamily &
      hrestricted & hrule & hglobalSources).
  destruct
    (raw_codedPALocalProof_strongStepPredecessorLogicalRoots_of_restricted_rule_and_growing_global_sources_and_selected_compiler_families
      M hPA inputs sourceWitnessList baseContext inputLevelNumeral
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      (rawDynamicTruthNativeLocalAligned_currentSigmaDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      (rawDynamicTruthNativeLocalAligned_currentPiDomain M tail
        predecessorLevel baseContext currentLocal
        nextInputGlobalSigma nextInputGlobalPi aligned)
      coqDynamicTruthNativeAlignedSigmaEvidenceConclusionTemplate
      coqDynamicTruthNativeAlignedPiEvidenceConclusionTemplate
      restrictedRoot ruleRoot
      hsourceWitnessed hlevel hsigmaDomain hpiDomain
      hsigmaFamily hpiFamily hrestricted hrule hglobalSources) as
    (targetWitnessList & targetContext & htargetWitnessed &
      hincluded & hlogicalRoots).
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  rewrite hsigmaConclusion, hpiConclusion in hlogicalRoots.
  exact hlogicalRoots.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.
