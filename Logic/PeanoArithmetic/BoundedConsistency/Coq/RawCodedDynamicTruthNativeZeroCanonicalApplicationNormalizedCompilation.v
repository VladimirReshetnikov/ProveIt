(**
  Canonical application-root boundary for the normalized rank-zero callback.

  Normalization retains the represented local resources and the complete
  canonical trace.  A proof-producing traversal may extend the witnessed PA
  tail while compiling the two first-successor applications.  This module
  states that exact residual and shows that it is sufficient for the older
  native direct-evidence callback by composing the reusable predecessor-state
  transport.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedLtSuccCasesProofCompilation
  RawCodedPAGrowingTemplateConjunction
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateBottomDirectStructuralInputs
  RawCodedTemplatePAEmbedding
  RawCodedFourStateTableAppendProofCompilation
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthLocalExclusiveTemplateDirectInputs
  RawCodedDynamicTruthLocalFieldProjectionCompilation
  RawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification
  RawCodedDynamicTruthLocalAdmissibilityCompilation
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorDirectEvidenceLogicalRoots
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation
  RawCodedDynamicTruthNativeZeroCanonicalTraceExactification
  RawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification
  RawCodedDynamicTruthNativeZeroCanonicalApplicationProofTransport
  RawCodedDynamicTruthNativeZeroCanonicalApplicationDirectEvidence
  RawCodedStrongStepPredecessorGlobalRowEvidenceCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationNormalizedCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedPAGrowingTemplateConjunction.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateBottomDirectStructuralInputs.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import
  PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthLocalFieldProjectionCompilation.
Import
  PABoundedRawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification.
Import PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorDirectEvidenceLogicalRoots.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalTraceExactification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationProofTransport.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationDirectEvidence.
Import
  PABoundedRawCodedStrongStepPredecessorGlobalRowEvidenceCompilation.

Import ListNotations.

(** Producer-facing split of the canonical application package.  Arithmetic
    endpoint compilation may first choose a witnessed context carrying
    atomic adequacy and the domain disjunction.  Global traversal is then
    allowed to grow once more while returning the two canonical applications
    through the standard growing-pair interface. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists endpointWitnessList endpointContext atomicRoot domainRoot,
      RawCodedPAAxiomWitnessContext M endpointWitnessList endpointContext /\
      RawContextListIncluded M baseContext endpointContext /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawFormulaOrCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M)) domainRoot /\
      RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
        endpointContext
        (rawQuotedFormulaCode M
          dynamicTruthZeroInputGlobalSigmaApplicationFormula)
        (rawQuotedFormulaCode M
          dynamicTruthZeroInputGlobalPiApplicationFormula).

Arguments
  RawDynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources
  M translation : clear implicits.

(** Append-facing form of the same residual.  Unlike an empty-prefix pair,
    these applications are compiled with the two predecessor-state formulas
    already present.  This is essential: the canonical Sigma application is
    not itself an open theorem of PA. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists endpointWitnessList endpointContext atomicRoot domainRoot,
      RawCodedPAAxiomWitnessContext M endpointWitnessList endpointContext /\
      RawContextListIncluded M baseContext endpointContext /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawFormulaOrCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M)) domainRoot /\
      RawCodedPAGrowingTemplateLocalProofPairAt M translation
        endpointContext coqDynamicTruthPredecessorStateTemplateContext
        (rawQuotedFormulaCode M
          dynamicTruthZeroInputGlobalSigmaApplicationFormula)
        (rawQuotedFormulaCode M
          dynamicTruthZeroInputGlobalPiApplicationFormula).

Arguments
  RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources
  M translation : clear implicits.

(** Canonical application resources which retain the caller assumptions of
    the direct strong-step shell.  Both arithmetic roots live under the
    joint predecessor state above [callerPrefix], and the synchronized
    application pair retains the definitionally equal combined template
    prefix. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (callerPrefix : TemplateContext) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists endpointWitnessList endpointContext atomicRoot domainRoot,
      RawCodedPAAxiomWitnessContext M endpointWitnessList endpointContext /\
      RawContextListIncluded M baseContext endpointContext /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M
          (rawTemplateContextCodeOnTail
            (rawBottomDirectStructuralTemplateTranslation M hPA)
            endpointContext callerPrefix))
        (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M
          (rawTemplateContextCodeOnTail
            (rawBottomDirectStructuralTemplateTranslation M hPA)
            endpointContext callerPrefix))
        (rawFormulaOrCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M)) domainRoot /\
      RawCodedPAGrowingTemplateLocalProofPairAt M
        (rawBottomDirectStructuralTemplateTranslation M hPA)
        endpointContext
        (coqDynamicTruthPredecessorStateTemplateContext ++ callerPrefix)
        (rawQuotedFormulaCode M
          dynamicTruthZeroInputGlobalSigmaApplicationFormula)
        (rawQuotedFormulaCode M
          dynamicTruthZeroInputGlobalPiApplicationFormula).

Arguments
  RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources
  M hPA callerPrefix : clear implicits.

(** Final rank-zero logical roots under the retained caller prefix.  This is
    the exact prefix-parametric counterpart of the state-only normalized
    callback result consumed by direct rule dispatch. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerUnderCallerPrefixOnCanonicalNormalizedResources
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (callerPrefix : TemplateContext) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists targetWitnessList targetContext,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawDynamicTruthPredecessorStateLogicalRootsAt M
        (rawTemplateContextCodeOnTail
          (rawBottomDirectStructuralTemplateTranslation M hPA)
          targetContext callerPrefix)
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)
        (rawDynamicTruthZeroSigmaEvidenceCode M)
        (rawDynamicTruthZeroPiEvidenceCode M).

Arguments
  RawDynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerUnderCallerPrefixOnCanonicalNormalizedResources
  M hPA callerPrefix : clear implicits.

(** Concrete append-facing residue.  Arithmetic normalization first chooses
    one witnessed endpoint carrying atomic adequacy and the rank-domain
    disjunction.  The remaining traversal producer supplies both canonical
    row-implication packages under the literal predecessor-state prefix, at
    one standard helper batch.  The five row binders and seventh-field
    normalization are compiled by the adapter below.  Packaging both
    polarities together records the synchronization required by the
    downstream growing pair and avoids two independently chosen append
    contexts. *)
Definition
    RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendInputResourcesCompilerOnCanonicalNormalizedResources
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists endpointWitnessList endpointContext atomicRoot domainRoot,
    exists appendWitnesses : StandardPAAxiomWitnessPrefix,
      RawCodedPAAxiomWitnessContext M endpointWitnessList endpointContext /\
      RawContextListIncluded M baseContext endpointContext /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawFormulaOrCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M)) domainRoot /\
      RawDynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt
        M translation 0 coqDynamicTruthPredecessorStateTemplateContext
          appendWitnesses /\
      RawDynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt
        M translation 1 coqDynamicTruthPredecessorStateTemplateContext
          appendWitnesses.

Arguments
  RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendInputResourcesCompilerOnCanonicalNormalizedResources
  M translation : clear implicits.

(** Invocation-dependent arithmetic endpoint, separated from the canonical
    append traversal.  The endpoint consumes normalized roots and the trace;
    it does not choose append witnesses or mention either polarity. *)
Definition
    RawDynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerOnCanonicalNormalizedResources
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists endpointWitnessList endpointContext atomicRoot domainRoot,
      RawCodedPAAxiomWitnessContext M endpointWitnessList endpointContext /\
      RawContextListIncluded M baseContext endpointContext /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawFormulaOrCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M)) domainRoot.

Arguments
  RawDynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerOnCanonicalNormalizedResources
  M translation : clear implicits.

(** Prefix-preserving endpoint used inside the direct strong-step shell.
    The caller prefix contains proof-analysis assumptions which must survive
    the rank-zero traversal.  The two predecessor-state assumptions remain
    outermost, while the caller prefix is retained immediately above the
    witnessed PA tail.  The bottom structural translation is fixed because
    rank zero fixes all three arithmetic alignments canonically. *)
Definition
    RawDynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M)
    (callerPrefix : TemplateContext) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists endpointWitnessList endpointContext atomicRoot domainRoot,
      RawCodedPAAxiomWitnessContext M endpointWitnessList endpointContext /\
      RawContextListIncluded M baseContext endpointContext /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M
          (rawTemplateContextCodeOnTail
            (rawBottomDirectStructuralTemplateTranslation M hPA)
            endpointContext callerPrefix))
        (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M
          (rawTemplateContextCodeOnTail
            (rawBottomDirectStructuralTemplateTranslation M hPA)
            endpointContext callerPrefix))
        (rawFormulaOrCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M)) domainRoot.

Arguments
  RawDynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources
  M hPA translation callerPrefix : clear implicits.

(** Decision-only consequence of a normalized rank-zero invocation.  The
    stored local field already contains totality of the two fixed evidence
    predicates; an arithmetic endpoint supplies exactly the admissibility
    premises needed to use it.  The result retains the caller prefix and may
    grow the witnessed PA tail, just like the surrounding callback
    interfaces. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingEvidenceDecisionCompilerUnderCallerPrefixOnCanonicalNormalizedResources
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M)
    (callerPrefix : TemplateContext) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists targetWitnessList targetContext decisionRoot,
      RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
      RawContextListIncluded M baseContext targetContext /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M
          (rawTemplateContextCodeOnTail
            (rawBottomDirectStructuralTemplateTranslation M hPA)
            targetContext callerPrefix))
        (rawFormulaOrCode M
          (rawDynamicTruthZeroSigmaEvidenceCode M)
          (rawDynamicTruthZeroPiEvidenceCode M)) decisionRoot.

Arguments
  RawDynamicTruthNativeLocalZeroGrowingEvidenceDecisionCompilerUnderCallerPrefixOnCanonicalNormalizedResources
  M hPA translation callerPrefix : clear implicits.

(** Independently growing atomic-adequacy endpoint. *)
Definition
    RawDynamicTruthNativeLocalZeroCanonicalAtomicEndpointCompilerOnCanonicalNormalizedResources
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    RawCodedPAGrowingTemplateLocalProofAt M translation
      witnessList baseContext coqDynamicTruthPredecessorStateTemplateContext
      (rawDynamicTruthLocalAtomicAdequacyCode M).

Arguments
  RawDynamicTruthNativeLocalZeroCanonicalAtomicEndpointCompilerOnCanonicalNormalizedResources
  M translation : clear implicits.

(** Independently growing rank-domain endpoint. *)
Definition
    RawDynamicTruthNativeLocalZeroCanonicalDomainEndpointCompilerOnCanonicalNormalizedResources
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    RawCodedPAGrowingTemplateLocalProofAt M translation
      witnessList baseContext coqDynamicTruthPredecessorStateTemplateContext
      (rawFormulaOrCode M
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)).

Arguments
  RawDynamicTruthNativeLocalZeroCanonicalDomainEndpointCompilerOnCanonicalNormalizedResources
  M translation : clear implicits.

(** Primitive arithmetic resources for the rank-zero endpoint.  The
    normalized callback need not manufacture atomic adequacy and the rank
    disjunction directly: the generic strong-step endpoint theorem derives
    both from restricted-proof validity and rule validity.  The producer
    chooses the structural interpretation used by those two formulas and
    records only the three alignments needed by that theorem.  Both roots may
    use the predecessor-state assumptions already present at their actual
    call site; no contraction to the bare PA tail is required. *)
Definition
    RawDynamicTruthNativeLocalZeroCanonicalRestrictedRuleEndpointInputsCompilerOnCanonicalNormalizedResources
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists inputs : RawCodedTemplateDirectStructuralInputs M,
    exists levelNumeral restrictedRoot ruleRoot : M,
      rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm = levelNumeral /\
      RawCodedFormulaSingleSubstitution M levelNumeral
        (rawNumeralValue M
          (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
        (rawDynamicTruthZeroSigmaDomainCode M) /\
      RawCodedFormulaSingleSubstitution M levelNumeral
        (rawNumeralValue M
          (formulaCode dynamicTruthLocalPiInputDomainTemplate))
        (rawDynamicTruthZeroPiDomainCode M) /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M baseContext)
        (rawDirectTemplateFormula inputs
          coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
        restrictedRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M baseContext)
        (rawDirectTemplateFormula inputs
          coqStrongStepProofEndpointAtomicAdequacyRulePremise)
        ruleRoot.

Arguments
  RawDynamicTruthNativeLocalZeroCanonicalRestrictedRuleEndpointInputsCompilerOnCanonicalNormalizedResources
  M translation : clear implicits.

(** All structural data for the canonical rank-zero endpoint is fixed.  Keep
    the three facts in one package so fixed-tail and growing-tail clients use
    the same numeral and substitution witnesses. *)
Lemma raw_dynamicTruthNativeLocalZeroCanonicalBottomEndpointAlignments :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  rawDirectTemplateTerm (rawBottomTemplateDirectStructuralInputs M hPA)
      coqRestrictedPASoundnessLowerLevelTerm =
      rawQuotedTermCode M (Term.numeral 0) /\
  RawCodedFormulaSingleSubstitution M
      (rawQuotedTermCode M (Term.numeral 0))
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
      (rawDynamicTruthZeroSigmaDomainCode M) /\
  RawCodedFormulaSingleSubstitution M
      (rawQuotedTermCode M (Term.numeral 0))
      (rawNumeralValue M
        (formulaCode dynamicTruthLocalPiInputDomainTemplate))
      (rawDynamicTruthZeroPiDomainCode M).
Proof.
  intros M hPA.
  split.
  - exact (rawBottomDirectTemplate_lowerLevelTerm M hPA).
  - split.
    + rewrite <- (rawQuotedFormulaCode_standard M hPA
        dynamicTruthLocalSigmaInputDomainTemplate).
      exact (raw_dynamicTruthZeroSigmaDomain_substitution M hPA).
    + rewrite <- (rawQuotedFormulaCode_standard M hPA
        dynamicTruthLocalPiInputDomainTemplate).
      exact (raw_dynamicTruthZeroPiDomain_substitution M hPA).
Qed.

(** The append traversal reserves parameter name six for its row bound.  In
    the canonical bottom translation every successor parameter name selects
    the upper numeral, which is also zero.  Consequently its represented
    below-branch is the no-less-than-zero antecedent compiled in the light
    arithmetic layer. *)
Lemma raw_dynamicTruthZeroCanonicalBottom_append_below_parameter_zero :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  rawTemplateFormula (rawBottomDirectStructuralTemplateTranslation M hPA)
    (coqLtSuccCasesBelowTemplate
      (ttVar 4)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)) =
  rawTemplateFormula (rawBottomDirectStructuralTemplateTranslation M hPA)
    (coqNoLtZeroAntecedentTemplate (ttVar 4)).
Proof.
  intros M hPA.
  rewrite coqNoLtZeroAntecedentTemplate_append_below_zero.
  reflexivity.
Qed.

(** Compile append existence first, then grow that witnessed tail once for
    the vacuous inherited traversal.  The result is the complete inherited
    half of the canonical row payload on one synchronized standard witness
    batch.  No predecessor lookup theorem is assumed: [bottom -> bottom] is
    proved locally and the impossible [rowIndex < 0] premise supplies every
    row production. *)
Theorem
    raw_dynamicTruthZeroCanonicalBottom_permutedAppendInheritedRowResourcesUnderPrefix_on_standardWitnessTail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    rootMode outerPrefix,
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) /\
    RawDynamicTruthZeroCanonicalPermutedAppendInheritedRowResourcesUnderPrefixAt
      M (rawBottomDirectStructuralTemplateTranslation M hPA)
      rootMode outerPrefix witnesses.
Proof.
  intros M hPA rootMode outerPrefix.
  set (translation := rawBottomDirectStructuralTemplateTranslation M hPA).
  set (inputs := rawBottomTemplateDirectStructuralInputs M hPA).
  set (rowPrefix :=
    templateContextShiftMany 5
      (coqFourStateTableAppendWitnessContext
        (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
        (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
        (ttParameter coqDynamicTruthAppendRowBoundParameterName)
        (embedPATerm (Term.numeral rootMode))
        (ttVar 2) (ttVar 1) (ttVar 0) outerPrefix)).
  destruct
    (raw_dynamicTruthZeroCanonicalPermutedAppendRoot_on_standardWitnessTail
      M hPA translation
      (rawBottomDirectStructuralTemplatePAAgreement M hPA) rootMode)
    as (appendWitnesses & appendRoot & happendWitnessed & happend).
  destruct
    (raw_codedPALocalProofOf_below_zero_imp_ignored_imp_on_witnessed_tail_under_prefix
      M hPA translation
      (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        appendWitnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        appendWitnesses (raw_zero M))
      (templateContextShiftMany 5 rowPrefix) (ttVar 4)
      coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate
      (templateFormulaShiftMany 5
        (coqFourStateTableAppendConcreteClosedRowProductionTemplate
          (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
          (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)))
      (raw_directStructuralTemplatePrefix_atomically_adequate
        M hPA inputs (templateContextShiftMany 5 rowPrefix))
      ((raw_directStructuralTemplatePrefix_atomically_adequate
          M hPA inputs [coqNoLtZeroAntecedentTemplate (ttVar 4)])
        (coqNoLtZeroAntecedentTemplate (ttVar 4))
        (or_introl eq_refl))
      ((raw_directStructuralTemplatePrefix_atomically_adequate
          M hPA inputs
          [coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate])
        coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate
        (or_introl eq_refl))
      happendWitnessed)
    as (traversalWitnesses & bodyRoot & hfinalWitnessed & hbody).
  set (finalWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      traversalWitnesses
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        appendWitnesses (raw_zero M))).
  set (finalContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      traversalWitnesses
      (rawStandardPAAxiomWitnessPrefixContextCode M
        appendWitnesses (raw_zero M))).
  assert (hboundBody : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation finalContext
        (templateContextShiftMany 5 rowPrefix))
      (rawTemplateFormula translation
        coqDynamicTruthZeroCanonicalVacuousInheritedBoundRowBodyTemplate)
      bodyRoot).
  {
    unfold coqDynamicTruthZeroCanonicalVacuousInheritedBoundRowBodyTemplate.
    rewrite !rawTemplateFormula_imp.
    unfold translation in hbody |- *.
    rewrite raw_dynamicTruthZeroCanonicalBottom_append_below_parameter_zero.
    exact hbody.
  }
  destruct
    (raw_codedPALocalProofOf_universal_introduction_chain_on_witnessed_tail
      M hPA translation finalWitnessList finalContext 5
      rowPrefix
      coqDynamicTruthZeroCanonicalVacuousInheritedBoundRowBodyTemplate
      bodyRoot hfinalWitnessed hboundBody)
    as [traversalRoot htraversal].
  set (visibleRowContext :=
    rawTemplateContextCodeOnTail translation finalContext rowPrefix).
  assert (hvisibleRowContext : RawContextListRealizable M visibleRowContext).
  {
    unfold visibleRowContext.
    exact (raw_templateContextOnTail_realizable M hPA translation
      finalContext rowPrefix
      (raw_codedPAAxiomWitnessContext_context_realizable M
        finalWitnessList finalContext hfinalWitnessed)).
  }
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    visibleRowContext (rawFormulaBotCode M) hvisibleRowContext)
    as holdLookupBody.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    visibleRowContext (rawFormulaBotCode M) (rawFormulaBotCode M)
    _ holdLookupBody) as holdLookup.
  lazymatch type of holdLookup with
  | RawCodedPALocalProofOf _ _ _ ?oldLookupRoot =>
      assert (holdLookupTemplate : RawCodedPALocalProofOf M
        visibleRowContext
        (rawTemplateFormula translation
          coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate)
        oldLookupRoot)
  end.
  {
    unfold coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate.
    rewrite rawTemplateFormula_imp, rawTemplateFormula_bot.
    exact holdLookup.
  }
  destruct
    (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
      M hPA traversalWitnesses
      (rawStandardPAAxiomWitnessPrefixContextCode M
        appendWitnesses (raw_zero M))
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0))) appendRoot
      (raw_codedPAAxiomWitnessContext_context_realizable M
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          appendWitnesses (raw_zero M))
        (rawStandardPAAxiomWitnessPrefixContextCode M
          appendWitnesses (raw_zero M)) happendWitnessed)
      happend)
    as [transportedAppendRoot htransportedAppend].
  exists (traversalWitnesses ++ appendWitnesses).
  rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
  rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
  split; [exact hfinalWitnessed |].
  exists transportedAppendRoot,
    coqDynamicTruthZeroCanonicalVacuousInheritedTraversalTemplate,
    coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate.
  split.
  - rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
    exact htransportedAppend.
  - split.
    + exact
        coqDynamicTruthZeroCanonicalVacuousInheritedTraversalTemplate_open.
    + exists traversalRoot.
      lazymatch type of holdLookupTemplate with
      | RawCodedPALocalProofOf _ _ _ ?oldLookupRoot =>
          exists oldLookupRoot
      end.
      split.
      * fold finalContext in htraversal.
        rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
        exact htraversal.
      * unfold visibleRowContext in holdLookupTemplate.
        rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
        exact holdLookupTemplate.
Qed.

(** Complete one canonical payload from its sole unresolved coordinate.  The
    append and vacuous inherited branch are compiled first; the generic
    synchronizer then runs the fixed-production compiler on that witnessed
    tail and transports all earlier roots across its helper batch. *)
Theorem
    raw_dynamicTruthZeroCanonicalBottom_permutedAppendRowKernelPayload_on_standardWitnessTail_of_growing_fixed_production :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    rootMode outerPrefix,
  RawDynamicTruthZeroCanonicalGrowingFixedProductionCompilerUnderPrefixAt
    M (rawBottomDirectStructuralTemplateTranslation M hPA)
    rootMode outerPrefix ->
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) /\
    RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
      M (rawBottomDirectStructuralTemplateTranslation M hPA)
      rootMode outerPrefix witnesses.
Proof.
  intros M hPA rootMode outerPrefix hfixedCompiler.
  destruct
    (raw_dynamicTruthZeroCanonicalBottom_permutedAppendInheritedRowResourcesUnderPrefix_on_standardWitnessTail
      M hPA rootMode outerPrefix) as
    (inheritedWitnesses & hinheritedWitnessed & hinheritedResources).
  exact
    (raw_dynamicTruthZeroCanonicalPermutedAppendRowKernelPayload_on_standardWitnessTail_of_inherited_and_growing_fixed_production
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      rootMode outerPrefix inheritedWitnesses
      hinheritedWitnessed hinheritedResources hfixedCompiler).
Qed.

(** The two independent fixed rows are sufficient for the former complete
    independent-payload premise.  Each branch keeps its own witness batch;
    the existing pair adapter performs cross-branch synchronization only when
    the downstream append traversal actually needs a common tail. *)
Theorem
    raw_dynamicTruthZeroCanonicalBottom_independentPermutedAppendRowKernelPayloadsUnderPrefix_of_independent_growing_fixed_productions :
  forall (M : RawPAModel) (hPA : RawPASatisfies M) outerPrefix,
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionCompilersUnderPrefix
    M (rawBottomDirectStructuralTemplateTranslation M hPA) outerPrefix ->
  RawDynamicTruthZeroCanonicalIndependentPermutedAppendRowKernelPayloadsUnderPrefix
    M (rawBottomDirectStructuralTemplateTranslation M hPA) outerPrefix.
Proof.
  intros M hPA outerPrefix [hsigmaFixed hpiFixed].
  split.
  - destruct
      (raw_dynamicTruthZeroCanonicalBottom_permutedAppendRowKernelPayload_on_standardWitnessTail_of_growing_fixed_production
        M hPA 0 outerPrefix hsigmaFixed) as
      (sigmaWitnesses & _ & hsigmaPayload).
    exists sigmaWitnesses. exact hsigmaPayload.
  - destruct
      (raw_dynamicTruthZeroCanonicalBottom_permutedAppendRowKernelPayload_on_standardWitnessTail_of_growing_fixed_production
        M hPA 1 outerPrefix hpiFixed) as
      (piWitnesses & _ & hpiPayload).
    exists piWitnesses. exact hpiPayload.
Qed.

(** Relax the final canonical row boundary once more: either polarity may
    return a direct row proof or a refutation of its exact temporary append
    context.  The source-level adapter inserts represented bottom
    elimination before the existing append/inherited synchronization, so
    no downstream payload type changes. *)
Theorem
    raw_dynamicTruthZeroCanonicalBottom_independentPermutedAppendRowKernelPayloadsUnderPrefix_of_independent_growing_fixed_productions_or_refutations
    : forall (M : RawPAModel) (hPA : RawPASatisfies M) outerPrefix,
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersUnderPrefix
    M (rawBottomDirectStructuralTemplateTranslation M hPA) outerPrefix ->
  RawDynamicTruthZeroCanonicalIndependentPermutedAppendRowKernelPayloadsUnderPrefix
    M (rawBottomDirectStructuralTemplateTranslation M hPA) outerPrefix.
Proof.
  intros M hPA outerPrefix hsources.
  apply
    (raw_dynamicTruthZeroCanonicalBottom_independentPermutedAppendRowKernelPayloadsUnderPrefix_of_independent_growing_fixed_productions
      M hPA outerPrefix).
  exact
    (raw_dynamicTruthZeroCanonicalIndependentGrowingFixedProductionCompilersUnderPrefix_of_production_or_refutation
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      outerPrefix hsources).
Qed.

(** Both arithmetic premises are literal assumptions of the direct
    strong-step endpoint.  When they occur in [callerPrefix], prepend the
    two predecessor-state formulas, compile the assumption leaves with the
    generic strong-step endpoint, and use the exact context-app identity to
    expose the native joint-state shape expected downstream. *)
Theorem
    raw_dynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources_of_template_assumptions
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (translation : RawCodedTemplateTranslation M) callerPrefix,
  In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
    callerPrefix ->
  In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
  RawDynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources
    M hPA translation callerPrefix.
Proof.
  intros M hPA translation callerPrefix hrestrictedIn hruleIn
    tail witnessList baseContext helperRoots
    sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace.
  pose proof
    (rawDynamicTruthNativeLocalZeroNormalized_fields
      M translation witnessList baseContext helperRoots hresources)
    as hfields.
  pose proof
    (rawDynamicTruthNativeLocalZeroCurrentFields_witnessed
      M witnessList baseContext hfields) as hwitnessed.
  destruct
    (raw_dynamicTruthNativeLocalZeroCanonicalBottomEndpointAlignments
      M hPA) as (hlevel & hsigmaDomain & hpiDomain).
  destruct
    (raw_codedPALocalProof_strongStepPredecessor_atomic_and_domain_from_template_assumptions_under_prefix
      M hPA (rawBottomTemplateDirectStructuralInputs M hPA)
      witnessList baseContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ callerPrefix)
      (rawQuotedTermCode M (Term.numeral 0))
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      hwitnessed
      (in_or_app _ _ _ (or_intror hrestrictedIn))
      (in_or_app _ _ _ (or_intror hruleIn))
      hlevel hsigmaDomain hpiDomain)
    as (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      hendpointWitnessed & hbaseEndpointIncluded & hatomic & hdomain).
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      endpointContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ callerPrefix))
    (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot) in hatomic.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      endpointContext
      (coqDynamicTruthPredecessorStateTemplateContext ++ callerPrefix))
    (rawFormulaOrCode M
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)) domainRoot) in hdomain.
  rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
    M (rawBottomDirectStructuralTemplateTranslation M hPA)
    (rawBottomDirectStructuralTemplatePAAgreement M hPA)
    endpointContext callerPrefix) in hatomic, hdomain.
  exists endpointWitnessList, endpointContext, atomicRoot, domainRoot.
  split; [exact hendpointWitnessed |].
  split; [exact hbaseEndpointIncluded |].
  split; assumption.
Qed.

(** Consume the normalized decision projection on the arithmetic endpoint's
    witnessed extension.  The endpoint and local-field projection are
    intentionally synchronized here rather than in their producer: this
    keeps the endpoint interface independent of local truth totality and
    permits both components to choose their natural source contexts. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingEvidenceDecisionCompilerUnderCallerPrefixOnCanonicalNormalizedResources_of_endpoint :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (translation : RawCodedTemplateTranslation M) callerPrefix,
  RawDynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources
    M hPA translation callerPrefix ->
  RawDynamicTruthNativeLocalZeroGrowingEvidenceDecisionCompilerUnderCallerPrefixOnCanonicalNormalizedResources
    M hPA translation callerPrefix.
Proof.
  intros M hPA translation callerPrefix hendpoint
    tail witnessList baseContext helperRoots
    sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace.
  pose proof
    (rawDynamicTruthNativeLocalZeroNormalized_fields
      M translation witnessList baseContext helperRoots hresources)
    as hfields.
  pose proof
    (rawDynamicTruthNativeLocalZeroCurrentFields_witnessed
      M witnessList baseContext hfields) as hbaseWitnessed.
  destruct
    (rawDynamicTruthNativeLocalZeroNormalized_localProjections
      M translation witnessList baseContext helperRoots hresources)
    as [sourceRoot hprojected].
  destruct hprojected as [hdecisionProjection _hexclusiveProjection].
  destruct
    (hendpoint tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      hendpointWitnessed & hbaseEndpointIncluded & hatomic & hdomain).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      witnessList baseContext endpointWitnessList endpointContext []
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalDecisionCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M)
          (rawDynamicTruthZeroSigmaEvidenceCode M)
          (rawDynamicTruthZeroPiEvidenceCode M)))
      (rawDynamicTruthLocalDecisionProjectionRoot M baseContext
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)
        (rawDynamicTruthZeroSigmaEvidenceCode M)
        (rawDynamicTruthZeroPiEvidenceCode M) sourceRoot)
      hbaseWitnessed hendpointWitnessed hbaseEndpointIncluded
      hdecisionProjection)
    as [endpointDecisionRoot hendpointDecision].
  cbn [rawTemplateContextCodeOnTail] in hendpointDecision.
  destruct
    (raw_dynamicTruthZeroLocalExclusiveTemplateIdentification_exists M hPA)
    as [inputs hidentification].
  pose proof
    (rawCoqDynamicTruthLocalDecisionEliminationChain_identified
      M hPA inputs
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      (rawDynamicTruthZeroSigmaEvidenceCode M)
      (rawDynamicTruthZeroPiEvidenceCode M)
      hidentification) as hdecisionChain.
  destruct
    (raw_dynamicTruthPredecessorEvidenceDecision_of_projected_decision_under_prefix_atomic_and_domain
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      endpointWitnessList endpointContext callerPrefix
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      (rawDynamicTruthZeroSigmaEvidenceCode M)
      (rawDynamicTruthZeroPiEvidenceCode M)
      endpointDecisionRoot atomicRoot domainRoot
      (raw_directStructuralTemplatePrefix_atomically_adequate M hPA
        (rawBottomTemplateDirectStructuralInputs M hPA)
        (coqDynamicTruthPredecessorStateTemplateContext ++ callerPrefix))
      hendpointWitnessed hdecisionChain hendpointDecision hatomic hdomain)
    as (targetWitnessList & targetContext & decisionRoot &
      htargetWitnessed & hendpointTargetIncluded & hdecision).
  exists targetWitnessList, targetContext, decisionRoot.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hendpointTargetIncluded member
      (hbaseEndpointIncluded member hmember)).
  - exact hdecision.
Qed.

(** Canonical rank-zero clients need only produce the two genuinely logical
    roots.  The bottom structural interpretation fixes the lower parameter
    to numeral zero, and the standard zero-domain substitutions discharge
    all three structural alignment obligations from the preceding generic
    interface. *)
Definition
    RawDynamicTruthNativeLocalZeroCanonicalRestrictedRuleRootsCompilerOnCanonicalNormalizedResources
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists restrictedRoot ruleRoot : M,
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M baseContext)
        (rawDirectTemplateFormula
          (rawBottomTemplateDirectStructuralInputs M hPA)
          coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
        restrictedRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M baseContext)
        (rawDirectTemplateFormula
          (rawBottomTemplateDirectStructuralInputs M hPA)
          coqStrongStepProofEndpointAtomicAdequacyRulePremise)
        ruleRoot.

Arguments
  RawDynamicTruthNativeLocalZeroCanonicalRestrictedRuleRootsCompilerOnCanonicalNormalizedResources
  M hPA translation : clear implicits.

(** Proof-producing rule analysis may append standard PA axioms before both
    roots become available.  This is the natural residual boundary: it keeps
    the two roots synchronized on one witnessed extension and records only
    inclusion of the incoming tail. *)
Definition
    RawDynamicTruthNativeLocalZeroCanonicalGrowingRestrictedRuleRootsCompilerOnCanonicalNormalizedResources
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists rootWitnessList rootContext restrictedRoot ruleRoot : M,
      RawCodedPAAxiomWitnessContext M rootWitnessList rootContext /\
      RawContextListIncluded M baseContext rootContext /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M rootContext)
        (rawDirectTemplateFormula
          (rawBottomTemplateDirectStructuralInputs M hPA)
          coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
        restrictedRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M rootContext)
        (rawDirectTemplateFormula
          (rawBottomTemplateDirectStructuralInputs M hPA)
          coqStrongStepProofEndpointAtomicAdequacyRulePremise)
        ruleRoot.

Arguments
  RawDynamicTruthNativeLocalZeroCanonicalGrowingRestrictedRuleRootsCompilerOnCanonicalNormalizedResources
  M hPA translation : clear implicits.

(** The two proof analyses are independent and may append different standard
    PA prefixes.  Each result preserves the predecessor-state assumptions;
    synchronization is an internal consumer responsibility rather than a
    producer-side equality constraint on chosen tails. *)
Definition
    RawDynamicTruthNativeLocalZeroCanonicalIndependentGrowingRestrictedRuleRootCompilersOnCanonicalNormalizedResources
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    RawCodedPAGrowingTemplateLocalProofAt M
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      witnessList baseContext
      coqDynamicTruthPredecessorStateTemplateContext
      (rawDirectTemplateFormula
        (rawBottomTemplateDirectStructuralInputs M hPA)
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate) /\
    RawCodedPAGrowingTemplateLocalProofAt M
      (rawBottomDirectStructuralTemplateTranslation M hPA)
      witnessList baseContext
      coqDynamicTruthPredecessorStateTemplateContext
      (rawDirectTemplateFormula
        (rawBottomTemplateDirectStructuralInputs M hPA)
        coqStrongStepProofEndpointAtomicAdequacyRulePremise).

Arguments
  RawDynamicTruthNativeLocalZeroCanonicalIndependentGrowingRestrictedRuleRootCompilersOnCanonicalNormalizedResources
  M hPA translation : clear implicits.

(** Merge the independently selected witnessed tails while retaining the
    shared predecessor-state prefix verbatim. *)
Theorem
    raw_dynamicTruthNativeLocalZeroCanonicalGrowingRestrictedRuleRootsCompilerOnCanonicalNormalizedResources_of_independent
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroCanonicalIndependentGrowingRestrictedRuleRootCompilersOnCanonicalNormalizedResources
    M hPA translation ->
  RawDynamicTruthNativeLocalZeroCanonicalGrowingRestrictedRuleRootsCompilerOnCanonicalNormalizedResources
    M hPA translation.
Proof.
  intros M hPA translation hcompilers tail witnessList baseContext
    helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompilers tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (hrestricted & hrule).
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_pair_at_prefix
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      witnessList baseContext
      coqDynamicTruthPredecessorStateTemplateContext
      (rawDirectTemplateFormula
        (rawBottomTemplateDirectStructuralInputs M hPA)
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
      (rawDirectTemplateFormula
        (rawBottomTemplateDirectStructuralInputs M hPA)
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)
      hrestricted hrule) as hpair.
  destruct hpair as
    (rootWitnessList & rootContext & restrictedRoot & ruleRoot &
      hrootWitnessed & hbaseRootIncluded & hrestrictedRoot & hruleRoot).
  rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
    M (rawBottomDirectStructuralTemplateTranslation M hPA)
    (rawBottomDirectStructuralTemplatePAAgreement M hPA)
    rootContext) in hrestrictedRoot, hruleRoot.
  exists rootWitnessList, rootContext, restrictedRoot, ruleRoot.
  split; [exact hrootWitnessed |].
  split; [exact hbaseRootIncluded |].
  split; assumption.
Qed.

(** Exact-tail production remains a sufficient compatibility interface. *)
Theorem
    raw_dynamicTruthNativeLocalZeroCanonicalGrowingRestrictedRuleRootsCompilerOnCanonicalNormalizedResources_of_fixed
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroCanonicalRestrictedRuleRootsCompilerOnCanonicalNormalizedResources
    M hPA translation ->
  RawDynamicTruthNativeLocalZeroCanonicalGrowingRestrictedRuleRootsCompilerOnCanonicalNormalizedResources
    M hPA translation.
Proof.
  intros M hPA translation hcompiler tail witnessList baseContext
    helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (restrictedRoot & ruleRoot & hrestricted & hrule).
  pose proof
    (rawDynamicTruthNativeLocalZeroNormalized_fields
      M translation witnessList baseContext helperRoots hresources)
    as hfields.
  pose proof
    (rawDynamicTruthNativeLocalZeroCurrentFields_witnessed
      M witnessList baseContext hfields) as hwitnessed.
  exists witnessList, baseContext, restrictedRoot, ruleRoot.
  split; [exact hwitnessed |].
  split.
  - intros member hmember. exact hmember.
  - split; assumption.
Qed.

Theorem
    raw_dynamicTruthNativeLocalZeroCanonicalRestrictedRuleEndpointInputsCompilerOnCanonicalNormalizedResources_of_roots
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroCanonicalRestrictedRuleRootsCompilerOnCanonicalNormalizedResources
    M hPA translation ->
  RawDynamicTruthNativeLocalZeroCanonicalRestrictedRuleEndpointInputsCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hcompiler tail witnessList baseContext
    helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (restrictedRoot & ruleRoot & hrestricted & hrule).
  destruct
    (raw_dynamicTruthNativeLocalZeroCanonicalBottomEndpointAlignments
      M hPA) as (hlevel & hsigmaDomain & hpiDomain).
  exists (rawBottomTemplateDirectStructuralInputs M hPA),
    (rawQuotedTermCode M (Term.numeral 0)), restrictedRoot, ruleRoot.
  split; [exact hlevel |].
  split; [exact hsigmaDomain |].
  split; [exact hpiDomain |].
  split; assumption.
Qed.

(** Compile the primitive restricted/rule pair into one synchronized
    arithmetic endpoint.  The witnessed source context is recovered from the
    normalized field package; every PA-law proof, prefix insertion, and
    context-growth step is delegated to the reusable strong-step compiler. *)
Theorem
    raw_dynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerOnCanonicalNormalizedResources_of_restricted_rule_inputs
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroCanonicalRestrictedRuleEndpointInputsCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hcompiler tail witnessList baseContext
    helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (inputs & levelNumeral & restrictedRoot & ruleRoot &
      hlevel & hsigmaDomain & hpiDomain & hrestricted & hrule).
  pose proof
    (rawDynamicTruthNativeLocalZeroNormalized_fields
      M translation witnessList baseContext helperRoots hresources)
    as hfields.
  pose proof
    (rawDynamicTruthNativeLocalZeroCurrentFields_witnessed
      M witnessList baseContext hfields) as hwitnessed.
  exact
    (raw_codedPALocalProof_strongStepPredecessor_atomic_and_domain_of_restricted_and_rule_roots_under_predecessor_state
      M hPA inputs witnessList baseContext levelNumeral
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      restrictedRoot ruleRoot hwitnessed
      hlevel hsigmaDomain hpiDomain hrestricted hrule).
Qed.

(** Canonical root production is sufficient for the synchronized endpoint;
    structural inputs and both zero-domain traces are reconstructed rather
    than exposed to the dependency-ordered client. *)
Theorem
    raw_dynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerOnCanonicalNormalizedResources_of_restricted_rule_roots
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroCanonicalRestrictedRuleRootsCompilerOnCanonicalNormalizedResources
    M hPA translation ->
  RawDynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hroots.
  exact
    (raw_dynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerOnCanonicalNormalizedResources_of_restricted_rule_inputs
      M hPA translation
      (raw_dynamicTruthNativeLocalZeroCanonicalRestrictedRuleEndpointInputsCompilerOnCanonicalNormalizedResources_of_roots
        M hPA translation hroots)).
Qed.

(** The preferred canonical endpoint accepts the two logical roots on any
    synchronized witnessed extension.  The generic extension-aware strong-
    step lemma composes that growth with the endpoint law's own PA prefix. *)
Theorem
    raw_dynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerOnCanonicalNormalizedResources_of_growing_restricted_rule_roots
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroCanonicalGrowingRestrictedRuleRootsCompilerOnCanonicalNormalizedResources
    M hPA translation ->
  RawDynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hcompiler tail witnessList baseContext
    helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (rootWitnessList & rootContext & restrictedRoot & ruleRoot &
      hrootWitnessed & hbaseRootIncluded & hrestricted & hrule).
  destruct
    (raw_dynamicTruthNativeLocalZeroCanonicalBottomEndpointAlignments
      M hPA) as (hlevel & hsigmaDomain & hpiDomain).
  exact
    (raw_codedPALocalProof_strongStepPredecessor_atomic_and_domain_of_restricted_and_rule_roots_under_predecessor_state_on_witnessed_extension_from
      M hPA (rawBottomTemplateDirectStructuralInputs M hPA)
      baseContext rootWitnessList rootContext
      (rawQuotedTermCode M (Term.numeral 0))
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      restrictedRoot ruleRoot hrootWitnessed hbaseRootIncluded
      hlevel hsigmaDomain hpiDomain hrestricted hrule).
Qed.

(** Independent root producers suffice for the complete endpoint; their
    witnessed tails are synchronized before the endpoint law adds its own
    standard PA prefix. *)
Theorem
    raw_dynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerOnCanonicalNormalizedResources_of_independent_growing_restricted_rule_roots
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroCanonicalIndependentGrowingRestrictedRuleRootCompilersOnCanonicalNormalizedResources
    M hPA translation ->
  RawDynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hroots.
  exact
    (raw_dynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerOnCanonicalNormalizedResources_of_growing_restricted_rule_roots
      M hPA translation
      (raw_dynamicTruthNativeLocalZeroCanonicalGrowingRestrictedRuleRootsCompilerOnCanonicalNormalizedResources_of_independent
        M hPA translation hroots)).
Qed.

(** Merge independently selected atomic and domain witnessed tails.  The
    shared predecessor-state prefix is transported verbatim by the generic
    growing-pair constructor, so the result has exactly the endpoint shape
    consumed by canonical application compilation. *)
Theorem
    raw_dynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerOnCanonicalNormalizedResources_of_atomic_and_domain
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroCanonicalAtomicEndpointCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroCanonicalDomainEndpointCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hagreement hatomicCompiler hdomainCompiler
    tail witnessList baseContext helperRoots
    sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_pair_at_prefix
      M hPA translation witnessList baseContext
      coqDynamicTruthPredecessorStateTemplateContext
      (rawDynamicTruthLocalAtomicAdequacyCode M)
      (rawFormulaOrCode M
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M))
      (hatomicCompiler tail witnessList baseContext helperRoots
        sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
      (hdomainCompiler tail witnessList baseContext helperRoots
        sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace))
    as hpair.
  destruct hpair as
    (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      hendpointWitnessed & hbaseEndpointIncluded & hatomic & hdomain).
  exists endpointWitnessList, endpointContext, atomicRoot, domainRoot.
  split; [exact hendpointWitnessed |].
  split; [exact hbaseEndpointIncluded |].
  rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
    M translation hagreement endpointContext) in hatomic, hdomain.
  split; assumption.
Qed.

(** Kernel-facing form of the synchronized canonical append residual.  The
    arithmetic endpoint is unchanged, but each polarity supplies only the
    append root, inherited traversal/lookup roots, and fixed mode production
    needed by the generic row compiler.  Keeping one shared standard helper
    batch records that the two growing applications start from the same
    witnessed PA tail. *)
Definition
    RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendKernelResourcesCompilerOnCanonicalNormalizedResources
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists endpointWitnessList endpointContext atomicRoot domainRoot,
    exists appendWitnesses : StandardPAAxiomWitnessPrefix,
      RawCodedPAAxiomWitnessContext M endpointWitnessList endpointContext /\
      RawContextListIncluded M baseContext endpointContext /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M endpointContext)
        (rawFormulaOrCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M)) domainRoot /\
      RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
        M translation 0 coqDynamicTruthPredecessorStateTemplateContext
          appendWitnesses /\
      RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
        M translation 1 coqDynamicTruthPredecessorStateTemplateContext
          appendWitnesses.

Arguments
  RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendKernelResourcesCompilerOnCanonicalNormalizedResources
  M translation : clear implicits.

(** Row-kernel resources under the caller assumptions of the direct
    strong-step shell.  Arithmetic roots and both append payloads share the
    exact combined prefix [state ++ callerPrefix]; no contraction back to
    the state-only context is requested. *)
Definition
    RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendKernelResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M)
    (callerPrefix : TemplateContext) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists endpointWitnessList endpointContext atomicRoot domainRoot,
    exists appendWitnesses : StandardPAAxiomWitnessPrefix,
      RawCodedPAAxiomWitnessContext M endpointWitnessList endpointContext /\
      RawContextListIncluded M baseContext endpointContext /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M
          (rawTemplateContextCodeOnTail
            (rawBottomDirectStructuralTemplateTranslation M hPA)
            endpointContext callerPrefix))
        (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot /\
      RawCodedPALocalProofOf M
        (rawDynamicTruthPredecessorJointStateContext M
          (rawTemplateContextCodeOnTail
            (rawBottomDirectStructuralTemplateTranslation M hPA)
            endpointContext callerPrefix))
        (rawFormulaOrCode M
          (rawDynamicTruthZeroSigmaDomainCode M)
          (rawDynamicTruthZeroPiDomainCode M)) domainRoot /\
      RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
        M translation 0
          (coqDynamicTruthPredecessorStateTemplateContext ++ callerPrefix)
          appendWitnesses /\
      RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadUnderPrefixAt
        M translation 1
          (coqDynamicTruthPredecessorStateTemplateContext ++ callerPrefix)
          appendWitnesses.

Arguments
  RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendKernelResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources
  M hPA translation callerPrefix : clear implicits.

(** Product reassociation at the retained caller prefix. *)
Theorem
    raw_dynamicTruthNativeLocalZeroCanonicalPermutedAppendKernelResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources_of_endpoint_and_payload_pair
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (translation : RawCodedTemplateTranslation M) callerPrefix,
  RawDynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources
    M hPA translation callerPrefix ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadPairUnderPrefix
    M translation
      (coqDynamicTruthPredecessorStateTemplateContext ++ callerPrefix) ->
  RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendKernelResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources
    M hPA translation callerPrefix.
Proof.
  intros M hPA translation callerPrefix hendpoint hpayloads
    tail witnessList baseContext helperRoots
    sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace.
  destruct
    (hendpoint tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      hendpointWitnessed & hbaseEndpointIncluded & hatomic & hdomain).
  destruct hpayloads as (appendWitnesses & hsigmaPayload & hpiPayload).
  exists endpointWitnessList, endpointContext, atomicRoot, domainRoot,
    appendWitnesses.
  split; [exact hendpointWitnessed |].
  split; [exact hbaseEndpointIncluded |].
  split; [exact hatomic |].
  split; [exact hdomain |].
  split; assumption.
Qed.

(** Canonical rank-zero kernel resources need no restricted/rule root
    producer once the direct-shell assumptions are retained. *)
Corollary
    raw_dynamicTruthNativeLocalZeroCanonicalPermutedAppendKernelResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources_of_template_assumptions_and_payload_pair
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (translation : RawCodedTemplateTranslation M) callerPrefix,
  In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
    callerPrefix ->
  In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadPairUnderPrefix
    M translation
      (coqDynamicTruthPredecessorStateTemplateContext ++ callerPrefix) ->
  RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendKernelResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources
    M hPA translation callerPrefix.
Proof.
  intros M hPA translation callerPrefix hrestrictedIn hruleIn hpayloads.
  exact
    (raw_dynamicTruthNativeLocalZeroCanonicalPermutedAppendKernelResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources_of_endpoint_and_payload_pair
      M hPA translation callerPrefix
      (raw_dynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources_of_template_assumptions
        M hPA translation callerPrefix hrestrictedIn hruleIn)
      hpayloads).
Qed.

(** Compile prefix-aware row kernels to the synchronized canonical
    application pair without changing or contracting the combined prefix. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources_of_permuted_append_kernel_resources
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall callerPrefix,
  RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendKernelResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources
    M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      callerPrefix ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources
    M hPA callerPrefix.
Proof.
  intros M hPA callerPrefix hcompiler
    tail witnessList baseContext helperRoots
    sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      appendWitnesses & hendpointWitnessed & hbaseEndpointIncluded &
      hatomic & hdomain & hsigmaPayload & hpiPayload).
  set (combinedPrefix :=
    coqDynamicTruthPredecessorStateTemplateContext ++ callerPrefix).
  pose proof
    (raw_dynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt_of_kernel
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      (rawBottomDirectStructuralTemplatePAAgreement M hPA) 0
      combinedPrefix appendWitnesses
      (raw_dynamicTruthZeroCanonicalSigmaPermutedAppendRowKernelInputsUnderPrefixAt_of_payload
        M (rawBottomDirectStructuralTemplateTranslation M hPA)
        combinedPrefix appendWitnesses hsigmaPayload))
    as hsigmaRows.
  pose proof
    (raw_dynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt_of_kernel
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      (rawBottomDirectStructuralTemplatePAAgreement M hPA) 1
      combinedPrefix appendWitnesses
      (raw_dynamicTruthZeroCanonicalPiPermutedAppendRowKernelInputsUnderPrefixAt_of_payload
        M (rawBottomDirectStructuralTemplateTranslation M hPA)
        combinedPrefix appendWitnesses hpiPayload))
    as hpiRows.
  pose proof
    (raw_dynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt_of_row_implication_inputs
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA) 0
      combinedPrefix appendWitnesses hsigmaRows) as hsigmaInputs.
  pose proof
    (raw_dynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt_of_row_implication_inputs
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA) 1
      combinedPrefix appendWitnesses hpiRows) as hpiInputs.
  exists endpointWitnessList, endpointContext, atomicRoot, domainRoot.
  split; [exact hendpointWitnessed |].
  split; [exact hbaseEndpointIncluded |].
  split; [exact hatomic |].
  split; [exact hdomain |].
  exact
    (raw_dynamicTruthZeroCanonicalApplicationPair_of_permuted_append_inputs_under_prefix
      M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
      (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      combinedPrefix appendWitnesses endpointWitnessList endpointContext
      (raw_directStructuralTemplatePrefix_atomically_adequate M hPA
        (rawBottomTemplateDirectStructuralInputs M hPA) combinedPrefix)
      hendpointWitnessed hsigmaInputs hpiInputs).
Qed.

(** Convert the synchronized canonical applications to the fixed native
    evidence pair, transport the arithmetic leaves through the same witness
    extension, and invoke prefix-general admissibility.  This is the first
    complete rank-zero logical-root compiler which never contracts the
    direct-shell assumptions. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerUnderCallerPrefixOnCanonicalNormalizedResources_of_state_application_resources
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall callerPrefix,
  RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources
    M hPA callerPrefix ->
  RawDynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerUnderCallerPrefixOnCanonicalNormalizedResources
    M hPA callerPrefix.
Proof.
  intros M hPA callerPrefix hcompiler
    tail witnessList baseContext helperRoots
    sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace.
  set (translation := rawBottomDirectStructuralTemplateTranslation M hPA).
  set (combinedPrefix :=
    coqDynamicTruthPredecessorStateTemplateContext ++ callerPrefix).
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      hendpointWitnessed & hbaseEndpointIncluded & hatomic & hdomain &
      applicationWitnessList & applicationContext &
      sigmaApplicationRoot & piApplicationRoot &
      happlicationWitnessed & hendpointApplicationIncluded &
      hsigmaApplication & hpiApplication).
  assert (hatomicCombined : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation endpointContext
        combinedPrefix)
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot).
  {
    unfold combinedPrefix, translation.
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M (rawBottomDirectStructuralTemplateTranslation M hPA)
      (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      endpointContext callerPrefix).
    exact hatomic.
  }
  assert (hdomainCombined : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation endpointContext
        combinedPrefix)
      (rawFormulaOrCode M
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)) domainRoot).
  {
    unfold combinedPrefix, translation.
    rewrite (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M (rawBottomDirectStructuralTemplateTranslation M hPA)
      (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      endpointContext callerPrefix).
    exact hdomain.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation endpointWitnessList endpointContext
      applicationWitnessList applicationContext combinedPrefix
      (rawDynamicTruthLocalAtomicAdequacyCode M) atomicRoot
      hendpointWitnessed happlicationWitnessed
      hendpointApplicationIncluded hatomicCombined)
    as [applicationAtomicRoot happlicationAtomic].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation endpointWitnessList endpointContext
      applicationWitnessList applicationContext combinedPrefix
      (rawFormulaOrCode M
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)) domainRoot
      hendpointWitnessed happlicationWitnessed
      hendpointApplicationIncluded hdomainCombined)
    as [applicationDomainRoot happlicationDomain].
  destruct
    (raw_dynamicTruthZeroNativeEvidenceRoots_of_canonicalApplicationRoots_under_prefix
      M hPA translation (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      applicationWitnessList applicationContext combinedPrefix
      sigmaApplicationRoot piApplicationRoot
      (raw_directStructuralTemplatePrefix_atomically_adequate M hPA
        (rawBottomTemplateDirectStructuralInputs M hPA) combinedPrefix)
      happlicationWitnessed hsigmaApplication hpiApplication)
    as (evidenceWitnessList & evidenceContext &
      sigmaEvidenceRoot & piEvidenceRoot & hevidenceWitnessed &
      happlicationEvidenceIncluded & hsigmaEvidenceCombined &
      hpiEvidenceCombined).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation applicationWitnessList applicationContext
      evidenceWitnessList evidenceContext combinedPrefix
      (rawDynamicTruthLocalAtomicAdequacyCode M) applicationAtomicRoot
      happlicationWitnessed hevidenceWitnessed
      happlicationEvidenceIncluded happlicationAtomic)
    as [evidenceAtomicRoot hevidenceAtomicCombined].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation applicationWitnessList applicationContext
      evidenceWitnessList evidenceContext combinedPrefix
      (rawFormulaOrCode M
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)) applicationDomainRoot
      happlicationWitnessed hevidenceWitnessed
      happlicationEvidenceIncluded happlicationDomain)
    as [evidenceDomainRoot hevidenceDomainCombined].
  assert (hevidenceAtomic : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation evidenceContext
          callerPrefix))
      (rawDynamicTruthLocalAtomicAdequacyCode M) evidenceAtomicRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      evidenceContext callerPrefix).
    exact hevidenceAtomicCombined.
  }
  assert (hevidenceDomain : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation evidenceContext
          callerPrefix))
      (rawFormulaOrCode M
        (rawDynamicTruthZeroSigmaDomainCode M)
        (rawDynamicTruthZeroPiDomainCode M)) evidenceDomainRoot).
  {
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      evidenceContext callerPrefix).
    exact hevidenceDomainCombined.
  }
  assert (hsigmaEvidence : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation evidenceContext
          callerPrefix))
      (rawDynamicTruthZeroSigmaEvidenceCode M) sigmaEvidenceRoot).
  {
    unfold rawDynamicTruthZeroSigmaEvidenceCode.
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      evidenceContext callerPrefix).
    exact hsigmaEvidenceCombined.
  }
  assert (hpiEvidence : RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M
        (rawTemplateContextCodeOnTail translation evidenceContext
          callerPrefix))
      (rawDynamicTruthZeroPiEvidenceCode M) piEvidenceRoot).
  {
    unfold rawDynamicTruthZeroPiEvidenceCode.
    rewrite <- (raw_dynamicTruthPredecessorStateTemplateContext_app_code
      M translation (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      evidenceContext callerPrefix).
    exact hpiEvidenceCombined.
  }
  destruct
    (raw_dynamicTruthPredecessorStateLogicalRootsAt_of_direct_evidence_under_prefix_atomic_and_domain
      M hPA translation (rawBottomDirectStructuralTemplatePAAgreement M hPA)
      evidenceWitnessList evidenceContext callerPrefix
      (rawDynamicTruthZeroSigmaDomainCode M)
      (rawDynamicTruthZeroPiDomainCode M)
      (rawDynamicTruthZeroSigmaEvidenceCode M)
      (rawDynamicTruthZeroPiEvidenceCode M)
      evidenceAtomicRoot evidenceDomainRoot sigmaEvidenceRoot piEvidenceRoot
      (raw_directStructuralTemplatePrefix_atomically_adequate M hPA
        (rawBottomTemplateDirectStructuralInputs M hPA) callerPrefix)
      hevidenceWitnessed hevidenceAtomic hevidenceDomain
      hsigmaEvidence hpiEvidence)
    as (targetWitnessList & targetContext & htargetWitnessed &
      hevidenceTargetIncluded & hlogicalRoots).
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hevidenceTargetIncluded member
      (happlicationEvidenceIncluded member
        (hendpointApplicationIncluded member
          (hbaseEndpointIncluded member hmember)))).
  - exact hlogicalRoots.
Qed.

(** End-to-end retained-assumption rank-zero closure.  The former pair of
    independently growing restricted/rule root compilers is absent: those
    roots are assumption leaves, while the synchronized append payload pair
    remains the sole proof-producing traversal resource. *)
Corollary
    raw_dynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerUnderCallerPrefixOnCanonicalNormalizedResources_of_template_assumptions_and_payload_pair
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall callerPrefix,
  In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
    callerPrefix ->
  In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadPairUnderPrefix
    M (rawBottomDirectStructuralTemplateTranslation M hPA)
      (coqDynamicTruthPredecessorStateTemplateContext ++ callerPrefix) ->
  RawDynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerUnderCallerPrefixOnCanonicalNormalizedResources
    M hPA callerPrefix.
Proof.
  intros M hPA callerPrefix hrestrictedIn hruleIn hpayloads.
  exact
    (raw_dynamicTruthNativeLocalZeroGrowingLogicalRootsCompilerUnderCallerPrefixOnCanonicalNormalizedResources_of_state_application_resources
      M hPA callerPrefix
      (raw_dynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources_of_permuted_append_kernel_resources
        M hPA callerPrefix
        (raw_dynamicTruthNativeLocalZeroCanonicalPermutedAppendKernelResourcesCompilerUnderCallerPrefixOnCanonicalNormalizedResources_of_template_assumptions_and_payload_pair
          M hPA (rawBottomDirectStructuralTemplateTranslation M hPA)
          callerPrefix hrestrictedIn hruleIn hpayloads))).
Qed.

(** Combine the invocation-dependent endpoint with the model-global,
    synchronized canonical row payloads.  This is only product reassociation:
    no represented proof code or witnessed context is changed. *)
Theorem
    raw_dynamicTruthNativeLocalZeroCanonicalPermutedAppendKernelResourcesCompilerOnCanonicalNormalizedResources_of_endpoint_and_payload_pair
    : forall (M : RawPAModel)
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeLocalZeroCanonicalEndpointResourcesCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthZeroCanonicalPermutedAppendRowKernelPayloadPairUnderPrefix
    M translation coqDynamicTruthPredecessorStateTemplateContext ->
  RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendKernelResourcesCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M translation hendpoint hpayloads tail witnessList baseContext
    helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hendpoint tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      hendpointWitnessed & hbaseEndpointIncluded & hatomic & hdomain).
  destruct hpayloads as (appendWitnesses & hsigmaPayload & hpiPayload).
  exists endpointWitnessList, endpointContext, atomicRoot, domainRoot,
    appendWitnesses.
  split; [exact hendpointWitnessed |].
  split; [exact hbaseEndpointIncluded |].
  split; [exact hatomic |].
  split; [exact hdomain |].
  split; assumption.
Qed.

(** Compile both synchronized kernel packages to the row-implication
    interface.  All endpoint witnesses and roots are preserved verbatim; the
    only constructed objects are the two represented arithmetic case splits
    and their implication introductions. *)
Theorem
    raw_dynamicTruthNativeLocalZeroCanonicalPermutedAppendInputResourcesCompilerOnCanonicalNormalizedResources_of_kernel_resources
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendKernelResourcesCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendInputResourcesCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hagreement hcompiler tail witnessList
    baseContext helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      appendWitnesses & hendpointWitnessed & hbaseEndpointIncluded &
      hatomic & hdomain & hsigmaKernel & hpiKernel).
  exists endpointWitnessList, endpointContext, atomicRoot, domainRoot,
    appendWitnesses.
  split; [exact hendpointWitnessed |].
  split; [exact hbaseEndpointIncluded |].
  split; [exact hatomic |].
  split; [exact hdomain |].
  split.
  - exact
      (raw_dynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt_of_kernel
        M hPA translation hagreement 0
        coqDynamicTruthPredecessorStateTemplateContext appendWitnesses
        (raw_dynamicTruthZeroCanonicalSigmaPermutedAppendRowKernelInputsUnderPrefixAt_of_payload
          M translation coqDynamicTruthPredecessorStateTemplateContext
          appendWitnesses hsigmaKernel)).
  - exact
      (raw_dynamicTruthZeroCanonicalPermutedAppendRowImplicationInputsUnderPrefixAt_of_kernel
        M hPA translation hagreement 1
        coqDynamicTruthPredecessorStateTemplateContext appendWitnesses
        (raw_dynamicTruthZeroCanonicalPiPermutedAppendRowKernelInputsUnderPrefixAt_of_payload
          M translation coqDynamicTruthPredecessorStateTemplateContext
          appendWitnesses hpiKernel)).
Qed.

(** Compile the concrete synchronized row-implication packages into the abstract
    state-application resource interface used by the existing normalized
    callback.  No represented proof is moved back to the normalized base:
    the arithmetic endpoint is retained as the source of the growing pair,
    and append traversal may extend it further. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources_of_permuted_append_input_resources
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendInputResourcesCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hagreement hcompiler tail witnessList
    baseContext helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      appendWitnesses & hendpointWitnessed & hbaseEndpointIncluded &
      hatomic & hdomain & hsigmaRows & hpiRows).
  pose proof
    (raw_dynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt_of_row_implication_inputs
      M hPA translation 0 coqDynamicTruthPredecessorStateTemplateContext
      appendWitnesses hsigmaRows) as hsigmaInputs.
  pose proof
    (raw_dynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt_of_row_implication_inputs
      M hPA translation 1 coqDynamicTruthPredecessorStateTemplateContext
      appendWitnesses hpiRows) as hpiInputs.
  exists endpointWitnessList, endpointContext, atomicRoot, domainRoot.
  split; [exact hendpointWitnessed |].
  split; [exact hbaseEndpointIncluded |].
  split; [exact hatomic |].
  split; [exact hdomain |].
  exact
    (raw_dynamicTruthZeroCanonicalStateApplicationPair_of_permuted_append_inputs
      M hPA translation hagreement appendWitnesses
      endpointWitnessList endpointContext hendpointWitnessed
      hsigmaInputs hpiInputs).
Qed.

(** Direct kernel-to-application adapter used by dependency-ordered callback
    assembly.  Factoring this composition here keeps the synchronized
    two-polarity traversal argument out of every higher-level bundle. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources_of_permuted_append_kernel_resources
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroCanonicalPermutedAppendKernelResourcesCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hagreement hcompiler.
  exact
    (raw_dynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources_of_permuted_append_input_resources
      M hPA translation hagreement
      (raw_dynamicTruthNativeLocalZeroCanonicalPermutedAppendInputResourcesCompilerOnCanonicalNormalizedResources_of_kernel_resources
        M hPA translation hagreement hcompiler)).
Qed.

(** Interpret the shared template prefix as the literal joint state context.
    The growing pair already records the final witnessed tail and inclusion,
    so no post-hoc assumption insertion occurs. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources_of_state_application_resources
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hagreement hcompiler tail witnessList
    baseContext helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      hendpointWitnessed & hbaseEndpointIncluded & hatomic & hdomain &
      applicationWitnessList & applicationContext &
      sigmaApplicationRoot & piApplicationRoot &
      happlicationWitnessed & hendpointApplicationIncluded &
      hsigmaApplication & hpiApplication).
  rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
    M translation hagreement applicationContext) in
    hsigmaApplication, hpiApplication.
  exists endpointWitnessList, endpointContext, atomicRoot, domainRoot.
  split; [exact hendpointWitnessed |].
  split; [exact hbaseEndpointIncluded |].
  split; [exact hatomic |].
  split; [exact hdomain |].
  exists applicationWitnessList, applicationContext.
  split; [exact happlicationWitnessed |].
  split; [exact hendpointApplicationIncluded |].
  constructor.
  - exists sigmaApplicationRoot. exact hsigmaApplication.
  - exists piApplicationRoot. exact hpiApplication.
Qed.

(** Conversely, expose any concrete joint-state global-root package through
    the structurally named state prefix.  Thus the append-facing form is an
    exact reformulation, not an additional compiler assumption. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources_of_global_application_resources
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M _hPA translation hagreement hcompiler tail witnessList
    baseContext helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      hendpointWitnessed & hbaseEndpointIncluded & hatomic & hdomain &
      applicationWitnessList & applicationContext &
      happlicationWitnessed & hendpointApplicationIncluded &
      happlications).
  destruct happlications as
    [(sigmaApplicationRoot & hsigmaApplication)
      (piApplicationRoot & hpiApplication)].
  exists endpointWitnessList, endpointContext, atomicRoot, domainRoot.
  split; [exact hendpointWitnessed |].
  split; [exact hbaseEndpointIncluded |].
  split; [exact hatomic |].
  split; [exact hdomain |].
  exists applicationWitnessList, applicationContext,
    sigmaApplicationRoot, piApplicationRoot.
  split; [exact happlicationWitnessed |].
  split; [exact hendpointApplicationIncluded |].
  rewrite (raw_dynamicTruthPredecessorStateTemplateContextCode
    M translation hagreement applicationContext).
  split; assumption.
Qed.

Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalApplicationResourceCompilers_equivalent
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  (RawDynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources
      M translation <->
   RawDynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources
      M translation).
Proof.
  intros M hPA translation hagreement. split.
  - exact
      (raw_dynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources_of_state_application_resources
        M hPA translation hagreement).
  - exact
      (raw_dynamicTruthNativeLocalZeroGrowingCanonicalStateApplicationResourcesCompilerOnCanonicalNormalizedResources_of_global_application_resources
        M hPA translation hagreement).
Qed.

(** Exact proof-producing residue after rank-zero normalization.  The output
    may grow the witnessed tail and concludes canonical applications, not
    native truth evidence.  Atomic adequacy and the domain disjunction travel
    with those applications so the subsequent evidence handoff is closed. *)
Definition
    RawDynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  forall (tail : nat -> M) witnessList baseContext (helperRoots : list M)
      sigmaDomain piDomain sigmaEvidence piEvidence,
    RawDynamicTruthNativeLocalZeroNormalizedResourcesAt M translation
      witnessList baseContext helperRoots ->
    RawDynamicTruthNativeLocalZeroCanonicalFullTraceAt M tail
      sigmaDomain piDomain sigmaEvidence piEvidence ->
    exists applicationWitnessList applicationContext,
      RawCodedPAAxiomWitnessContext M
        applicationWitnessList applicationContext /\
      RawContextListIncluded M baseContext applicationContext /\
      RawDynamicTruthZeroCanonicalApplicationRootsAt M applicationContext.

Arguments
  RawDynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources
  M translation : clear implicits.

(** Synchronize the split producer resources into the compact four-root
    application package.  Both possible context-growth steps are retained
    and their inclusions are composed, rather than requiring contraction to
    the normalized callback base. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources_of_global_application_resources
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalGlobalApplicationResourcesCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hagreement hcompiler tail witnessList
    baseContext helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (endpointWitnessList & endpointContext & atomicRoot & domainRoot &
      hendpointWitnessed & hbaseEndpointIncluded & hatomic & hdomain &
      hglobals).
  destruct
    (raw_dynamicTruthZeroCanonicalApplicationRootsAt_of_growing_global_roots
      M hPA translation hagreement endpointWitnessList endpointContext
      atomicRoot domainRoot hendpointWitnessed hatomic hdomain hglobals)
    as (applicationWitnessList & applicationContext &
      happlicationWitnessed & hendpointApplicationIncluded &
      happlications).
  exists applicationWitnessList, applicationContext.
  split; [exact happlicationWitnessed |].
  split.
  - intros member hmember.
    exact (hendpointApplicationIncluded member
      (hbaseEndpointIncluded member hmember)).
  - exact happlications.
Qed.

(** Canonical application production suffices for native direct evidence.
    The two possible context extensions are composed explicitly, keeping the
    residual compiler free to select whatever finite PA witness prefix its
    traversal needs. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCanonicalNormalizedResources_of_canonicalApplicationRoots
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hagreement hcompiler tail witnessList
    baseContext helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (applicationWitnessList & applicationContext &
      happlicationWitnessed & hbaseApplicationIncluded & happlications).
  destruct
    (raw_dynamicTruthZeroDirectEvidenceRoots_of_canonicalApplicationRoots
      M hPA translation hagreement applicationWitnessList applicationContext
      happlicationWitnessed happlications)
    as (evidenceWitnessList & evidenceContext & hevidenceWitnessed &
      happlicationEvidenceIncluded & hevidence).
  exists evidenceWitnessList, evidenceContext.
  split; [exact hevidenceWitnessed |].
  split.
  - intros member hmember.
    exact (happlicationEvidenceIncluded member
      (hbaseApplicationIncluded member hmember)).
  - exact hevidence.
Qed.

(** Converse compiler adapter.  The normalized traversal may therefore stop
    at either the native evidence pair or the canonical global-application
    pair; the two resource boundaries differ only by PA-provable formulas
    and finite standard-axiom witness growth. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources_of_directEvidence
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCanonicalNormalizedResources
    M translation ->
  RawDynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources
    M translation.
Proof.
  intros M hPA translation hagreement hcompiler tail witnessList
    baseContext helperRoots sigmaDomain piDomain sigmaEvidence piEvidence
    hresources htrace.
  destruct
    (hcompiler tail witnessList baseContext helperRoots
      sigmaDomain piDomain sigmaEvidence piEvidence hresources htrace)
    as (evidenceWitnessList & evidenceContext & hevidenceWitnessed &
      hbaseEvidenceIncluded & hevidence).
  destruct
    (raw_dynamicTruthZeroCanonicalApplicationRoots_of_directEvidenceRoots
      M hPA translation hagreement evidenceWitnessList evidenceContext
      hevidenceWitnessed hevidence)
    as (applicationWitnessList & applicationContext &
      happlicationWitnessed & hevidenceApplicationIncluded &
      happlications).
  exists applicationWitnessList, applicationContext.
  split; [exact happlicationWitnessed |].
  split.
  - intros member hmember.
    exact (hevidenceApplicationIncluded member
      (hbaseEvidenceIncluded member hmember)).
  - exact happlications.
Qed.

Theorem
    raw_dynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsAndDirectEvidenceCompilers_equivalent
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  (RawDynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources
      M translation <->
   RawDynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCanonicalNormalizedResources
      M translation).
Proof.
  intros M hPA translation hagreement. split.
  - exact
      (raw_dynamicTruthNativeLocalZeroGrowingDirectEvidenceCompilerOnCanonicalNormalizedResources_of_canonicalApplicationRoots
        M hPA translation hagreement).
  - exact
      (raw_dynamicTruthNativeLocalZeroGrowingCanonicalApplicationRootsCompilerOnCanonicalNormalizedResources_of_directEvidence
        M hPA translation hagreement).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationNormalizedCompilation.
