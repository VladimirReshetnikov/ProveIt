(**
  Complete guarded Boolean branch roots from canonical append evidence.

  Parent atomic/domain roots and selected Sigma/Pi row evidence may choose
  different finite standard-axiom extensions.  This module transports the
  parent triple to the evidence producer's target and packages all five
  roots under the literal conjunction- or disjunction-specific deep prefix.
  The append payload remains the honest arithmetic residue; no implication
  prefix and no unrelated bottom translation is substituted for it.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedSyntaxConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedDynamicTruthLocalExclusiveTemplateDirectInputs
  RawCodedDynamicTruthBooleanGuardedBranchExclusivity
  RawCodedDynamicTruthBooleanDirectChildAdmissibilityProofCompilation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation
  RawCodedDynamicTruthNativeZeroGuardedNormalization
  RawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification
  RawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification
  RawCodedDynamicTruthNativeZeroGuardedCanonicalAppendIntegration
  RawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation
  RawCodedDynamicTruthNativeZeroBooleanGuardedParentCompilation
  RawCodedDynamicTruthBooleanGuardedDiagonalCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeZeroBooleanGuardedBranchCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthBooleanGuardedBranchExclusivity.
Import
  PABoundedRawCodedDynamicTruthBooleanDirectChildAdmissibilityProofCompilation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeZeroGuardedNormalization.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedCanonicalAppendIntegration.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroBooleanGuardedParentCompilation.
Import PABoundedRawCodedDynamicTruthBooleanGuardedDiagonalCompilation.

(** Transport the three parent roots across a witnessed inclusion while
    preserving the exact constructor-specific prefix. *)
Theorem raw_dynamicTruthBooleanGuardedParentBranchRoots_transport : forall
    constructor (M : RawPAModel), RawPASatisfies M -> forall
      translation sourceWitnessList sourceContext
      targetWitnessList targetContext callerPrefix,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPAAxiomWitnessContext M targetWitnessList targetContext ->
  RawContextListIncluded M sourceContext targetContext ->
  RawDynamicTruthBooleanGuardedParentBranchRootsAt constructor M translation
    sourceContext callerPrefix ->
  RawDynamicTruthBooleanGuardedParentBranchRootsAt constructor M translation
    targetContext callerPrefix.
Proof.
  intros constructor M hPA translation sourceWitnessList sourceContext
    targetWitnessList targetContext callerPrefix hsourceWitnessed
    htargetWitnessed hincluded hparent.
  destruct hparent as
    [(sourceRoot & hsource) (atomicRoot & hatomic)
      (domainRoot & hdomain)].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      targetWitnessList targetContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
      (rawTemplateFormula translation
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate))))
      sourceRoot hsourceWitnessed htargetWitnessed hincluded hsource)
    as [transportedSourceRoot htransportedSource].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      targetWitnessList targetContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanDirectChildAtomicPremiseTemplate constructor
          coqDynamicTruthBooleanGuardedLevelTerm
          coqDynamicTruthBooleanGuardedParentTerm
          coqDynamicTruthBooleanGuardedLeftTerm
          coqDynamicTruthBooleanGuardedRightTerm
          coqDynamicTruthBooleanGuardedChildTerm))
      atomicRoot hsourceWitnessed htargetWitnessed hincluded hatomic)
    as [transportedAtomicRoot htransportedAtomic].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      targetWitnessList targetContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanDirectChildDomainPremiseTemplate constructor
          coqDynamicTruthBooleanGuardedLevelTerm
          coqDynamicTruthBooleanGuardedParentTerm
          coqDynamicTruthBooleanGuardedLeftTerm
          coqDynamicTruthBooleanGuardedRightTerm
          coqDynamicTruthBooleanGuardedChildTerm))
      domainRoot hsourceWitnessed htargetWitnessed hincluded hdomain)
    as [transportedDomainRoot htransportedDomain].
  constructor.
  - exists transportedSourceRoot. exact htransportedSource.
  - exists transportedAtomicRoot. exact htransportedAtomic.
  - exists transportedDomainRoot. exact htransportedDomain.
Qed.

(** Attach prefix-generic evidence to a Boolean parent package. *)
Theorem
    raw_dynamicTruthBooleanGuardedBranchRoots_of_parent_and_evidence_on_witnessed_extension :
    forall constructor (M : RawPAModel), RawPASatisfies M -> forall
      translation sourceWitnessList sourceContext
      targetWitnessList targetContext callerPrefix,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPAAxiomWitnessContext M targetWitnessList targetContext ->
  RawContextListIncluded M sourceContext targetContext ->
  RawDynamicTruthBooleanGuardedParentBranchRootsAt constructor M translation
    sourceContext callerPrefix ->
  RawDynamicTruthGuardedEvidenceRootsUnderPrefixAt M translation
    targetContext
    (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix) ->
  RawDynamicTruthBooleanGuardedBranchRootsAt constructor M translation
    targetContext callerPrefix.
Proof.
  intros constructor M hPA translation sourceWitnessList sourceContext
    targetWitnessList targetContext callerPrefix hsource htarget hincluded
    hparent hevidence.
  pose proof
    (raw_dynamicTruthBooleanGuardedParentBranchRoots_transport
      constructor M hPA translation sourceWitnessList sourceContext
      targetWitnessList targetContext callerPrefix
      hsource htarget hincluded hparent) as htransportedParent.
  destruct htransportedParent as
    [(sourceRoot & hsourceRoot) (atomicRoot & hatomic)
      (domainRoot & hdomain)].
  destruct hevidence as
    [(sigmaRoot & hsigma) (piRoot & hpi)].
  constructor.
  - exists sourceRoot. exact hsourceRoot.
  - exists atomicRoot. exact hatomic.
  - exists domainRoot. exact hdomain.
  - exists sigmaRoot.
    unfold coqDynamicTruthBooleanGuardedLocalSigmaEvidenceTemplate.
    exact hsigma.
  - exists piRoot.
    unfold coqDynamicTruthBooleanGuardedLocalPiEvidenceTemplate.
    exact hpi.
Qed.

(** One canonical append payload pair completes either Boolean constructor
    on a witnessed extension of its parent package. *)
Theorem
    raw_dynamicTruthBooleanGuardedBranchRoots_on_witnessed_extension_of_parent_and_canonical_append_kernel_payload_pair :
    forall constructor (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      sourceWitnessList sourceContext callerPrefix,
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthBooleanGuardedParentBranchRootsAt constructor M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    sourceContext callerPrefix ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix) ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawDynamicTruthBooleanGuardedBranchRootsAt constructor M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext callerPrefix.
Proof.
  intros constructor M hPA inputs sourceWitnessList sourceContext
    callerPrefix hidentification hsource hparent hpayloads.
  destruct
    (raw_dynamicTruthGuardedEvidenceRootsUnderPrefix_on_witnessed_extension_of_canonical_append_kernel_payload_pair
      M hPA inputs sourceWitnessList sourceContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
      hidentification hsource hpayloads) as
    (targetWitnessList & targetContext & htargetWitnessed & hincluded &
      hevidence).
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  exact
    (raw_dynamicTruthBooleanGuardedBranchRoots_of_parent_and_evidence_on_witnessed_extension
      constructor M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      sourceWitnessList sourceContext targetWitnessList targetContext
      callerPrefix hsource htargetWitnessed hincluded hparent hevidence).
Qed.

(** End-to-end constructor-local boundary from normalized resources.  The
    evidence identification supplies the older local-exclusive projection
    used by the parent compiler, ensuring that one selected translation is
    retained throughout. *)
Theorem
    raw_dynamicTruthBooleanGuardedBranchRoots_on_witnessed_extension_of_zero_normalized_and_canonical_append_kernel_payload_pair :
    forall constructor (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      normalizedTranslation witnessList baseContext helperRoots callerPrefix,
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
    normalizedTranslation witnessList baseContext helperRoots ->
  In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
    callerPrefix ->
  In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix) ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthBooleanGuardedBranchRootsAt constructor M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext callerPrefix.
Proof.
  intros constructor M hPA inputs normalizedTranslation witnessList
    baseContext helperRoots callerPrefix hidentification hnormalized
    hrestrictedIn hruleIn hpayloads.
  destruct
    (raw_dynamicTruthBooleanGuardedParentBranchRoots_of_zero_normalized_selected_identification_and_template_assumptions
      constructor M hPA inputs normalizedTranslation witnessList baseContext
      helperRoots callerPrefix
      (rawDynamicTruthZeroGuardedEvidence_localExclusive
        M inputs hidentification)
      hnormalized hrestrictedIn hruleIn) as
    (parentWitnessList & parentContext & hparentWitnessed &
      hbaseParentIncluded & hparent).
  destruct
    (raw_dynamicTruthBooleanGuardedBranchRoots_on_witnessed_extension_of_parent_and_canonical_append_kernel_payload_pair
      constructor M hPA inputs parentWitnessList parentContext callerPrefix
      hidentification hparentWitnessed hparent hpayloads) as
    (targetWitnessList & targetContext & htargetWitnessed &
      hparentTargetIncluded & hbranch).
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hparentTargetIncluded member
      (hbaseParentIncluded member hmember)).
  - exact hbranch.
Qed.

(** Apply the constructor-local guarded cell without discarding the caller
    assumptions.  This is the exact output needed inside a strong-step rule
    case before its assumptions are discharged. *)
Theorem
    raw_dynamicTruthBooleanGuardedDiagonalPair_on_witnessed_extension_of_zero_normalized_and_canonical_append_kernel_payload_pair :
    forall constructor (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      normalizedTranslation witnessList baseContext helperRoots callerPrefix,
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
    normalizedTranslation witnessList baseContext helperRoots ->
  In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
    callerPrefix ->
  In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix) ->
  exists targetWitnessList targetContext pairRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext callerPrefix)
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M constructor)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M constructor)
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros constructor M hPA inputs normalizedTranslation witnessList
    baseContext helperRoots callerPrefix hidentification hnormalized
    hrestrictedIn hruleIn hpayloads.
  destruct
    (raw_dynamicTruthBooleanGuardedBranchRoots_on_witnessed_extension_of_zero_normalized_and_canonical_append_kernel_payload_pair
      constructor M hPA inputs normalizedTranslation witnessList baseContext
      helperRoots callerPrefix hidentification hnormalized
      hrestrictedIn hruleIn hpayloads) as
    (branchWitnessList & branchContext & hbranchWitnessed &
      hbaseBranchIncluded & hbranch).
  destruct
    (raw_dynamicTruthBooleanGuardedDiagonalPair_on_witnessed_extension_under_caller_prefix
      constructor M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      branchWitnessList branchContext callerPrefix
      (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
        M hPA inputs callerPrefix)
      (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
        M hPA inputs
        (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix))
      hbranchWitnessed hbranch) as
    (targetWitnessList & targetContext & pairRoot & htargetWitnessed &
      hbranchTargetIncluded & hpair).
  exists targetWitnessList, targetContext, pairRoot.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hbranchTargetIncluded member
      (hbaseBranchIncluded member hmember)).
  - exact hpair.
Qed.

(** The two diagonal pair roots under a still-live template prefix. *)
Record RawDynamicTruthLocalBooleanDiagonalPairRootsUnderTemplatePrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (baseContext : M) (prefix : TemplateContext) : Prop := {
  rawDynamicTruthLocalBooleanDiagonalUnderPrefix_and : exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext prefix)
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanAnd)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanAnd)
          (rawFormulaBotCode M))) root;
  rawDynamicTruthLocalBooleanDiagonalUnderPrefix_or : exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext prefix)
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanOr)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanOr)
          (rawFormulaBotCode M))) root
}.

Arguments RawDynamicTruthLocalBooleanDiagonalPairRootsUnderTemplatePrefixAt
  M translation baseContext prefix : clear implicits.

(** Build both Boolean diagonals independently, merge their witnessed PA
    tails, and transport both prefixed proofs to the common target. *)
Theorem
    raw_dynamicTruthLocalBooleanDiagonalPairRootsUnderTemplatePrefixAt_on_witnessed_extension_of_zero_normalized_and_canonical_append_kernel_payload_pairs :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      normalizedTranslation witnessList baseContext helperRoots callerPrefix,
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
    normalizedTranslation witnessList baseContext helperRoots ->
  In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
    callerPrefix ->
  In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthBooleanGuardedDeepPrefix
        DTBooleanAnd callerPrefix) ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthBooleanGuardedDeepPrefix
        DTBooleanOr callerPrefix) ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthLocalBooleanDiagonalPairRootsUnderTemplatePrefixAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext callerPrefix.
Proof.
  intros M hPA inputs normalizedTranslation witnessList baseContext
    helperRoots callerPrefix hidentification hnormalized
    hrestrictedIn hruleIn handPayload horPayload.
  destruct
    (raw_dynamicTruthBooleanGuardedDiagonalPair_on_witnessed_extension_of_zero_normalized_and_canonical_append_kernel_payload_pair
      DTBooleanAnd M hPA inputs normalizedTranslation witnessList baseContext
      helperRoots callerPrefix hidentification hnormalized
      hrestrictedIn hruleIn handPayload) as
    (andWitnessList & andContext & andRoot & handWitnessed &
      hbaseAndIncluded & hand).
  destruct
    (raw_dynamicTruthBooleanGuardedDiagonalPair_on_witnessed_extension_of_zero_normalized_and_canonical_append_kernel_payload_pair
      DTBooleanOr M hPA inputs normalizedTranslation witnessList baseContext
      helperRoots callerPrefix hidentification hnormalized
      hrestrictedIn hruleIn horPayload) as
    (orWitnessList & orContext & orRoot & horWitnessed &
      hbaseOrIncluded & hor).
  destruct
    (raw_codedPAAxiomWitnessContext_prefixMerge M hPA
      andWitnessList andContext orWitnessList orContext
      handWitnessed horWitnessed) as
    (targetWitnessList & targetContext & htargetWitnessed &
      _handWitnessIncluded & handIncluded &
      _horWitnessIncluded & horIncluded & _htransport).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      andWitnessList andContext targetWitnessList targetContext callerPrefix
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanAnd)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanAnd)
          (rawFormulaBotCode M)))
      andRoot handWitnessed htargetWitnessed handIncluded hand)
    as [transportedAndRoot htransportedAnd].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      orWitnessList orContext targetWitnessList targetContext callerPrefix
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanOr)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanOr)
          (rawFormulaBotCode M)))
      orRoot horWitnessed htargetWitnessed horIncluded hor)
    as [transportedOrRoot htransportedOr].
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (handIncluded member (hbaseAndIncluded member hmember)).
  - constructor.
    + exists transportedAndRoot. exact htransportedAnd.
    + exists transportedOrRoot. exact htransportedOr.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroBooleanGuardedBranchCompilation.
