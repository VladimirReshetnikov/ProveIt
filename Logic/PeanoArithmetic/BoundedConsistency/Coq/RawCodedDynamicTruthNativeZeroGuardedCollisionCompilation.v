(**
  Synchronize all constructor-sensitive guarded collision roots.

  The implication predecessor and the two Boolean diagonals are compiled
  under different constructor-specific deep prefixes.  Their final formulas,
  however, all live under the same caller prefix.  This module keeps that
  prefix abstract, lets the implication and Boolean producers grow their
  standard-PA witness tails independently, and then transports all three
  roots to one witnessed target.

  Keeping the caller prefix live is essential: the normalized rank-zero
  parent compilers use the restricted-proof and endpoint-adequacy assumptions
  supplied by the surrounding strong-step shell.  No attempt is made here to
  turn those assumptions into globally provable formulas.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofAssumptionDischarge
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation
  RawCodedDynamicTruthImpGuardedBranchExclusivity
  RawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation
  RawCodedDynamicTruthBooleanGuardedBranchExclusivity
  RawCodedDynamicTruthBooleanGuardedDiagonalCompilation
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthNativeLocalGuardedNonImpPairCompilation
  RawCodedDynamicTruthNativeZeroGuardedNormalization
  RawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation
  RawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification
  RawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification
  RawCodedDynamicTruthNativeZeroGuardedCanonicalAppendIntegration
  RawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation
  RawCodedDynamicTruthNativeZeroBooleanGuardedBranchCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeZeroGuardedCollisionCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateLocalProofAssumptionDischarge.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.
Import PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.
Import
  PABoundedRawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation.
Import PABoundedRawCodedDynamicTruthBooleanGuardedBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBooleanGuardedDiagonalCompilation.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import PABoundedRawCodedDynamicTruthNativeLocalGuardedNonImpPairCompilation.
Import PABoundedRawCodedDynamicTruthNativeZeroGuardedNormalization.
Import
  PABoundedRawCodedDynamicTruthNativeZeroPredecessorLogicalRootsCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedCanonicalAppendIntegration.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroBooleanGuardedBranchCompilation.

(** The exact constructor-sensitive residue under a still-live caller prefix.
    The record deliberately stores proof existence rather than chosen roots,
    matching the public local-root interfaces used by the staged compiler. *)
Record RawDynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (baseContext : M) (callerPrefix : TemplateContext) : Prop := {
  rawDynamicTruthLocalGuardedCollision_boolean :
    RawDynamicTruthLocalBooleanDiagonalPairRootsUnderTemplatePrefixAt M
      translation baseContext callerPrefix;
  rawDynamicTruthLocalGuardedCollision_imp : exists predecessorRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext callerPrefix)
      (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
      predecessorRoot
}.

Arguments RawDynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt
  M translation baseContext callerPrefix : clear implicits.

(** The two assumptions used transiently by constructor-local endpoint
    compilation.  Their order is chosen once here so every later discharge
    uses the same literal context. *)
Definition coqDynamicTruthGuardedCollisionEndpointAssumptionPrefix
    : TemplateContext :=
  [ coqRestrictedPADerivationSoundnessRestrictedProofTemplate;
    coqStrongStepProofEndpointAtomicAdequacyRulePremise ].

(** Compile implication, conjunction, and disjunction independently and merge
    their witnessed tails.  The payload hypotheses are constructor-local: it
    would be unsound to reuse the implication payload under a Boolean guard,
    because those prefixes contain different branch assumptions. *)
Theorem
    raw_dynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt_on_witnessed_extension_of_zero_normalized_and_canonical_append_kernel_payload_pairs :
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
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix) ->
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
    RawDynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext callerPrefix.
Proof.
  intros M hPA inputs normalizedTranslation witnessList baseContext
    helperRoots callerPrefix hidentification hnormalized
    hrestrictedIn hruleIn himpPayload handPayload horPayload.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).

  (** First build and close the implication branch. *)
  destruct
    (raw_dynamicTruthImpGuardedParentBranchRoots_of_zero_normalized_selected_identification_and_template_assumptions
      M hPA inputs normalizedTranslation witnessList baseContext helperRoots
      callerPrefix
      (rawDynamicTruthZeroGuardedEvidence_localExclusive
        M inputs hidentification)
      hnormalized hrestrictedIn hruleIn) as
    (impParentWitnessList & impParentContext & himpParentWitnessed &
      hbaseImpParentIncluded & himpParent).
  destruct
    (raw_dynamicTruthImpGuardedBranchRoots_on_witnessed_extension_of_parent_and_canonical_append_kernel_payload_pair
      M hPA inputs impParentWitnessList impParentContext callerPrefix
      hidentification himpParentWitnessed himpParent himpPayload) as
    (impBranchWitnessList & impBranchContext & himpBranchWitnessed &
      himpParentBranchIncluded & himpBranch).
  destruct
    (raw_dynamicTruthImpGuardedPredecessorRoot_on_witnessed_extension_of_branch_roots
      M hPA translation impBranchWitnessList impBranchContext callerPrefix
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
        M hPA inputs (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      himpBranchWitnessed himpBranch) as
    (impWitnessList & impContext & impRoot & himpWitnessed &
      himpBranchIncluded & himp).
  assert (hbaseImpIncluded :
      RawContextListIncluded M baseContext impContext).
  {
    intros member hmember.
    exact (himpBranchIncluded member
      (himpParentBranchIncluded member
        (hbaseImpParentIncluded member hmember))).
  }

  (** The Boolean compiler already synchronizes the And and Or branches. *)
  destruct
    (raw_dynamicTruthLocalBooleanDiagonalPairRootsUnderTemplatePrefixAt_on_witnessed_extension_of_zero_normalized_and_canonical_append_kernel_payload_pairs
      M hPA inputs normalizedTranslation witnessList baseContext helperRoots
      callerPrefix hidentification hnormalized hrestrictedIn hruleIn
      handPayload horPayload) as
    (booleanWitnessList & booleanContext & hbooleanWitnessed &
      hbaseBooleanIncluded & hboolean).

  (** Merge the implication and Boolean targets, then transport every final
      root under the unchanged caller prefix. *)
  destruct
    (raw_codedPAAxiomWitnessContext_prefixMerge M hPA
      impWitnessList impContext booleanWitnessList booleanContext
      himpWitnessed hbooleanWitnessed) as
    (targetWitnessList & targetContext & htargetWitnessed &
      _himpWitnessIncluded & himpIncluded &
      _hbooleanWitnessIncluded & hbooleanIncluded & _htransport).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation impWitnessList impContext
      targetWitnessList targetContext callerPrefix
      (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
      impRoot himpWitnessed htargetWitnessed himpIncluded himp) as
    [transportedImpRoot htransportedImp].
  destruct hboolean as
    [(andRoot & hand) (orRoot & hor)].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation booleanWitnessList booleanContext
      targetWitnessList targetContext callerPrefix
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanAnd)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanAnd)
          (rawFormulaBotCode M)))
      andRoot hbooleanWitnessed htargetWitnessed hbooleanIncluded hand) as
    [transportedAndRoot htransportedAnd].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation booleanWitnessList booleanContext
      targetWitnessList targetContext callerPrefix
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanOr)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanOr)
          (rawFormulaBotCode M)))
      orRoot hbooleanWitnessed htargetWitnessed hbooleanIncluded hor) as
    [transportedOrRoot htransportedOr].

  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (himpIncluded member (hbaseImpIncluded member hmember)).
  - constructor.
    + constructor.
      * exists transportedAndRoot. exact htransportedAnd.
      * exists transportedOrRoot. exact htransportedOr.
    + exists transportedImpRoot. exact htransportedImp.
Qed.

(** Replace the two live assumptions by actual local proofs.  Payload
    production may enlarge the PA tail first; the two premise roots are
    transported to that final target before the generic two-assumption cut is
    applied independently to all three collision conclusions. *)
Theorem
    raw_dynamicTruthLocalGuardedCollisionRootsAt_on_witnessed_extension_of_zero_normalized_restricted_rule_roots_and_canonical_append_kernel_payload_pairs :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      normalizedTranslation witnessList baseContext helperRoots
      restrictedRoot ruleRoot,
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
    normalizedTranslation witnessList baseContext helperRoots ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    restrictedRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyRulePremise)
    ruleRoot ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthImpGuardedDeepPrefix
        coqDynamicTruthGuardedCollisionEndpointAssumptionPrefix) ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthBooleanGuardedDeepPrefix DTBooleanAnd
        coqDynamicTruthGuardedCollisionEndpointAssumptionPrefix) ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthBooleanGuardedDeepPrefix DTBooleanOr
        coqDynamicTruthGuardedCollisionEndpointAssumptionPrefix) ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthLocalBooleanDiagonalPairRootsAt M targetContext /\
    RawDynamicTruthLocalRootAt M targetContext
      (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M).
Proof.
  intros M hPA inputs normalizedTranslation witnessList baseContext
    helperRoots restrictedRoot ruleRoot hidentification hnormalized
    hrestricted hrule himpPayload handPayload horPayload.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (callerPrefix :=
    coqDynamicTruthGuardedCollisionEndpointAssumptionPrefix).
  destruct
    (raw_dynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt_on_witnessed_extension_of_zero_normalized_and_canonical_append_kernel_payload_pairs
      M hPA inputs normalizedTranslation witnessList baseContext helperRoots
      callerPrefix hidentification hnormalized
      (or_introl eq_refl) (or_intror (or_introl eq_refl))
      himpPayload handPayload horPayload) as
    (targetWitnessList & targetContext & htargetWitnessed &
      hbaseTargetIncluded & hcollision).
  pose proof
    (rawDynamicTruthNativeLocalZeroGuardedNormalized_fields
      M normalizedTranslation witnessList baseContext helperRoots hnormalized)
    as hfields.
  pose proof
    (rawDynamicTruthNativeLocalZeroCurrentFields_witnessed
      M witnessList baseContext hfields) as hbaseWitnessed.
  assert (hbaseRealizable : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable
      M witnessList baseContext hbaseWitnessed).
  }
  assert (htargetRealizable : RawContextListRealizable M targetContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable
      M targetWitnessList targetContext htargetWitnessed).
  }
  assert (hprefixAdequate :
      RawCodedTemplatePrefixAtomicallyAdequate M translation callerPrefix).
  {
    unfold translation.
    exact (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
      M hPA inputs callerPrefix).
  }
  assert (hrestrictedOnEmptyPrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext [])
      (rawTemplateFormula translation
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
      restrictedRoot).
  {
    cbn [rawTemplateContextCodeOnTail].
    exact hrestricted.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation witnessList baseContext
      targetWitnessList targetContext []
      (rawTemplateFormula translation
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
      restrictedRoot hbaseWitnessed htargetWitnessed hbaseTargetIncluded
      hrestrictedOnEmptyPrefix) as
    [transportedRestrictedRoot htransportedRestricted].
  cbn [rawTemplateContextCodeOnTail] in htransportedRestricted.
  assert (hruleOnEmptyPrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext [])
      (rawTemplateFormula translation
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)
      ruleRoot).
  {
    cbn [rawTemplateContextCodeOnTail].
    exact hrule.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation witnessList baseContext
      targetWitnessList targetContext []
      (rawTemplateFormula translation
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)
      ruleRoot hbaseWitnessed htargetWitnessed hbaseTargetIncluded
      hruleOnEmptyPrefix) as
    [transportedRuleRoot htransportedRule].
  cbn [rawTemplateContextCodeOnTail] in htransportedRule.
  destruct hcollision as
    [[(andRoot & hand) (orRoot & hor)] (impRoot & himp)].
  destruct
    (raw_codedPALocalProof_discharge_two_template_assumptions
      M hPA translation targetContext
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate
      coqStrongStepProofEndpointAtomicAdequacyRulePremise
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanAnd)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanAnd)
          (rawFormulaBotCode M)))
      transportedRestrictedRoot transportedRuleRoot andRoot
      htargetRealizable hprefixAdequate
      htransportedRestricted htransportedRule hand) as
    [dischargedAndRoot hdischargedAnd].
  destruct
    (raw_codedPALocalProof_discharge_two_template_assumptions
      M hPA translation targetContext
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate
      coqStrongStepProofEndpointAtomicAdequacyRulePremise
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanOr)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanOr)
          (rawFormulaBotCode M)))
      transportedRestrictedRoot transportedRuleRoot orRoot
      htargetRealizable hprefixAdequate
      htransportedRestricted htransportedRule hor) as
    [dischargedOrRoot hdischargedOr].
  destruct
    (raw_codedPALocalProof_discharge_two_template_assumptions
      M hPA translation targetContext
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate
      coqStrongStepProofEndpointAtomicAdequacyRulePremise
      (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
      transportedRestrictedRoot transportedRuleRoot impRoot
      htargetRealizable hprefixAdequate
      htransportedRestricted htransportedRule himp) as
    [dischargedImpRoot hdischargedImp].
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split; [exact hbaseTargetIncluded |].
  split.
  - split.
    + exists dischargedAndRoot. exact hdischargedAnd.
    + exists dischargedOrRoot. exact hdischargedOr.
  - exists dischargedImpRoot. exact hdischargedImp.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroGuardedCollisionCompilation.
