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
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedLtSuccCasesProofCompilation
  RawCodedPAGrowingTemplateConjunction
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
  RawCodedDynamicTruthNativeZeroGuardedFixedProductionBoundary
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
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedPAGrowingTemplateConjunction.
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
  PABoundedRawCodedDynamicTruthNativeZeroGuardedFixedProductionBoundary.
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

(** Merge an already synchronized Boolean pair with an independently
    compiled implication predecessor.  Constructor-local compilation is
    intentionally absent from this lemma: it is the reusable witnessed-tail
    join shared by membership-based and proof-root-based collision paths. *)
Theorem
    raw_dynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt_merge_boolean_and_imp :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      translation sourceContext callerPrefix
      booleanWitnessList booleanContext impWitnessList impContext impRoot,
  RawCodedPAAxiomWitnessContext M booleanWitnessList booleanContext ->
  RawContextListIncluded M sourceContext booleanContext ->
  RawDynamicTruthLocalBooleanDiagonalPairRootsUnderTemplatePrefixAt M
    translation booleanContext callerPrefix ->
  RawCodedPAAxiomWitnessContext M impWitnessList impContext ->
  RawContextListIncluded M sourceContext impContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation impContext callerPrefix)
    (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M) impRoot ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawDynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt M
      translation targetContext callerPrefix.
Proof.
  intros M hPA translation sourceContext callerPrefix
    booleanWitnessList booleanContext impWitnessList impContext impRoot
    hbooleanWitnessed hsourceBooleanIncluded hboolean
    himpWitnessed hsourceImpIncluded himp.
  destruct
    (raw_codedPAAxiomWitnessContext_prefixMerge M hPA
      booleanWitnessList booleanContext impWitnessList impContext
      hbooleanWitnessed himpWitnessed) as
    (targetWitnessList & targetContext & htargetWitnessed &
      _hbooleanWitnessIncluded & hbooleanIncluded &
      _himpWitnessIncluded & himpIncluded & _htransport).
  destruct hboolean as [(andRoot & hand) (orRoot & hor)].
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
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation impWitnessList impContext
      targetWitnessList targetContext callerPrefix
      (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
      impRoot himpWitnessed htargetWitnessed himpIncluded himp) as
    [transportedImpRoot htransportedImp].
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hbooleanIncluded member
      (hsourceBooleanIncluded member hmember)).
  - constructor.
    + constructor.
      * exists transportedAndRoot. exact htransportedAnd.
      * exists transportedOrRoot. exact htransportedOr.
    + exists transportedImpRoot. exact htransportedImp.
Qed.

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

(** Collision construction from actual renamed premise-root computations.
    All six computations may grow independently: implication, conjunction,
    and disjunction each receive their own restricted and rule roots beneath
    their literal five-binder prefix.  Fixed append residues remain shared
    through the constructor-indexed bundle, and only the three final
    collision roots are synchronized. *)
Theorem
    raw_dynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt_on_witnessed_extension_of_zero_normalized_independently_growing_renamed_premise_roots_and_guarded_collision_fixed_productions_or_refutations :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      normalizedTranslation witnessList baseContext helperRoots callerPrefix,
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
    normalizedTranslation witnessList baseContext helperRoots ->
  RawCodedPAGrowingTemplateLocalProofAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    witnessList baseContext (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate)) ->
  RawCodedPAGrowingTemplateLocalProofAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    witnessList baseContext (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)) ->
  RawCodedPAGrowingTemplateLocalProofAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    witnessList baseContext
    (coqDynamicTruthBooleanGuardedDeepPrefix DTBooleanAnd callerPrefix)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate)) ->
  RawCodedPAGrowingTemplateLocalProofAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    witnessList baseContext
    (coqDynamicTruthBooleanGuardedDeepPrefix DTBooleanAnd callerPrefix)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)) ->
  RawCodedPAGrowingTemplateLocalProofAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    witnessList baseContext
    (coqDynamicTruthBooleanGuardedDeepPrefix DTBooleanOr callerPrefix)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate)) ->
  RawCodedPAGrowingTemplateLocalProofAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    witnessList baseContext
    (coqDynamicTruthBooleanGuardedDeepPrefix DTBooleanOr callerPrefix)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingMany 5)
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)) ->
  RawDynamicTruthZeroCanonicalIdentifiedGuardedCollisionFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
    M hPA inputs ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      targetContext callerPrefix.
Proof.
  intros M hPA inputs normalizedTranslation witnessList baseContext
    helperRoots callerPrefix hidentification hnormalized
    himpRestrictedGrowing himpRuleGrowing
    handRestrictedGrowing handRuleGrowing
    horRestrictedGrowing horRuleGrowing hfixed.
  destruct
    (raw_dynamicTruthZeroCanonicalIdentified_guardedCollisionAppendRowKernelPayloadPairsForCaller_of_fixed
      M hPA inputs hidentification hfixed callerPrefix) as
    (himpPayload & handPayload & horPayload).

  destruct
    (raw_dynamicTruthImpGuardedParentBranchRoots_of_zero_normalized_selected_identification_and_independently_growing_renamed_roots
      M hPA inputs normalizedTranslation witnessList baseContext helperRoots
      callerPrefix
      (rawDynamicTruthZeroGuardedEvidence_localExclusive
        M inputs hidentification)
      hnormalized himpRestrictedGrowing himpRuleGrowing) as
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
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      impBranchWitnessList impBranchContext callerPrefix
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
        M hPA inputs (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      himpBranchWitnessed himpBranch) as
    (impWitnessList & impContext & impRoot & himpWitnessed &
      himpBranchIncluded & himp).
  assert (hbaseImpIncluded : RawContextListIncluded M baseContext impContext).
  {
    intros member hmember.
    exact (himpBranchIncluded member
      (himpParentBranchIncluded member
        (hbaseImpParentIncluded member hmember))).
  }

  destruct
    (raw_dynamicTruthLocalBooleanDiagonalPairRootsUnderTemplatePrefixAt_on_witnessed_extension_of_zero_normalized_independently_growing_renamed_roots_and_canonical_append_kernel_payload_pairs
      M hPA inputs normalizedTranslation witnessList baseContext helperRoots
      callerPrefix hidentification hnormalized
      handRestrictedGrowing handRuleGrowing
      horRestrictedGrowing horRuleGrowing handPayload horPayload) as
    (booleanWitnessList & booleanContext & hbooleanWitnessed &
      hbaseBooleanIncluded & hboolean).

  exact
    (raw_dynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt_merge_boolean_and_imp
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext callerPrefix booleanWitnessList booleanContext
      impWitnessList impContext impRoot hbooleanWitnessed
      hbaseBooleanIncluded hboolean himpWitnessed hbaseImpIncluded himp).
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

(** Fixed-production-facing spelling of the preceding endpoint.  The three
    payload hypotheses collapse to one explicit constructor-indexed fixed
    bundle; suffix insertion and payload synchronization are internal. *)
Corollary
    raw_dynamicTruthLocalGuardedCollisionRootsAt_on_witnessed_extension_of_zero_normalized_restricted_rule_roots_and_guarded_collision_fixed_productions_or_refutations :
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
  RawDynamicTruthZeroCanonicalIdentifiedGuardedCollisionFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
    M hPA inputs ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthLocalBooleanDiagonalPairRootsAt M targetContext /\
    RawDynamicTruthLocalRootAt M targetContext
      (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M).
Proof.
  intros M hPA inputs normalizedTranslation witnessList baseContext
    helperRoots restrictedRoot ruleRoot hidentification hnormalized
    hrestricted hrule hfixed.
  destruct
    (raw_dynamicTruthZeroCanonicalIdentified_guardedCollisionAppendRowKernelPayloadPairsForCaller_of_fixed
      M hPA inputs hidentification hfixed
      coqDynamicTruthGuardedCollisionEndpointAssumptionPrefix) as
    (himpPayload & handPayload & horPayload).
  exact
    (raw_dynamicTruthLocalGuardedCollisionRootsAt_on_witnessed_extension_of_zero_normalized_restricted_rule_roots_and_canonical_append_kernel_payload_pairs
      M hPA inputs normalizedTranslation witnessList baseContext helperRoots
      restrictedRoot ruleRoot hidentification hnormalized
      hrestricted hrule himpPayload handPayload horPayload).
Qed.

(** Producer-facing relaxation of the preceding endpoint.  Restricted-proof
    analysis, rule validation, and guarded collision construction may each
    append their own finite batch of PA witnesses.  The three computations
    are synchronized only after they have selected their natural endpoints;
    the generic growing two-assumption cut then closes the live shell for
    each constructor independently.

    This formulation is strictly weaker than requiring the two premise roots
    in [baseContext].  It is also the form needed by the dependency-ordered
    callback boundary, whose proof analyses deliberately expose growing
    template proofs rather than equating independently generated tails. *)
Theorem
    raw_dynamicTruthLocalGuardedCollisionRootsAt_on_witnessed_extension_of_zero_normalized_independently_growing_restricted_rule_roots_and_guarded_collision_fixed_productions_or_refutations :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      normalizedTranslation witnessList baseContext helperRoots,
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  RawDynamicTruthNativeLocalZeroGuardedNormalizedResourcesAt M
    normalizedTranslation witnessList baseContext helperRoots ->
  RawCodedPAGrowingTemplateLocalProofAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    witnessList baseContext []
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate) ->
  RawCodedPAGrowingTemplateLocalProofAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    witnessList baseContext []
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyRulePremise) ->
  RawDynamicTruthZeroCanonicalIdentifiedGuardedCollisionFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
    M hPA inputs ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthLocalBooleanDiagonalPairRootsAt M targetContext /\
    RawDynamicTruthLocalRootAt M targetContext
      (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M).
Proof.
  intros M hPA inputs normalizedTranslation witnessList baseContext
    helperRoots hidentification hnormalized hrestricted hrule hfixed.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (callerPrefix :=
    coqDynamicTruthGuardedCollisionEndpointAssumptionPrefix).
  destruct
    (raw_dynamicTruthZeroCanonicalIdentified_guardedCollisionAppendRowKernelPayloadPairsForCaller_of_fixed
      M hPA inputs hidentification hfixed callerPrefix) as
    (himpPayload & handPayload & horPayload).
  destruct
    (raw_dynamicTruthLocalGuardedCollisionRootsUnderTemplatePrefixAt_on_witnessed_extension_of_zero_normalized_and_canonical_append_kernel_payload_pairs
      M hPA inputs normalizedTranslation witnessList baseContext helperRoots
      callerPrefix hidentification hnormalized
      (or_introl eq_refl) (or_intror (or_introl eq_refl))
      himpPayload handPayload horPayload) as
    (collisionWitnessList & collisionContext & hcollisionWitnessed &
      hbaseCollisionIncluded & hcollision).
  destruct hcollision as
    [[(andRoot & hand) (orRoot & hor)] (impRoot & himp)].
  assert (hprefixAdequate :
      RawCodedTemplatePrefixAtomicallyAdequate M translation callerPrefix).
  {
    unfold translation, callerPrefix,
      coqDynamicTruthGuardedCollisionEndpointAssumptionPrefix.
    exact (raw_guardedDirectStructuralTemplatePrefix_atomically_adequate
      M hPA inputs
      [coqRestrictedPADerivationSoundnessRestrictedProofTemplate;
       coqStrongStepProofEndpointAtomicAdequacyRulePremise]).
  }
  assert (handGrowing : RawCodedPAGrowingTemplateLocalProofAt M translation
      witnessList baseContext callerPrefix
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanAnd)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanAnd)
          (rawFormulaBotCode M)))).
  {
    exists collisionWitnessList, collisionContext, andRoot.
    split; [exact hcollisionWitnessed |].
    split; [exact hbaseCollisionIncluded | exact hand].
  }
  assert (horGrowing : RawCodedPAGrowingTemplateLocalProofAt M translation
      witnessList baseContext callerPrefix
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanOr)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanOr)
          (rawFormulaBotCode M)))).
  {
    exists collisionWitnessList, collisionContext, orRoot.
    split; [exact hcollisionWitnessed |].
    split; [exact hbaseCollisionIncluded | exact hor].
  }
  assert (himpGrowing : RawCodedPAGrowingTemplateLocalProofAt M translation
      witnessList baseContext callerPrefix
      (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)).
  {
    exists collisionWitnessList, collisionContext, impRoot.
    split; [exact hcollisionWitnessed |].
    split; [exact hbaseCollisionIncluded | exact himp].
  }
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_discharge_two_template_assumptions
      M hPA translation witnessList baseContext
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate
      coqStrongStepProofEndpointAtomicAdequacyRulePremise
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanAnd)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanAnd)
          (rawFormulaBotCode M)))
      hprefixAdequate hrestricted hrule handGrowing) as handDischarged.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_discharge_two_template_assumptions
      M hPA translation witnessList baseContext
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate
      coqStrongStepProofEndpointAtomicAdequacyRulePremise
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanOr)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanOr)
          (rawFormulaBotCode M)))
      hprefixAdequate hrestricted hrule horGrowing) as horDischarged.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_discharge_two_template_assumptions
      M hPA translation witnessList baseContext
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate
      coqStrongStepProofEndpointAtomicAdequacyRulePremise
      (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
      hprefixAdequate hrestricted hrule himpGrowing) as himpDischarged.
  destruct
    (raw_codedPAGrowingTemplateLocalProofAt_pair_at_prefix
      M hPA translation witnessList baseContext []
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanAnd)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanAnd)
          (rawFormulaBotCode M)))
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanOr)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanOr)
          (rawFormulaBotCode M)))
      handDischarged horDischarged) as
    (booleanWitnessList & booleanContext & dischargedAndRoot &
      dischargedOrRoot & hbooleanWitnessed & hbaseBooleanIncluded &
      hdischargedAnd & hdischargedOr).
  destruct himpDischarged as
    (impWitnessList & impContext & dischargedImpRoot & himpWitnessed &
      hbaseImpIncluded & hdischargedImp).
  destruct
    (raw_codedPAAxiomWitnessContext_prefixMerge M hPA
      booleanWitnessList booleanContext impWitnessList impContext
      hbooleanWitnessed himpWitnessed) as
    (targetWitnessList & targetContext & htargetWitnessed &
      _hbooleanWitnessIncluded & hbooleanIncluded &
      _himpWitnessIncluded & himpIncluded & _htransport).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation booleanWitnessList booleanContext
      targetWitnessList targetContext []
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanAnd)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanAnd)
          (rawFormulaBotCode M)))
      dischargedAndRoot hbooleanWitnessed htargetWitnessed
      hbooleanIncluded hdischargedAnd) as
    [transportedAndRoot htransportedAnd].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation booleanWitnessList booleanContext
      targetWitnessList targetContext []
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanOr)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanOr)
          (rawFormulaBotCode M)))
      dischargedOrRoot hbooleanWitnessed htargetWitnessed
      hbooleanIncluded hdischargedOr) as
    [transportedOrRoot htransportedOr].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation impWitnessList impContext
      targetWitnessList targetContext []
      (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
      dischargedImpRoot himpWitnessed htargetWitnessed
      himpIncluded hdischargedImp) as
    [transportedImpRoot htransportedImp].
  cbn [rawTemplateContextCodeOnTail] in
    htransportedAnd, htransportedOr, htransportedImp.
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hbooleanIncluded member
      (hbaseBooleanIncluded member hmember)).
  - split.
    + split.
      * exists transportedAndRoot. exact htransportedAnd.
      * exists transportedOrRoot. exact htransportedOr.
    + exists transportedImpRoot. exact htransportedImp.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroGuardedCollisionCompilation.
