(**
  Reduce the final V2 callback to the genuinely outstanding rule compiler.

  The older trace-level V2 resource record asks its caller to choose two
  direct-input records, prove two code equalities, and separately return a
  closure remainder and a carried-consistency bridge.  Those coordinates are
  not independent at an actual final trace.  The synchronized native package
  already constructed from that trace and its witnessed prerequisites:

  - chooses the basic direct inputs and retains their literal provenance;
  - supplies the strong-prefix closure remainder; and
  - compiles the carried-consistency bridge on the incoming base context.

  Once the provenance is exposed, opaque-tail invariance proves both code
  equalities as exact syntactic equalities.  Consequently the
  only remaining proof-producing datum at this seam is an ordinary V2
  rule-case compiler for some opaque extension of the canonical basic
  inputs.  This module states that residual directly and feeds it through the
  checked extended-to-basic V2 handoff.  It uses neither semantic
  truth-to-proof conversion nor any standardness assumption on the model.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateNumeralParameters
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessExtendedDirectInputs
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder
  RawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareDispatcherIntegration
  RawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsIdentification
  RawCodedRestrictedPANativeFinalUnifiedSynchronizedGrowingCoherence
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalUnifiedSynchronizedCarriedConsistency
  RawCodedDynamicTruthNativeFinalCarriedConsistencyAfterV2Soundness.

Module
  PABoundedRawCodedDynamicTruthNativeFinalV2UnifiedCarriedResidualReduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateNumeralParameters.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareDispatcherIntegration.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectSynchronizedRowsIdentification.
Import
  PABoundedRawCodedRestrictedPANativeFinalUnifiedSynchronizedGrowingCoherence.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalUnifiedSynchronizedCarriedConsistency.
Import
  PABoundedRawCodedDynamicTruthNativeFinalCarriedConsistencyAfterV2Soundness.

(** The sole residual after the synchronized carried construction.  The
    quantification over the three canonical selector coordinates lets the
    trace construction choose its witnesses first.  The caller then only
    chooses an opaque tail on which the already isolated V2 rule compiler is
    available.  No equation or consistency resource appears in this type. *)
Definition
    RawDynamicTruthNativeFinalV2CanonicalExtendedRemainingRuleCasesCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  exists opaqueTail :
      RawCoqRestrictedPAOpaqueTailDirectSelector M parameters,
    RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler M hPA
      (rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth opaqueTail).

Arguments
  RawDynamicTruthNativeFinalV2CanonicalExtendedRemainingRuleCasesCompiler
  M hPA : clear implicits.

(** Exact pointwise reduction.  The incoming trace and prerequisites select
    the canonical parameter/selector triple.  For that particular triple,
    one V2 compiler on one opaque tail is sufficient for the final proof.
    This quantifier order records the premise reduction without imposing a
    uniform rule-compiler hypothesis on unrelated selector choices. *)
Theorem
    raw_dynamicTruthNativeFinalStagedNextFinalProof_canonical_extended_remaining_v2_reduction
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (stageTail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M stageTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness ->
  exists (parameters : RawCodedTemplateNumeralParameters M),
  exists contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters,
    (exists opaqueTail :
        RawCoqRestrictedPAOpaqueTailDirectSelector M parameters,
      RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler M hPA
        (rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth opaqueTail)) ->
    exists finalCertificate : M,
      RawDynamicTruthNativeStagedNextFinalProofAt M
        stageTail level nextFinal finalCertificate.
Proof.
  intros M hPA stageTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites.

  (** This constructor performs the coherence, open-shell arithmetic, and
      bottom-growth stages on witnessed extensions of [baseContext]. *)
  destruct
    (raw_dynamicTruthNativeFinalStagedGraphTrace_unified_synchronized_carried_consistency_exists
      M hPA stageTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode
      witnessList baseContext htrace hprerequisites)
    as (parameters & basicInputs & currentGlobalSigma & currentGlobalPi &
      sigmaDomain & piDomain & nextSigmaEvidence & nextGlobalSigma &
      nextGlobalPi & sigmaApplicationSelector & contextApplicationSelector &
      closureCount & axiom & hcarriedResources).
  destruct hcarriedResources as
    [_hlower _hupper _hdirect hnative hremainder hcarried].

  (** The synchronized half of the native link deliberately retains the
      otherwise-hidden selector witnesses and literal input equality. *)
  destruct hnative as [_hunified hsynchronized].
  destruct hsynchronized as
    [_haxiomLink _hsynchronizedLower hprovenance].
  destruct hprovenance as
    (contextTruth & conclusionTruth & hbasicProvenance &
      _hconclusionSelectorLink).
  subst basicInputs.

  exists parameters, contextTruth, conclusionTruth.
  intros (opaqueTail & hv2).
  exact
    (raw_dynamicTruthNativeFinalStagedNextFinalProof_of_extended_remaining_v2_and_basic_carried
      M hPA parameters contextTruth conclusionTruth opaqueTail
      stageTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode baseContext
      (rawCoqRestrictedPADirectClosureReplacement M)
      axiom closureCount htrace hv2 hremainder hcarried).
Qed.

(** Pointwise final construction from the uniform one-coordinate residual.
    The reduction theorem above first selects the only three coordinates at
    which the residual is invoked. *)
Theorem
    raw_dynamicTruthNativeFinalStagedNextFinalProof_of_canonical_extended_remaining_v2
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeFinalV2CanonicalExtendedRemainingRuleCasesCompiler
    M hPA ->
  forall (stageTail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M stageTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness ->
  exists finalCertificate : M,
    RawDynamicTruthNativeStagedNextFinalProofAt M
      stageTail level nextFinal finalCertificate.
Proof.
  intros M hPA hremaining stageTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites.
  destruct
    (raw_dynamicTruthNativeFinalStagedNextFinalProof_canonical_extended_remaining_v2_reduction
      M hPA stageTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode witnessList baseContext
      htrace hprerequisites)
    as (parameters & contextTruth & conclusionTruth & hreduce).
  apply hreduce.
  exact (hremaining parameters contextTruth conclusionTruth).
Qed.

(** Public final callback with the reduced, one-coordinate residual. *)
Theorem
    raw_dynamicTruthNativeFinalStagedTraceProofCompiler_of_canonical_extended_remaining_v2
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeFinalV2CanonicalExtendedRemainingRuleCasesCompiler
    M hPA ->
  RawDynamicTruthNativeFinalStagedTraceProofCompiler M.
Proof.
  intros M hPA hremaining stageTail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites.
  exact
    (raw_dynamicTruthNativeFinalStagedNextFinalProof_of_canonical_extended_remaining_v2
      M hPA hremaining stageTail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode witnessList baseContext
      htrace hprerequisites).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalV2UnifiedCarriedResidualReduction.
