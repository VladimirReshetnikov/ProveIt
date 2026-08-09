(**
  Public callback adapter for the sixth native successor field.

  The dependency-ordered callback presents the five preceding successor
  fields as ordinary represented PA certificates.  The final root compiler,
  however, intentionally works over one explicit witnessed PA-axiom context
  containing the current six roots and all five new roots.  The committed
  staged-prerequisite accumulation chain is exactly the bridge between those
  interfaces.

  We merge certificates in production order: local, cross-level, shift,
  substitution, and axiom soundness.  At every step all roots already
  accumulated are transported into the newly returned witnessed context.
  The graph half of each original callback pair is retained unchanged.  The
  resulting eleven-root prerequisite and those five graph assertions feed
  the final source-linked compiler wrapper, which returns the exact public
  compact-target graph/proof pair.

  No context equality, empty-context replacement, or semantic validity-to-
  proof conversion is used here.  The only mathematical residual is the
  already isolated source-linked dynamic-soundness implication compiler.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CompactRestrictedPAConsistencyFormulaCodeGraph
  RawCodedTemplateDirectStructuralTranslation
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeStagedPrerequisiteAccumulation
  RawCodedDynamicTruthNativeFinalUniversalSoundnessComposition
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.

Module PABoundedRawCodedDynamicTruthNativeFinalStagedCallbackCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCompactRestrictedPAConsistencyFormulaCodeGraph.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeStagedPrerequisiteAccumulation.
Import PABoundedRawCodedDynamicTruthNativeFinalUniversalSoundnessComposition.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.

(** The exact public final callback follows from a pointwise trace-proof
    compiler.  All intermediate existential witnesses below are contexts and
    transported roots returned by proved accumulation theorems, not
    additional hypotheses.  Abstracting this last pointwise step lets an
    implementation grow the accumulated context before returning its
    ordinary proof. *)
Theorem
    raw_dynamicTruthNativeStagedNextFinalCompiler_of_trace_proof
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeFinalStagedTraceProofCompiler M ->
  RawDynamicTruthNativeStagedNextFinalCompiler M.
Proof.
  intros M hPA htraceProof.
  intros tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    [hcurrentGraphs hcurrentProofs]
    nextLocal localCertificate nextCrossLevel crossLevelCertificate
    nextShift shiftCertificate nextSubstitution substitutionCertificate
    nextAxiomSoundness axiomSoundnessCertificate
    hnextLocal hnextCrossLevel hnextShift hnextSubstitution
    hnextAxiomSoundness.
  unfold RawDynamicTruthNativeStagedNextLocalProofAt,
    RawDynamicTruthNativeStagedNextCrossLevelProofAt,
    RawDynamicTruthNativeStagedNextShiftProofAt,
    RawDynamicTruthNativeStagedNextSubstitutionProofAt,
    RawDynamicTruthNativeStagedNextAxiomSoundnessProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt in *.
  destruct hnextLocal as [hnextLocalGraph hnextLocalProof].
  destruct hnextCrossLevel as [hnextCrossGraph hnextCrossProof].
  destruct hnextShift as [hnextShiftGraph hnextShiftProof].
  destruct hnextSubstitution as
    [hnextSubstitutionGraph hnextSubstitutionProof].
  destruct hnextAxiomSoundness as
    [hnextAxiomGraph hnextAxiomProof].

  (** Add local to the current six-field common context. *)
  destruct
    (raw_dynamicTruthNativeCrossLevelStagedPrerequisites_of_current_and_local
      M hPA
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal localCertificate
      hcurrentProofs hnextLocalProof) as
    (localWitnessList & localContext &
      localCurrentLocalRoot & localCurrentCrossLevelRoot &
      localCurrentShiftRoot & localCurrentSubstitutionRoot &
      localCurrentAxiomSoundnessRoot & localCurrentFinalRoot &
      localNextLocalRoot & hlocalPrefix).

  (** Add cross-level and transport the preceding seven roots. *)
  destruct (raw_dynamicTruthNativeShiftStagedPrerequisites_add_crossLevel
    M hPA localWitnessList localContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel
    localCurrentLocalRoot localCurrentCrossLevelRoot
    localCurrentShiftRoot localCurrentSubstitutionRoot
    localCurrentAxiomSoundnessRoot localCurrentFinalRoot
    localNextLocalRoot crossLevelCertificate
    hlocalPrefix hnextCrossProof) as
    (crossWitnessList & crossContext &
      crossCurrentLocalRoot & crossCurrentCrossLevelRoot &
      crossCurrentShiftRoot & crossCurrentSubstitutionRoot &
      crossCurrentAxiomSoundnessRoot & crossCurrentFinalRoot &
      crossNextLocalRoot & crossNextCrossLevelRoot & hcrossPrefix).

  (** Add shift and transport the preceding eight roots. *)
  destruct (raw_dynamicTruthNativeSubstitutionStagedPrerequisites_add_shift
    M hPA crossWitnessList crossContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel nextShift
    crossCurrentLocalRoot crossCurrentCrossLevelRoot
    crossCurrentShiftRoot crossCurrentSubstitutionRoot
    crossCurrentAxiomSoundnessRoot crossCurrentFinalRoot
    crossNextLocalRoot crossNextCrossLevelRoot shiftCertificate
    hcrossPrefix hnextShiftProof) as
    (shiftWitnessList & shiftContext &
      shiftCurrentLocalRoot & shiftCurrentCrossLevelRoot &
      shiftCurrentShiftRoot & shiftCurrentSubstitutionRoot &
      shiftCurrentAxiomSoundnessRoot & shiftCurrentFinalRoot &
      shiftNextLocalRoot & shiftNextCrossLevelRoot & shiftNextShiftRoot &
      hshiftPrefix).

  (** Add substitution and transport the preceding nine roots. *)
  destruct
    (raw_dynamicTruthNativeAxiomStagedPrerequisites_add_substitution
      M hPA shiftWitnessList shiftContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      shiftCurrentLocalRoot shiftCurrentCrossLevelRoot
      shiftCurrentShiftRoot shiftCurrentSubstitutionRoot
      shiftCurrentAxiomSoundnessRoot shiftCurrentFinalRoot
      shiftNextLocalRoot shiftNextCrossLevelRoot shiftNextShiftRoot
      substitutionCertificate hshiftPrefix hnextSubstitutionProof) as
    (substitutionWitnessList & substitutionContext &
      substitutionCurrentLocalRoot & substitutionCurrentCrossLevelRoot &
      substitutionCurrentShiftRoot & substitutionCurrentSubstitutionRoot &
      substitutionCurrentAxiomSoundnessRoot & substitutionCurrentFinalRoot &
      substitutionNextLocalRoot & substitutionNextCrossLevelRoot &
      substitutionNextShiftRoot & substitutionNextSubstitutionRoot &
      hsubstitutionPrefix).

  (** Add axiom soundness and retain the complete eleven-root package. *)
  destruct
    (raw_dynamicTruthNativeFinalStagedPrerequisites_add_axiomSoundness
      M hPA substitutionWitnessList substitutionContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      substitutionCurrentLocalRoot substitutionCurrentCrossLevelRoot
      substitutionCurrentShiftRoot substitutionCurrentSubstitutionRoot
      substitutionCurrentAxiomSoundnessRoot substitutionCurrentFinalRoot
      substitutionNextLocalRoot substitutionNextCrossLevelRoot
      substitutionNextShiftRoot substitutionNextSubstitutionRoot
      axiomSoundnessCertificate hsubstitutionPrefix hnextAxiomProof) as
    (finalWitnessList & finalContext &
      finalCurrentLocalRoot & finalCurrentCrossLevelRoot &
      finalCurrentShiftRoot & finalCurrentSubstitutionRoot &
      finalCurrentAxiomSoundnessRoot & finalCurrentFinalRoot &
      finalNextLocalRoot & finalNextCrossLevelRoot & finalNextShiftRoot &
      finalNextSubstitutionRoot & finalNextAxiomSoundnessRoot &
      hfinalPrerequisitesAt).
  assert (hfinalPrerequisitesOn :
      RawDynamicTruthNativeFinalStagedPrerequisitesOn M
        finalWitnessList finalContext
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal
        nextLocal nextCrossLevel nextShift nextSubstitution
        nextAxiomSoundness).
  {
    exists finalCurrentLocalRoot, finalCurrentCrossLevelRoot,
      finalCurrentShiftRoot, finalCurrentSubstitutionRoot,
      finalCurrentAxiomSoundnessRoot, finalCurrentFinalRoot,
      finalNextLocalRoot, finalNextCrossLevelRoot, finalNextShiftRoot,
      finalNextSubstitutionRoot, finalNextAxiomSoundnessRoot.
    exact hfinalPrerequisitesAt.
  }
  destruct (compactRestrictedPAConsistencyFormulaCodeGraph_raw_total
    M hPA tail (raw_succ M level)) as [nextFinal hnextFinalGraph].
  destruct (raw_dynamicTruthNativeFinalStagedGraphTrace_of_graphs
    M hPA tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    hcurrentGraphs hnextLocalGraph hnextCrossGraph hnextShiftGraph
    hnextSubstitutionGraph hnextAxiomGraph hnextFinalGraph) as
    [successorNumeralCode htrace].
  destruct (htraceProof tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode finalWitnessList finalContext
    htrace hfinalPrerequisitesOn) as [finalCertificate hfinal].
  exists nextFinal, finalCertificate.
  exact hfinal.
Qed.

(** Backward-compatible specialization to the original global
    source-linked implication compiler. *)
Theorem
    raw_dynamicTruthNativeStagedNextFinalCompiler_of_source_linked_implication
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M ->
  RawDynamicTruthNativeStagedNextFinalCompiler M.
Proof.
  intros M hPA hsourceLinked.
  exact
    (raw_dynamicTruthNativeStagedNextFinalCompiler_of_trace_proof
      M hPA
      (raw_dynamicTruthNativeFinalStagedTraceProofCompiler_of_source_linked_implication
        M hPA hsourceLinked)).
Qed.

(** Public callback adapter using the reduced universal-soundness seam.  The
    target-opening proof is supplied by the final target-refutation compiler,
    so this theorem exposes only the genuinely remaining two-root package
    (represented universal soundness and its consistency bridge). *)
Theorem
    raw_dynamicTruthNativeStagedNextFinalCompiler_of_universal_soundness_bridge
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeFinalUniversalSoundnessBridgeCompiler M ->
  RawDynamicTruthNativeStagedNextFinalCompiler M.
Proof.
  intros M hPA hbridge.
  exact (raw_dynamicTruthNativeStagedNextFinalCompiler_of_source_linked_implication
    M hPA
    (raw_dynamicTruthNativeFinalSourceLinkedImplicationRootCompiler_of_bridge
      M hPA hbridge)).
Qed.

(** Context-flexible public adapter for the direct soundness architecture.
    The supplied compiler may merge an ordinary direct soundness certificate
    into the staged base before producing its two bridge roots; the generic
    trace interface hides that merge from the public callback. *)
Theorem
    raw_dynamicTruthNativeStagedNextFinalCompiler_of_growing_direct_bridge :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeCompiler
    M inputs ->
  RawDynamicTruthNativeStagedNextFinalCompiler M.
Proof.
  intros M hPA inputs hbridge.
  exact
    (raw_dynamicTruthNativeStagedNextFinalCompiler_of_trace_proof
      M hPA
      (raw_dynamicTruthNativeFinalStagedTraceProofCompiler_of_growing_direct_bridge
        M hPA inputs hbridge)).
Qed.

End PABoundedRawCodedDynamicTruthNativeFinalStagedCallbackCompilation.
