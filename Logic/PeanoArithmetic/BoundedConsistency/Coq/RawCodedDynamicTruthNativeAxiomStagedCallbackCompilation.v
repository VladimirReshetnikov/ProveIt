(**
  Public dependency-ordered callback for native PA-axiom soundness.

  The staged axiom root compiler works with one adequate paired-global orbit,
  one exact axiom-field transform, and ten formula roots in a common
  witnessed PA-axiom context.  The public callback instead receives the
  current six-field common-context package followed by four ordinary
  certificates for local, cross-level, shift, and substitution.

  This module bridges those interfaces structurally.  It first selects one
  adequate orbit and one transform output and retains those exact witnesses
  for both positive-graph membership and proof compilation.  It then merges
  the four ordinary certificates into the current witnessed context in their
  dependency order.  Finally the exact transform-selected staged endpoint
  opens the linked axiom trace and packages its carried root as the public
  graph/proof pair.

  No context equality, empty-context replacement, or semantic validity-to-
  proof conversion occurs.  The sole proof-producing residual is the linked
  staged kernel-implication compiler isolated by the axiom root module.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation
  RawCodedDynamicTruthNativeStagedPrerequisiteAccumulation.

Module PABoundedRawCodedDynamicTruthNativeAxiomStagedCallbackCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeStagedPrerequisiteAccumulation.

(** Select the graph output without forgetting the orbit and transform which
    generated it.  Keeping these three facts in one existential package
    prevents proof compilation from reopening the positive graph and
    choosing an unrelated orbit trace. *)
Theorem raw_dynamicTruthNativeAxiom_staged_graph_selection : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel,
  exists currentGlobalSigma currentGlobalPi fieldCode : M,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi /\
    RawDynamicTruthNativeAxiomSoundnessFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode /\
    raw_formula_sat M
      (scons M fieldCode (scons M predecessorLevel tail))
      dynamicTruthNativeAxiomSoundnessPositiveGraph.
Proof.
  intros M hPA tail predecessorLevel.
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (currentGlobalSigma & currentGlobalPi & horbitGraph &
      hcurrentSigmaAdequate & hcurrentPiAdequate).
  pose proof (proj1
    (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff
      M tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi)
    horbitGraph) as horbit.
  assert (hadequateOrbit :
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail (raw_succ M predecessorLevel)
        currentGlobalSigma currentGlobalPi).
  {
    apply (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff
        M tail (raw_succ M predecessorLevel)
        currentGlobalSigma currentGlobalPi)).
    split; [exact horbit |].
    split; assumption.
  }
  destruct
    (dynamicTruthNativeAxiomSoundnessFieldTransformGraph_raw_total_on_adequate
      M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
      hcurrentSigmaAdequate hcurrentPiAdequate) as
    (fieldCode & htransformGraph & hfieldAdequate).
  pose proof (proj1
    (raw_sat_dynamicTruthNativeAxiomSoundnessFieldTransformGraph_iff
      M tail currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)
    htransformGraph) as htransform.
  exists currentGlobalSigma, currentGlobalPi, fieldCode.
  split; [exact hadequateOrbit |].
  split; [exact htransform |].
  apply (proj2
    (raw_sat_dynamicTruthNativeAxiomSoundnessPositiveGraph_iff
      M tail predecessorLevel fieldCode)).
  exists currentGlobalSigma, currentGlobalPi.
  split.
  - apply (proj1
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff
        M tail (raw_succ M predecessorLevel)
        currentGlobalSigma currentGlobalPi)).
    exact hadequateOrbit.
  - exact htransform.
Qed.

(** The exact public axiom-soundness callback follows from the sole linked
    arithmetic seam.  Each certificate accumulation step transports every
    root already installed; no context is identified propositionally. *)
Theorem
    raw_dynamicTruthNativeStagedNextAxiomSoundnessCompiler_of_kernel_implication
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M ->
  RawDynamicTruthNativeStagedNextAxiomSoundnessCompiler M.
Proof.
  intros M hPA hkernel tail predecessorLevel
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent
    nextLocal localCertificate nextCrossLevel crossLevelCertificate
    nextShift shiftCertificate nextSubstitution substitutionCertificate
    hnextLocal hnextCrossLevel hnextShift hnextSubstitution.
  destruct hcurrent as [hcurrentGraphs hcurrentProofs].
  unfold RawDynamicTruthNativeStagedNextLocalProofAt,
    RawDynamicTruthNativeStagedNextCrossLevelProofAt,
    RawDynamicTruthNativeStagedNextShiftProofAt,
    RawDynamicTruthNativeStagedNextSubstitutionProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt in *.
  destruct hnextLocal as [hnextLocalGraph hnextLocalProof].
  destruct hnextCrossLevel as [hnextCrossGraph hnextCrossProof].
  destruct hnextShift as [hnextShiftGraph hnextShiftProof].
  destruct hnextSubstitution as
    [hnextSubstitutionGraph hnextSubstitutionProof].

  (** Keep one adequate orbit, its literal transform, and the positive-graph
      target together until the final proof has been compiled. *)
  destruct (raw_dynamicTruthNativeAxiom_staged_graph_selection
    M hPA tail predecessorLevel) as
    (currentGlobalSigma & currentGlobalPi & nextAxiomSoundness &
      hadequateOrbit & htransform & hnextAxiomGraph).

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

  (** Add substitution and retain the complete ten-root axiom prefix. *)
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
    (axiomWitnessList & axiomContext &
      axiomCurrentLocalRoot & axiomCurrentCrossLevelRoot &
      axiomCurrentShiftRoot & axiomCurrentSubstitutionRoot &
      axiomCurrentAxiomSoundnessRoot & axiomCurrentFinalRoot &
      axiomNextLocalRoot & axiomNextCrossLevelRoot & axiomNextShiftRoot &
      axiomNextSubstitutionRoot & haxiomPrerequisites).

  destruct
    (raw_dynamicTruthNativeAxiomPositiveProofAt_of_staged_kernel_implication
      M hPA hkernel tail predecessorLevel
      currentGlobalSigma currentGlobalPi nextAxiomSoundness
      hadequateOrbit htransform
      axiomWitnessList axiomContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      axiomCurrentLocalRoot axiomCurrentCrossLevelRoot
      axiomCurrentShiftRoot axiomCurrentSubstitutionRoot
      axiomCurrentAxiomSoundnessRoot axiomCurrentFinalRoot
      axiomNextLocalRoot axiomNextCrossLevelRoot axiomNextShiftRoot
      axiomNextSubstitutionRoot haxiomPrerequisites) as
    [axiomSoundnessCertificate hnextAxiomProof].
  exists nextAxiomSoundness, axiomSoundnessCertificate.
  unfold RawDynamicTruthNativeStagedNextAxiomSoundnessProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt.
  destruct hnextAxiomProof as [hcompiledGraph hcompiledProof].
  split.
  - (** Both graph assertions describe the same orbit/transform-selected
        target.  Return the one retained by graph selection explicitly. *)
    exact hnextAxiomGraph.
  - exact hcompiledProof.
Qed.

End PABoundedRawCodedDynamicTruthNativeAxiomStagedCallbackCompilation.
