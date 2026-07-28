(**
  Public dependency-ordered callback for the staged cross-level field.

  The cross-level root compiler works with an exact transform and with the
  six current roots plus the already produced local root in one witnessed
  context.  The public staged callback instead receives a current master
  package and an ordinary local certificate.  This module supplies the
  missing structural adapter between those interfaces.

  We select one adequate paired-global orbit and one transform output from
  the represented graphs, retain those same witnesses for both graph truth
  and proof compilation, merge the local certificate into the current
  witnessed context, and invoke the sole trace-linked body-implication
  compiler.  No graph functionality or equality between independently
  selected orbit witnesses is needed at this stage.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeCrossLevelPositiveGraph
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation
  RawCodedDynamicTruthNativeCrossLevelStagedRootCompilation
  RawCodedDynamicTruthNativeStagedPrerequisiteAccumulation.

Module PABoundedRawCodedDynamicTruthNativeCrossLevelStagedCallbackCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import
  PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeStagedPrerequisiteAccumulation.

(** A graph-and-transform selection which preserves the adequate orbit used
    by the proof compiler.  Returning all three facts together prevents the
    callback from reopening the positive graph and choosing another orbit. *)
Theorem raw_dynamicTruthNativeCrossLevel_staged_graph_selection : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel,
  exists currentGlobalSigma currentGlobalPi fieldCode : M,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi /\
    RawDynamicTruthNativeCrossLevelFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode /\
    raw_formula_sat M
      (scons M fieldCode (scons M predecessorLevel tail))
      dynamicTruthNativeCrossLevelPositiveGraph.
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
    repeat split; assumption.
  }
  destruct
    (dynamicTruthNativeCrossLevelFieldTransformGraph_raw_total_on_adequate
      M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
      hcurrentSigmaAdequate hcurrentPiAdequate) as
    [fieldCode htransformGraph].
  pose proof (proj1
    (raw_sat_dynamicTruthNativeCrossLevelFieldTransformGraph_iff
      M tail currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)
    htransformGraph) as htransform.
  exists currentGlobalSigma, currentGlobalPi, fieldCode.
  split; [exact hadequateOrbit |].
  split; [exact htransform |].
  apply (proj2
    (raw_sat_dynamicTruthNativeCrossLevelPositiveGraph_iff
      M tail predecessorLevel fieldCode)).
  exists currentGlobalSigma, currentGlobalPi.
  split; assumption.
Qed.

(** The public callback now depends only on the one honest cross-level
    arithmetic seam isolated by the staged root compiler. *)
Theorem
    raw_dynamicTruthNativeStagedNextCrossLevelCompiler_of_body_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M ->
  RawDynamicTruthNativeStagedNextCrossLevelCompiler M.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent
    nextLocal localCertificate hnextLocal.
  destruct hcurrent as [hcurrentGraphs hcurrentProofs].
  unfold RawDynamicTruthNativeStagedNextLocalProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt in hnextLocal.
  destruct hnextLocal as [hnextLocalGraph hnextLocalProof].
  destruct
    (raw_dynamicTruthNativeCrossLevel_staged_graph_selection
      M hPA tail predecessorLevel) as
    (currentGlobalSigma & currentGlobalPi & nextCrossLevel &
      hadequateOrbit & htransform & hnextCrossLevelGraph).
  destruct
    (raw_dynamicTruthNativeCrossLevelStagedPrerequisites_of_current_and_local
      M hPA
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal localCertificate
      hcurrentProofs hnextLocalProof) as
    (witnessList & baseContext &
      currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & nextLocalRoot & hprerequisites).
  destruct
    (raw_dynamicTruthNativeCrossLevelStagedTransformProof_of_body_implication
      M hPA hcompiler tail predecessorLevel
      currentGlobalSigma currentGlobalPi nextCrossLevel
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot
      hadequateOrbit htransform hprerequisites) as
    [crossLevelCertificate hcrossLevelProof].
  exists nextCrossLevel, crossLevelCertificate.
  unfold RawDynamicTruthNativeStagedNextCrossLevelProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt.
  split; assumption.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeCrossLevelStagedCallbackCompilation.
