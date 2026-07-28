(**
  Public dependency-ordered callback for the staged substitution field.

  The substitution staged-root compiler consumes the current six roots and
  the preceding local, cross-level, and shift roots in one witnessed PA
  context.  The public callback supplies the current common package followed
  by three ordinary certificates, whose witnessed contexts are independently
  hidden.  This file is the structural adapter between those interfaces.

  A single adequate paired-global orbit and a single substitution transform
  are retained from target selection through proof compilation.  The three
  preceding certificates are accumulated in dependency order, transporting
  every earlier root into each returned witnessed context.  The resulting
  exact prerequisite record is passed to the sole linked body-implication
  residual; no context equality or semantic truth premise is introduced.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeSubstitutionPositiveGraph
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeSubstitutionStagedRootCompilation
  RawCodedDynamicTruthNativeStagedPrerequisiteAccumulation.

Module
  PABoundedRawCodedDynamicTruthNativeSubstitutionStagedCallbackCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeStagedPrerequisiteAccumulation.

(** Select the target only once.  The adequate orbit, exact transform, and
    public positive-graph assertion all retain the same carrier values. *)
Theorem raw_dynamicTruthNativeSubstitution_staged_graph_selection : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel,
  exists currentGlobalSigma currentGlobalPi fieldCode : M,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi /\
    RawDynamicTruthNativeSubstitutionFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode /\
    raw_formula_sat M
      (scons M fieldCode (scons M predecessorLevel tail))
      dynamicTruthNativeSubstitutionPositiveGraph.
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
    (dynamicTruthNativeSubstitutionFieldTransformGraph_raw_total_on_adequate
      M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
      hcurrentSigmaAdequate hcurrentPiAdequate) as
    (fieldCode & htransformGraph & _hfieldAdequate).
  pose proof (proj1
    (raw_sat_dynamicTruthNativeSubstitutionFieldTransformGraph_iff
      M tail currentGlobalSigma currentGlobalPi predecessorLevel fieldCode)
    htransformGraph) as htransform.
  exists currentGlobalSigma, currentGlobalPi, fieldCode.
  split; [exact hadequateOrbit |].
  split; [exact htransform |].
  apply (proj2
    (raw_sat_dynamicTruthNativeSubstitutionPositiveGraph_iff
      M tail predecessorLevel fieldCode)).
  exists currentGlobalSigma, currentGlobalPi.
  split; assumption.
Qed.

(** Accumulate current+local, then cross-level, then shift.  The final
    prerequisite package is exactly the one consumed by the staged
    substitution field theorem, so the adapter assumes only its linked
    body-implication compiler. *)
Theorem
    raw_dynamicTruthNativeStagedNextSubstitutionCompiler_of_body_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler
    M ->
  RawDynamicTruthNativeStagedNextSubstitutionCompiler M.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent
    nextLocal localCertificate nextCrossLevel crossLevelCertificate
    nextShift shiftCertificate
    hnextLocal hnextCrossLevel hnextShift.
  destruct hcurrent as [_hcurrentGraphs hcurrentProofs].
  unfold RawDynamicTruthNativeStagedNextLocalProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt in hnextLocal.
  destruct hnextLocal as [_hnextLocalGraph hnextLocalProof].
  unfold RawDynamicTruthNativeStagedNextCrossLevelProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt in hnextCrossLevel.
  destruct hnextCrossLevel as
    [_hnextCrossLevelGraph hnextCrossLevelProof].
  unfold RawDynamicTruthNativeStagedNextShiftProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt in hnextShift.
  destruct hnextShift as [_hnextShiftGraph hnextShiftProof].
  destruct
    (raw_dynamicTruthNativeSubstitution_staged_graph_selection
      M hPA tail predecessorLevel) as
    (currentGlobalSigma & currentGlobalPi & nextSubstitution &
      hadequateOrbit & htransform & hnextSubstitutionGraph).

  (** First synchronize the local certificate with the current six roots. *)
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
      localNextLocalRoot & hlocalPrerequisites).

  (** Add the cross-level certificate and transport the seven old roots. *)
  destruct
    (raw_dynamicTruthNativeShiftStagedPrerequisites_add_crossLevel
      M hPA localWitnessList localContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      localCurrentLocalRoot localCurrentCrossLevelRoot
      localCurrentShiftRoot localCurrentSubstitutionRoot
      localCurrentAxiomSoundnessRoot localCurrentFinalRoot
      localNextLocalRoot crossLevelCertificate
      hlocalPrerequisites hnextCrossLevelProof) as
    (crossWitnessList & crossContext &
      crossCurrentLocalRoot & crossCurrentCrossLevelRoot &
      crossCurrentShiftRoot & crossCurrentSubstitutionRoot &
      crossCurrentAxiomSoundnessRoot & crossCurrentFinalRoot &
      crossNextLocalRoot & crossNextCrossLevelRoot &
      hcrossPrerequisites).

  (** Add the shift certificate and retain the complete nine-root prefix. *)
  destruct
    (raw_dynamicTruthNativeSubstitutionStagedPrerequisites_add_shift
      M hPA crossWitnessList crossContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      crossCurrentLocalRoot crossCurrentCrossLevelRoot
      crossCurrentShiftRoot crossCurrentSubstitutionRoot
      crossCurrentAxiomSoundnessRoot crossCurrentFinalRoot
      crossNextLocalRoot crossNextCrossLevelRoot shiftCertificate
      hcrossPrerequisites hnextShiftProof) as
    (substitutionWitnessList & substitutionContext &
      substitutionCurrentLocalRoot & substitutionCurrentCrossLevelRoot &
      substitutionCurrentShiftRoot & substitutionCurrentSubstitutionRoot &
      substitutionCurrentAxiomSoundnessRoot &
      substitutionCurrentFinalRoot & substitutionNextLocalRoot &
      substitutionNextCrossLevelRoot & substitutionNextShiftRoot &
      hsubstitutionPrerequisites).

  destruct
    (raw_dynamicTruthNativeSubstitutionStagedFieldProof_of_body_implication
      M hPA hcompiler tail predecessorLevel
      currentGlobalSigma currentGlobalPi nextSubstitution
      substitutionWitnessList substitutionContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      substitutionCurrentLocalRoot substitutionCurrentCrossLevelRoot
      substitutionCurrentShiftRoot substitutionCurrentSubstitutionRoot
      substitutionCurrentAxiomSoundnessRoot substitutionCurrentFinalRoot
      substitutionNextLocalRoot substitutionNextCrossLevelRoot
      substitutionNextShiftRoot
      hadequateOrbit htransform hsubstitutionPrerequisites) as
    [substitutionCertificate hsubstitutionProof].
  exists nextSubstitution, substitutionCertificate.
  unfold RawDynamicTruthNativeStagedNextSubstitutionProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt.
  split; assumption.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeSubstitutionStagedCallbackCompilation.
