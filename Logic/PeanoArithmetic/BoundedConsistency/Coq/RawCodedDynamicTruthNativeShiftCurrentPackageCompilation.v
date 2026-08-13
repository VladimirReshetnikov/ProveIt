(**
  A call-site exact residual for the native shift successor.

  The older shift kernel accepts an arbitrary synchronized eight-root
  package.  The staged successor never calls it on arbitrary roots: it has
  the genuine current six-field package and the exact local and cross-level
  graph/proof pairs returned by the two preceding callbacks.  This module
  exposes precisely that smaller domain.

  The result retains the adequate paired orbit and exact shift transform
  used to select the output, together with an ordinary represented PA proof
  of that same output.  Keeping these witnesses makes the adapter to the
  public positive graph purely structural; no semantic truth is converted
  into proof syntax and no graph-functionality principle is assumed.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeShiftPositiveGraph
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeShiftStagedRootCompilation
  RawCodedDynamicTruthNativeShiftStagedCallbackCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeShiftCurrentPackageCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeShiftPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftStagedCallbackCompilation.

(** The proof-producing operation at the literal public shift call site. *)
Definition RawDynamicTruthNativeShiftCurrentPackageProofCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
    RawDynamicTruthNativeStagedPositiveCurrentAt M tail predecessorLevel
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal ->
    forall nextLocal localCertificate nextCrossLevel crossLevelCertificate,
      RawDynamicTruthNativeStagedNextLocalProofAt M
        tail predecessorLevel nextLocal localCertificate ->
      RawDynamicTruthNativeStagedNextCrossLevelProofAt M
        tail predecessorLevel nextCrossLevel crossLevelCertificate ->
      exists currentGlobalSigma currentGlobalPi
          nextShift shiftCertificate : M,
        RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
          tail (raw_succ M predecessorLevel)
          currentGlobalSigma currentGlobalPi /\
        RawDynamicTruthNativeShiftFieldTransformAt M
          currentGlobalSigma currentGlobalPi predecessorLevel nextShift /\
        RawCodedPAProofOf M nextShift shiftCertificate.

Arguments RawDynamicTruthNativeShiftCurrentPackageProofCompiler M
  : clear implicits.

(** The historical implication compiler supplies the smaller call-site
    operation.  The prerequisite helper synchronizes only the two graph-
    linked certificates actually received by the public callback. *)
Theorem
    raw_dynamicTruthNativeShiftCurrentPackageProofCompiler_of_body_implication
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M ->
  RawDynamicTruthNativeShiftCurrentPackageProofCompiler M.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent
    nextLocal localCertificate nextCrossLevel crossLevelCertificate
    hnextLocal hnextCrossLevel.
  destruct
    (raw_dynamicTruthNativeShiftStagedPrerequisites_of_callback_inputs
      M hPA tail predecessorLevel
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal localCertificate nextCrossLevel crossLevelCertificate
      hcurrent hnextLocal hnextCrossLevel) as
    (witnessList & baseContext & currentLocalRoot &
      currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & nextLocalRoot & nextCrossLevelRoot &
      hprerequisites).

  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M predecessorLevel)) as
    (currentGlobalSigma & currentGlobalPi & horbit &
      hcurrentSigma & hcurrentPi).
  assert (hadequateOrbit :
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail (raw_succ M predecessorLevel)
        currentGlobalSigma currentGlobalPi).
  {
    apply (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M tail
        (raw_succ M predecessorLevel)
        currentGlobalSigma currentGlobalPi)).
    split.
    - apply (proj1
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M tail
          (raw_succ M predecessorLevel)
          currentGlobalSigma currentGlobalPi)).
      exact horbit.
    - split; assumption.
  }
  destruct
    (dynamicTruthNativeShiftFieldTransformGraph_raw_total_on_adequate
      M hPA tail currentGlobalSigma currentGlobalPi predecessorLevel
      hcurrentSigma hcurrentPi) as
    (nextShift & htransformSat & _hnextShiftAdequate).
  pose proof (proj1
    (raw_sat_dynamicTruthNativeShiftFieldTransformGraph_iff M tail
      currentGlobalSigma currentGlobalPi predecessorLevel nextShift)
    htransformSat) as htransform.
  destruct
    (raw_dynamicTruthNativeShiftStagedTransformProof_of_body_implication
      M hPA hcompiler tail predecessorLevel
      currentGlobalSigma currentGlobalPi nextShift
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot
      hadequateOrbit htransform hprerequisites) as
    [shiftCertificate hshiftProof].
  exists currentGlobalSigma, currentGlobalPi, nextShift, shiftCertificate.
  split; [exact hadequateOrbit |].
  split; assumption.
Qed.

(** Reconstruct the public graph/proof pair from the retained selection. *)
Theorem
    raw_dynamicTruthNativeStagedNextShiftCompiler_of_currentPackageProofCompiler
    : forall (M : RawPAModel),
  RawDynamicTruthNativeShiftCurrentPackageProofCompiler M ->
  RawDynamicTruthNativeStagedNextShiftCompiler M.
Proof.
  intros M hcompiler tail predecessorLevel
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent
    nextLocal localCertificate nextCrossLevel crossLevelCertificate
    hnextLocal hnextCrossLevel.
  destruct
    (hcompiler tail predecessorLevel
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal hcurrent
      nextLocal localCertificate nextCrossLevel crossLevelCertificate
      hnextLocal hnextCrossLevel) as
    (currentGlobalSigma & currentGlobalPi & nextShift & shiftCertificate &
      hadequateOrbit & htransform & hshiftProof).
  exists nextShift, shiftCertificate.
  unfold RawDynamicTruthNativeStagedNextShiftProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt.
  split; [|exact hshiftProof].
  apply (proj2
    (raw_sat_dynamicTruthNativeShiftPositiveGraph_iff
      M tail predecessorLevel nextShift)).
  exists currentGlobalSigma, currentGlobalPi.
  split; [|exact htransform].
  exact (proj1 (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff
      M tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi) hadequateOrbit)).
Qed.

(** Named compatibility factorization from the former premise. *)
Corollary
    raw_dynamicTruthNativeStagedNextShiftCompiler_of_body_implication_via_currentPackage
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M ->
  RawDynamicTruthNativeStagedNextShiftCompiler M.
Proof.
  intros M hPA hbody.
  apply
    raw_dynamicTruthNativeStagedNextShiftCompiler_of_currentPackageProofCompiler.
  exact
    (raw_dynamicTruthNativeShiftCurrentPackageProofCompiler_of_body_implication
      M hPA hbody).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeShiftCurrentPackageCompilation.
