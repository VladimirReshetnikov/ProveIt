(**
  A call-site exact residual for native PA-axiom soundness.

  The historical axiom kernel accepts an arbitrary linked ten-root package,
  four formula shifts, and a context self-shift.  The dependency-ordered
  successor never invokes it on arbitrary data.  At its literal call site it
  has the genuine current six-field graph/common-context package followed by
  the exact local, cross-level, shift, and substitution graph/proof pairs
  produced by the preceding callbacks.

  This module restricts the proof-producing interface to those genuine
  inputs.  Its output retains one adequate paired-global orbit, the exact
  axiom-soundness transform selected from that orbit, and an ordinary PA
  proof of the same selected field.  Retaining all three facts makes the
  adapter back to the public positive graph purely structural: no graph
  functionality comparison and no semantic truth-to-proof conversion is
  required.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation
  RawCodedDynamicTruthNativeStagedPrerequisiteAccumulation
  RawCodedDynamicTruthNativeAxiomStagedCallbackCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeAxiomSoundnessCurrentPackageCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeStagedPrerequisiteAccumulation.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedCallbackCompilation.

(** The exact proof-producing operation used at the public axiom-soundness
    call site.  Unlike the linked kernel, none of the ten formula proofs can
    be chosen independently: six are carried by [hcurrent], and the last four
    arrive through their graph-indexed ordinary certificates. *)
Definition RawDynamicTruthNativeAxiomSoundnessCurrentPackageProofCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
    RawDynamicTruthNativeStagedPositiveCurrentAt M tail predecessorLevel
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal ->
    forall nextLocal localCertificate nextCrossLevel crossLevelCertificate
      nextShift shiftCertificate nextSubstitution substitutionCertificate,
      RawDynamicTruthNativeStagedNextLocalProofAt M
        tail predecessorLevel nextLocal localCertificate ->
      RawDynamicTruthNativeStagedNextCrossLevelProofAt M
        tail predecessorLevel nextCrossLevel crossLevelCertificate ->
      RawDynamicTruthNativeStagedNextShiftProofAt M
        tail predecessorLevel nextShift shiftCertificate ->
      RawDynamicTruthNativeStagedNextSubstitutionProofAt M
        tail predecessorLevel nextSubstitution substitutionCertificate ->
      exists currentGlobalSigma currentGlobalPi
          nextAxiomSoundness axiomSoundnessCertificate : M,
        RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
          tail (raw_succ M predecessorLevel)
          currentGlobalSigma currentGlobalPi /\
        RawDynamicTruthNativeAxiomSoundnessFieldTransformAt M
          currentGlobalSigma currentGlobalPi predecessorLevel
          nextAxiomSoundness /\
        RawCodedPAProofOf M
          nextAxiomSoundness axiomSoundnessCertificate.

Arguments RawDynamicTruthNativeAxiomSoundnessCurrentPackageProofCompiler M
  : clear implicits.

(** The stronger historical kernel supplies the call-site residual.  The
    proof accumulates the four ordinary certificates in dependency order,
    transporting all earlier roots at every witnessed-context extension. *)
Theorem
    raw_dynamicTruthNativeAxiomSoundnessCurrentPackageProofCompiler_of_kernel_implication
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M ->
  RawDynamicTruthNativeAxiomSoundnessCurrentPackageProofCompiler M.
Proof.
  intros M hPA hkernel tail predecessorLevel
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent
    nextLocal localCertificate nextCrossLevel crossLevelCertificate
    nextShift shiftCertificate nextSubstitution substitutionCertificate
    hnextLocal hnextCrossLevel hnextShift hnextSubstitution.
  destruct hcurrent as [_hcurrentGraphs hcurrentProofs].
  unfold RawDynamicTruthNativeStagedNextLocalProofAt,
    RawDynamicTruthNativeStagedNextCrossLevelProofAt,
    RawDynamicTruthNativeStagedNextShiftProofAt,
    RawDynamicTruthNativeStagedNextSubstitutionProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt in *.
  destruct hnextLocal as [_hnextLocalGraph hnextLocalProof].
  destruct hnextCrossLevel as [_hnextCrossGraph hnextCrossProof].
  destruct hnextShift as [_hnextShiftGraph hnextShiftProof].
  destruct hnextSubstitution as
    [_hnextSubstitutionGraph hnextSubstitutionProof].

  (** Select and retain the exact orbit/transform pair whose output will be
      compiled below.  The positive-graph projection returned by the helper
      is intentionally not used as a proof certificate. *)
  destruct
    (raw_dynamicTruthNativeAxiom_staged_graph_selection
      M hPA tail predecessorLevel) as
    (currentGlobalSigma & currentGlobalPi & nextAxiomSoundness &
      hadequateOrbit & htransform & _hnextAxiomGraph).

  (** Merge the local certificate with the genuine current package. *)
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

  (** Add cross-level while transporting the seven installed roots. *)
  destruct
    (raw_dynamicTruthNativeShiftStagedPrerequisites_add_crossLevel
      M hPA localWitnessList localContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      localCurrentLocalRoot localCurrentCrossLevelRoot
      localCurrentShiftRoot localCurrentSubstitutionRoot
      localCurrentAxiomSoundnessRoot localCurrentFinalRoot
      localNextLocalRoot crossLevelCertificate
      hlocalPrerequisites hnextCrossProof) as
    (crossWitnessList & crossContext &
      crossCurrentLocalRoot & crossCurrentCrossLevelRoot &
      crossCurrentShiftRoot & crossCurrentSubstitutionRoot &
      crossCurrentAxiomSoundnessRoot & crossCurrentFinalRoot &
      crossNextLocalRoot & crossNextCrossLevelRoot & hcrossPrerequisites).

  (** Add shift while transporting the eight installed roots. *)
  destruct
    (raw_dynamicTruthNativeSubstitutionStagedPrerequisites_add_shift
      M hPA crossWitnessList crossContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel nextShift
      crossCurrentLocalRoot crossCurrentCrossLevelRoot
      crossCurrentShiftRoot crossCurrentSubstitutionRoot
      crossCurrentAxiomSoundnessRoot crossCurrentFinalRoot
      crossNextLocalRoot crossNextCrossLevelRoot shiftCertificate
      hcrossPrerequisites hnextShiftProof) as
    (shiftWitnessList & shiftContext &
      shiftCurrentLocalRoot & shiftCurrentCrossLevelRoot &
      shiftCurrentShiftRoot & shiftCurrentSubstitutionRoot &
      shiftCurrentAxiomSoundnessRoot & shiftCurrentFinalRoot &
      shiftNextLocalRoot & shiftNextCrossLevelRoot & shiftNextShiftRoot &
      hshiftPrerequisites).

  (** Add substitution and obtain exactly the linked ten-root package used
      by the old arithmetic kernel. *)
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
      substitutionCertificate hshiftPrerequisites hnextSubstitutionProof) as
    (axiomWitnessList & axiomContext &
      axiomCurrentLocalRoot & axiomCurrentCrossLevelRoot &
      axiomCurrentShiftRoot & axiomCurrentSubstitutionRoot &
      axiomCurrentAxiomSoundnessRoot & axiomCurrentFinalRoot &
      axiomNextLocalRoot & axiomNextCrossLevelRoot & axiomNextShiftRoot &
      axiomNextSubstitutionRoot & haxiomPrerequisites).

  destruct
    (raw_dynamicTruthNativeAxiomTransformSelectedProof_of_staged_kernel_implication
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
    [axiomSoundnessCertificate haxiomProof].
  exists currentGlobalSigma, currentGlobalPi,
    nextAxiomSoundness, axiomSoundnessCertificate.
  split; [exact hadequateOrbit |].
  split; [exact htransform | exact haxiomProof].
Qed.

(** Reconstruct the public graph/proof pair from the retained selection.  No
    PA-satisfaction hypothesis is needed in this direction because both the
    semantic orbit/transform and represented proof are explicit outputs. *)
Theorem
    raw_dynamicTruthNativeStagedNextAxiomSoundnessCompiler_of_currentPackageProofCompiler
    : forall (M : RawPAModel),
  RawDynamicTruthNativeAxiomSoundnessCurrentPackageProofCompiler M ->
  RawDynamicTruthNativeStagedNextAxiomSoundnessCompiler M.
Proof.
  intros M hcompiler tail predecessorLevel
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent
    nextLocal localCertificate nextCrossLevel crossLevelCertificate
    nextShift shiftCertificate nextSubstitution substitutionCertificate
    hnextLocal hnextCrossLevel hnextShift hnextSubstitution.
  destruct
    (hcompiler tail predecessorLevel
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal hcurrent
      nextLocal localCertificate nextCrossLevel crossLevelCertificate
      nextShift shiftCertificate nextSubstitution substitutionCertificate
      hnextLocal hnextCrossLevel hnextShift hnextSubstitution) as
    (currentGlobalSigma & currentGlobalPi &
      nextAxiomSoundness & axiomSoundnessCertificate &
      hadequateOrbit & htransform & haxiomProof).
  exists nextAxiomSoundness, axiomSoundnessCertificate.
  unfold RawDynamicTruthNativeStagedNextAxiomSoundnessProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt.
  split; [|exact haxiomProof].
  apply (proj2
    (raw_sat_dynamicTruthNativeAxiomSoundnessPositiveGraph_iff
      M tail predecessorLevel nextAxiomSoundness)).
  exists currentGlobalSigma, currentGlobalPi.
  split; [|exact htransform].
  exact (proj1 (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff
      M tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi) hadequateOrbit)).
Qed.

(** Named compatibility factorization of the old premise through the exact
    current-package residual. *)
Corollary
    raw_dynamicTruthNativeStagedNextAxiomSoundnessCompiler_of_kernel_implication_via_currentPackage
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M ->
  RawDynamicTruthNativeStagedNextAxiomSoundnessCompiler M.
Proof.
  intros M hPA hkernel.
  apply
    raw_dynamicTruthNativeStagedNextAxiomSoundnessCompiler_of_currentPackageProofCompiler.
  exact
    (raw_dynamicTruthNativeAxiomSoundnessCurrentPackageProofCompiler_of_kernel_implication
      M hPA hkernel).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeAxiomSoundnessCurrentPackageCompilation.
