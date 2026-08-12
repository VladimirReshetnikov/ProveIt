(**
  A call-site exact residual for the native substitution successor.

  The historical staged substitution compiler accepts an arbitrary linked
  nine-root package and an arbitrary compatible substitution trace.  The
  public successor never calls it on such free-standing data.  Its inputs
  are the genuine current six-field package together with the exact local,
  cross-level, and shift graph/proof pairs already selected by the preceding
  callbacks.

  This module restricts the compiler to that genuine call-site domain.  The
  result retains the one adequate paired orbit and exact substitution
  transform used to select the output, alongside an ordinary represented PA
  proof of that output.  Consequently the reduced compiler reconstructs the
  public graph assertion without any graph-functionality comparison or
  semantic truth-to-proof conversion.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeSubstitutionPositiveGraph
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeSubstitutionStagedRootCompilation
  RawCodedDynamicTruthNativeStagedPrerequisiteAccumulation
  RawCodedDynamicTruthNativeSubstitutionStagedCallbackCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeSubstitutionCurrentPackageCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeStagedPrerequisiteAccumulation.
Import
  PABoundedRawCodedDynamicTruthNativeSubstitutionStagedCallbackCompilation.

(** The exact proof-producing operation used at the substitution call site.

    In contrast with
    [RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler],
    the quantified roots here cannot be chosen independently of the native
    master graph.  They arrive only through the three public predecessor
    certificates and the graph-linked current package. *)
Definition RawDynamicTruthNativeSubstitutionCurrentPackageProofCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
    RawDynamicTruthNativeStagedPositiveCurrentAt M tail predecessorLevel
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal ->
    forall nextLocal localCertificate nextCrossLevel crossLevelCertificate
      nextShift shiftCertificate,
      RawDynamicTruthNativeStagedNextLocalProofAt M
        tail predecessorLevel nextLocal localCertificate ->
      RawDynamicTruthNativeStagedNextCrossLevelProofAt M
        tail predecessorLevel nextCrossLevel crossLevelCertificate ->
      RawDynamicTruthNativeStagedNextShiftProofAt M
        tail predecessorLevel nextShift shiftCertificate ->
      exists currentGlobalSigma currentGlobalPi
          nextSubstitution substitutionCertificate : M,
        RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
          tail (raw_succ M predecessorLevel)
          currentGlobalSigma currentGlobalPi /\
        RawDynamicTruthNativeSubstitutionFieldTransformAt M
          currentGlobalSigma currentGlobalPi predecessorLevel
          nextSubstitution /\
        RawCodedPAProofOf M nextSubstitution substitutionCertificate.

Arguments RawDynamicTruthNativeSubstitutionCurrentPackageProofCompiler M
  : clear implicits.

(** The stronger historical implication compiler supplies the exact
    call-site residual.  The proof accumulates only the three certificates
    which the public callback actually receives and retains the literal orbit
    and transform selected by the existing graph-selection theorem. *)
Theorem
    raw_dynamicTruthNativeSubstitutionCurrentPackageProofCompiler_of_body_implication
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler
    M ->
  RawDynamicTruthNativeSubstitutionCurrentPackageProofCompiler M.
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
      hadequateOrbit & htransform & _hnextSubstitutionGraph).

  (** Synchronize the current package with the next-local certificate. *)
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

  (** Add the graph-linked cross-level certificate, transporting all seven
      roots into the returned witnessed context. *)
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

  (** Add the graph-linked shift certificate.  This is the exact nine-root
      package seen at the public substitution call site. *)
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
  exists currentGlobalSigma, currentGlobalPi,
    nextSubstitution, substitutionCertificate.
  split; [exact hadequateOrbit |].
  split; [exact htransform | exact hsubstitutionProof].
Qed.

(** Reconstruct the public graph/proof pair from the retained selection.  No
    PA hypothesis is needed because the reduced compiler has already supplied
    both the semantic graph witnesses and the represented proof certificate. *)
Theorem
    raw_dynamicTruthNativeStagedNextSubstitutionCompiler_of_currentPackageProofCompiler
    : forall (M : RawPAModel),
  RawDynamicTruthNativeSubstitutionCurrentPackageProofCompiler M ->
  RawDynamicTruthNativeStagedNextSubstitutionCompiler M.
Proof.
  intros M hcompiler tail predecessorLevel
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent
    nextLocal localCertificate nextCrossLevel crossLevelCertificate
    nextShift shiftCertificate hnextLocal hnextCrossLevel hnextShift.
  destruct
    (hcompiler tail predecessorLevel
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal hcurrent
      nextLocal localCertificate nextCrossLevel crossLevelCertificate
      nextShift shiftCertificate hnextLocal hnextCrossLevel hnextShift) as
    (currentGlobalSigma & currentGlobalPi &
      nextSubstitution & substitutionCertificate &
      hadequateOrbit & htransform & hsubstitutionProof).
  exists nextSubstitution, substitutionCertificate.
  unfold RawDynamicTruthNativeStagedNextSubstitutionProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt.
  split; [|exact hsubstitutionProof].
  apply (proj2
    (raw_sat_dynamicTruthNativeSubstitutionPositiveGraph_iff
      M tail predecessorLevel nextSubstitution)).
  exists currentGlobalSigma, currentGlobalPi.
  split; [|exact htransform].
  exact (proj1 (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff
      M tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi) hadequateOrbit)).
Qed.

(** Named compatibility factorisation from the historical premise to the
    public callback through the smaller call-site residual. *)
Corollary
    raw_dynamicTruthNativeStagedNextSubstitutionCompiler_of_body_implication_via_currentPackage
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler
    M ->
  RawDynamicTruthNativeStagedNextSubstitutionCompiler M.
Proof.
  intros M hPA hbody.
  apply
    raw_dynamicTruthNativeStagedNextSubstitutionCompiler_of_currentPackageProofCompiler.
  exact
    (raw_dynamicTruthNativeSubstitutionCurrentPackageProofCompiler_of_body_implication
      M hPA hbody).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeSubstitutionCurrentPackageCompilation.
