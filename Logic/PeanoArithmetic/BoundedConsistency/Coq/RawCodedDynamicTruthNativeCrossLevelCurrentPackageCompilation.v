(**
  A call-site exact residual for the native cross-level successor.

  The historical staged cross-level compiler is deliberately
  context-preserving, but its type is stronger than the public successor
  actually needs.  It must return an implication root for every tuple of
  seven formulas having local proofs in a witnessed context, even when those
  formulas are unrelated to the current master graph and to the next-local
  graph.  The public callback never presents such an arbitrary tuple: it has
  the exact current graph/proof package and the exact graph-selected ordinary
  proof of the next local field.

  This file records that smaller domain.  A compiler may inspect those two
  genuine packages, choose one adequate paired orbit and its exact
  cross-level transform, and return an ordinary proof of that selected field.
  The trace witnesses are retained in the output so that no graph truth is
  mistaken for proof syntax.  The old body-implication compiler supplies the
  new interface, while the new interface supplies the public staged callback
  directly.  Thus downstream developments can target the call-site residual
  without proving the stronger arbitrary-package implication interface.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeCrossLevelPositiveGraph
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation
  RawCodedDynamicTruthNativeCrossLevelStagedRootCompilation
  RawCodedDynamicTruthNativeStagedPrerequisiteAccumulation
  RawCodedDynamicTruthNativeCrossLevelStagedCallbackCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeCrossLevelCurrentPackageCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeStagedPrerequisiteAccumulation.
Import
  PABoundedRawCodedDynamicTruthNativeCrossLevelStagedCallbackCompilation.

(** The exact proof-producing operation used at the cross-level call site.

    Unlike [RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler],
    this property is not required to accept arbitrary formulas which merely
    happen to have seven local roots.  Its two inputs are the graph-linked
    current package and the graph-linked next-local certificate received by
    [RawDynamicTruthNativeStagedNextCrossLevelCompiler].  Its existential
    output also lets the construction choose the orbit and transform it uses;
    it is not required to prove every extensionally equivalent graph witness.
*)
Definition RawDynamicTruthNativeCrossLevelCurrentPackageProofCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
    RawDynamicTruthNativeStagedPositiveCurrentAt M tail predecessorLevel
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal ->
    forall nextLocal localCertificate,
      RawDynamicTruthNativeStagedNextLocalProofAt M
        tail predecessorLevel nextLocal localCertificate ->
      exists currentGlobalSigma currentGlobalPi
          nextCrossLevel crossLevelCertificate : M,
        RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
          tail (raw_succ M predecessorLevel)
          currentGlobalSigma currentGlobalPi /\
        RawDynamicTruthNativeCrossLevelFieldTransformAt M
          currentGlobalSigma currentGlobalPi predecessorLevel
          nextCrossLevel /\
        RawCodedPAProofOf M nextCrossLevel crossLevelCertificate.

Arguments RawDynamicTruthNativeCrossLevelCurrentPackageProofCompiler M
  : clear implicits.

(** Dropping the retained adequate-orbit witness recovers the public staged
    cross-level callback.  The converse is intentionally not claimed: an
    independently selected adequate orbit need not have the same transform
    output as the callback without an additional graph-functionality
    argument.  We state and use only the unconditional direction below.  The
    adapter from the historical compiler separately establishes the call-site
    domain reduction used downstream. *)

(** The stronger historical implication compiler supplies the call-site
    residual.  The proof deliberately keeps the graph-selected adequate orbit
    used by the transform, merges only the genuine next-local certificate into
    the genuine current package, and invokes the existing carried-field
    closer. *)
Theorem
    raw_dynamicTruthNativeCrossLevelCurrentPackageProofCompiler_of_body_implication
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M ->
  RawDynamicTruthNativeCrossLevelCurrentPackageProofCompiler M.
Proof.
  intros M hPA hbody tail predecessorLevel
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
      M hPA hbody tail predecessorLevel
      currentGlobalSigma currentGlobalPi nextCrossLevel
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot
      hadequateOrbit htransform hprerequisites) as
    [crossLevelCertificate hcrossLevelProof].
  exists currentGlobalSigma, currentGlobalPi,
    nextCrossLevel, crossLevelCertificate.
  repeat split; assumption.
Qed.

(** Package the retained orbit and transform as graph truth and expose the
    existing public callback.  This direction is law-free and does not need a
    PA-satisfaction hypothesis: the proof certificate is already an explicit
    output of the call-site compiler. *)
Theorem
    raw_dynamicTruthNativeStagedNextCrossLevelCompiler_of_currentPackageProofCompiler
    : forall (M : RawPAModel),
  RawDynamicTruthNativeCrossLevelCurrentPackageProofCompiler M ->
  RawDynamicTruthNativeStagedNextCrossLevelCompiler M.
Proof.
  intros M hcompiler tail predecessorLevel
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent
    nextLocal localCertificate hnextLocal.
  destruct (hcompiler tail predecessorLevel
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent
    nextLocal localCertificate hnextLocal) as
    (currentGlobalSigma & currentGlobalPi &
      nextCrossLevel & crossLevelCertificate &
      hadequateOrbit & htransform & hcrossLevelProof).
  exists nextCrossLevel, crossLevelCertificate.
  unfold RawDynamicTruthNativeStagedNextCrossLevelProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt.
  split; [|exact hcrossLevelProof].
  apply (proj2
    (raw_sat_dynamicTruthNativeCrossLevelPositiveGraph_iff
      M tail predecessorLevel nextCrossLevel)).
  exists currentGlobalSigma, currentGlobalPi.
  split; [|exact htransform].
  exact (proj1
    (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff
      M tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi) hadequateOrbit).
Qed.

(** A direct compatibility corollary records the full factorisation of the
    old premise through the smaller call-site residual. *)
Corollary
    raw_dynamicTruthNativeStagedNextCrossLevelCompiler_of_body_implication_via_currentPackage
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M ->
  RawDynamicTruthNativeStagedNextCrossLevelCompiler M.
Proof.
  intros M hPA hbody.
  apply
    raw_dynamicTruthNativeStagedNextCrossLevelCompiler_of_currentPackageProofCompiler.
  exact
    (raw_dynamicTruthNativeCrossLevelCurrentPackageProofCompiler_of_body_implication
      M hPA hbody).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeCrossLevelCurrentPackageCompilation.
