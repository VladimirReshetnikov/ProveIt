(**
  Dependency-ordered assembly of the native positive master successor.

  The older proof-total assembly asks for five field compilers which work in
  isolation and for a separate compact-consistency successor.  That is a
  convenient sufficient interface, but it is stronger than the staged Lean
  construction: later fields there are proved from the current certificate
  and from the fields already installed at this successor step.

  This file records that dependency order literally.  Each stage keeps the
  graph witness and the ordinary PA certificate indexed by the *same* target.
  The local stage sees the current six-field package; cross-level also sees
  local; shift also sees cross-level; substitution also sees shift; axiom
  soundness also sees substitution; and the final compact field sees all five
  earlier outputs.  The last stage produces the compact target directly, so
  no [RawRestrictedPAConsistencyCertificateSuccessor] is assumed here.

  Six independently produced ordinary certificates are synchronized only at
  the endpoint, using the completed witnessed-context merge transport.  This
  is structural assembly: it does not erase a context, identify two graph
  outputs, or convert semantic truth into a proof.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPALocalProofExistential
  RawCodedPAProvability
  CompactRestrictedPAConsistencyFormulaCodeGraph
  CompactPAUniformProvability
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedTruthCertificateMasterSuccessorBridge
  RawCodedDynamicTruthMasterSplicedSuccessorBridge
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeCrossLevelPositiveGraph
  RawCodedDynamicTruthNativeShiftPositiveGraph
  RawCodedDynamicTruthNativeSubstitutionPositiveGraph
  RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph
  RawCodedDynamicTruthNativeMasterEndpoint
  RawCodedDynamicTruthNativeMasterSuccessorFromProofTotals
  RawCodedPALocalProofWitnessedContextMergeTransportComplete.

Module PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAProvability.
Import PABoundedCompactRestrictedPAConsistencyFormulaCodeGraph.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedTruthCertificateMasterSuccessorBridge.
Import PABoundedRawCodedDynamicTruthMasterSplicedSuccessorBridge.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeShiftPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeMasterEndpoint.
Import PABoundedRawCodedDynamicTruthNativeMasterSuccessorFromProofTotals.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.

(** The exact current input presented by the native component successor.
    Keeping graph and proof packages together prevents a staged callback from
    silently changing either the six selected targets or their shared
    witnessed PA context. *)
Definition RawDynamicTruthNativeStagedPositiveCurrentAt
    (M : RawPAModel) (tail : nat -> M) (level : M)
    (currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal : M) : Prop :=
  RawSixFieldMasterGraphWitnessesAt M
    dynamicTruthNativeSplicedLocalFieldGraph
    dynamicTruthNativeSplicedCrossLevelFieldGraph
    dynamicTruthNativeSplicedShiftFieldGraph
    dynamicTruthNativeSplicedSubstitutionFieldGraph
    dynamicTruthNativeSplicedAxiomSoundnessFieldGraph
    tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal /\
  RawSixFieldMasterCommonContextProofsOf M
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal.

Arguments RawDynamicTruthNativeStagedPositiveCurrentAt
  M tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal : clear implicits.

(** A positive-field stage always returns one graph-selected target and one
    ordinary PA certificate of exactly that target.  The five named aliases
    below fix the graph, while retaining the common shape explicitly. *)
Definition RawDynamicTruthNativePositiveFieldOrdinaryProofAt
    (M : RawPAModel) (positiveGraph : formula)
    (tail : nat -> M) (level target certificate : M) : Prop :=
  raw_formula_sat M
    (scons M target (scons M level tail)) positiveGraph /\
  RawCodedPAProofOf M target certificate.

Arguments RawDynamicTruthNativePositiveFieldOrdinaryProofAt
  M positiveGraph tail level target certificate : clear implicits.

Definition RawDynamicTruthNativeStagedNextLocalProofAt
    (M : RawPAModel) (tail : nat -> M) (level target certificate : M)
    : Prop :=
  RawDynamicTruthNativePositiveFieldOrdinaryProofAt M
    dynamicTruthNativeLocalPositiveGraph
    tail level target certificate.

Arguments RawDynamicTruthNativeStagedNextLocalProofAt
  M tail level target certificate : clear implicits.

Definition RawDynamicTruthNativeStagedNextCrossLevelProofAt
    (M : RawPAModel) (tail : nat -> M) (level target certificate : M)
    : Prop :=
  RawDynamicTruthNativePositiveFieldOrdinaryProofAt M
    dynamicTruthNativeCrossLevelPositiveGraph
    tail level target certificate.

Arguments RawDynamicTruthNativeStagedNextCrossLevelProofAt
  M tail level target certificate : clear implicits.

Definition RawDynamicTruthNativeStagedNextShiftProofAt
    (M : RawPAModel) (tail : nat -> M) (level target certificate : M)
    : Prop :=
  RawDynamicTruthNativePositiveFieldOrdinaryProofAt M
    dynamicTruthNativeShiftPositiveGraph
    tail level target certificate.

Arguments RawDynamicTruthNativeStagedNextShiftProofAt
  M tail level target certificate : clear implicits.

Definition RawDynamicTruthNativeStagedNextSubstitutionProofAt
    (M : RawPAModel) (tail : nat -> M) (level target certificate : M)
    : Prop :=
  RawDynamicTruthNativePositiveFieldOrdinaryProofAt M
    dynamicTruthNativeSubstitutionPositiveGraph
    tail level target certificate.

Arguments RawDynamicTruthNativeStagedNextSubstitutionProofAt
  M tail level target certificate : clear implicits.

Definition RawDynamicTruthNativeStagedNextAxiomSoundnessProofAt
    (M : RawPAModel) (tail : nat -> M) (level target certificate : M)
    : Prop :=
  RawDynamicTruthNativePositiveFieldOrdinaryProofAt M
    dynamicTruthNativeAxiomSoundnessPositiveGraph
    tail level target certificate.

Arguments RawDynamicTruthNativeStagedNextAxiomSoundnessProofAt
  M tail level target certificate : clear implicits.

(** Unlike the first five stages, the final graph is already indexed by the
    actual successor [S level].  Naming this distinction avoids the common
    off-by-one mistake in a hand-written master successor. *)
Definition RawDynamicTruthNativeStagedNextFinalProofAt
    (M : RawPAModel) (tail : nat -> M) (level target certificate : M)
    : Prop :=
  raw_formula_sat M
    (scons M target (scons M (raw_succ M level) tail))
    compactRestrictedPAConsistencyFormulaCodeGraph /\
  RawCodedPAProofOf M target certificate.

Arguments RawDynamicTruthNativeStagedNextFinalProofAt
  M tail level target certificate : clear implicits.

(** The first proof-producing callback. *)
Definition RawDynamicTruthNativeStagedNextLocalCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
    RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal ->
    exists nextLocal localCertificate : M,
      RawDynamicTruthNativeStagedNextLocalProofAt M
        tail level nextLocal localCertificate.

Arguments RawDynamicTruthNativeStagedNextLocalCompiler M : clear implicits.

(** Cross-level may use the current package and the exact local target and
    certificate selected immediately before it. *)
Definition RawDynamicTruthNativeStagedNextCrossLevelCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
    RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal ->
    forall nextLocal localCertificate,
      RawDynamicTruthNativeStagedNextLocalProofAt M
        tail level nextLocal localCertificate ->
      exists nextCrossLevel crossLevelCertificate : M,
        RawDynamicTruthNativeStagedNextCrossLevelProofAt M
          tail level nextCrossLevel crossLevelCertificate.

Arguments RawDynamicTruthNativeStagedNextCrossLevelCompiler M
  : clear implicits.

(** Shift sees both preceding successor fields. *)
Definition RawDynamicTruthNativeStagedNextShiftCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
    RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal ->
    forall nextLocal localCertificate nextCrossLevel crossLevelCertificate,
      RawDynamicTruthNativeStagedNextLocalProofAt M
        tail level nextLocal localCertificate ->
      RawDynamicTruthNativeStagedNextCrossLevelProofAt M
        tail level nextCrossLevel crossLevelCertificate ->
      exists nextShift shiftCertificate : M,
        RawDynamicTruthNativeStagedNextShiftProofAt M
          tail level nextShift shiftCertificate.

Arguments RawDynamicTruthNativeStagedNextShiftCompiler M : clear implicits.

(** Substitution sees the local, cross-level, and shift outputs. *)
Definition RawDynamicTruthNativeStagedNextSubstitutionCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
    RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal ->
    forall nextLocal localCertificate nextCrossLevel crossLevelCertificate
      nextShift shiftCertificate,
      RawDynamicTruthNativeStagedNextLocalProofAt M
        tail level nextLocal localCertificate ->
      RawDynamicTruthNativeStagedNextCrossLevelProofAt M
        tail level nextCrossLevel crossLevelCertificate ->
      RawDynamicTruthNativeStagedNextShiftProofAt M
        tail level nextShift shiftCertificate ->
      exists nextSubstitution substitutionCertificate : M,
        RawDynamicTruthNativeStagedNextSubstitutionProofAt M
          tail level nextSubstitution substitutionCertificate.

Arguments RawDynamicTruthNativeStagedNextSubstitutionCompiler M
  : clear implicits.

(** The soundness stage sees all four preceding positive outputs. *)
Definition RawDynamicTruthNativeStagedNextAxiomSoundnessCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
    RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal ->
    forall nextLocal localCertificate nextCrossLevel crossLevelCertificate
      nextShift shiftCertificate nextSubstitution substitutionCertificate,
      RawDynamicTruthNativeStagedNextLocalProofAt M
        tail level nextLocal localCertificate ->
      RawDynamicTruthNativeStagedNextCrossLevelProofAt M
        tail level nextCrossLevel crossLevelCertificate ->
      RawDynamicTruthNativeStagedNextShiftProofAt M
        tail level nextShift shiftCertificate ->
      RawDynamicTruthNativeStagedNextSubstitutionProofAt M
        tail level nextSubstitution substitutionCertificate ->
      exists nextAxiomSoundness axiomSoundnessCertificate : M,
        RawDynamicTruthNativeStagedNextAxiomSoundnessProofAt M
          tail level nextAxiomSoundness axiomSoundnessCertificate.

Arguments RawDynamicTruthNativeStagedNextAxiomSoundnessCompiler M
  : clear implicits.

(** The final stage is deliberately phrased as a direct graph-and-proof
    producer.  It can use the whole dependency prefix and is not replaced by
    the stronger, context-free consistency-certificate successor API. *)
Definition RawDynamicTruthNativeStagedNextFinalCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
    RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal ->
    forall nextLocal localCertificate nextCrossLevel crossLevelCertificate
      nextShift shiftCertificate nextSubstitution substitutionCertificate
      nextAxiomSoundness axiomSoundnessCertificate,
      RawDynamicTruthNativeStagedNextLocalProofAt M
        tail level nextLocal localCertificate ->
      RawDynamicTruthNativeStagedNextCrossLevelProofAt M
        tail level nextCrossLevel crossLevelCertificate ->
      RawDynamicTruthNativeStagedNextShiftProofAt M
        tail level nextShift shiftCertificate ->
      RawDynamicTruthNativeStagedNextSubstitutionProofAt M
        tail level nextSubstitution substitutionCertificate ->
      RawDynamicTruthNativeStagedNextAxiomSoundnessProofAt M
        tail level nextAxiomSoundness axiomSoundnessCertificate ->
      exists nextFinal finalCertificate : M,
        RawDynamicTruthNativeStagedNextFinalProofAt M
          tail level nextFinal finalCertificate.

Arguments RawDynamicTruthNativeStagedNextFinalCompiler M : clear implicits.

(** A modular bundle of the six callbacks.  Each later callback is allowed
    to inspect all earlier graph/proof pairs, exactly matching the staged
    certificate order. *)
Definition RawDynamicTruthNativeDependencyOrderedPositiveCallbacks
    (M : RawPAModel) : Prop :=
  RawDynamicTruthNativeStagedNextLocalCompiler M /\
  RawDynamicTruthNativeStagedNextCrossLevelCompiler M /\
  RawDynamicTruthNativeStagedNextShiftCompiler M /\
  RawDynamicTruthNativeStagedNextSubstitutionCompiler M /\
  RawDynamicTruthNativeStagedNextAxiomSoundnessCompiler M /\
  RawDynamicTruthNativeStagedNextFinalCompiler M.

Arguments RawDynamicTruthNativeDependencyOrderedPositiveCallbacks M
  : clear implicits.

(** The weakest single callback needed by structural assembly.  Its nested
    existential shape lets every target and certificate depend on all
    witnesses chosen before it; no stage is required to work independently
    of that concrete prefix. *)
Definition RawDynamicTruthNativeStagedPositiveOrdinarySuccessor
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
    RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal ->
    exists nextLocal localCertificate : M,
      RawDynamicTruthNativeStagedNextLocalProofAt M
        tail level nextLocal localCertificate /\
    exists nextCrossLevel crossLevelCertificate : M,
      RawDynamicTruthNativeStagedNextCrossLevelProofAt M
        tail level nextCrossLevel crossLevelCertificate /\
    exists nextShift shiftCertificate : M,
      RawDynamicTruthNativeStagedNextShiftProofAt M
        tail level nextShift shiftCertificate /\
    exists nextSubstitution substitutionCertificate : M,
      RawDynamicTruthNativeStagedNextSubstitutionProofAt M
        tail level nextSubstitution substitutionCertificate /\
    exists nextAxiomSoundness axiomSoundnessCertificate : M,
      RawDynamicTruthNativeStagedNextAxiomSoundnessProofAt M
        tail level nextAxiomSoundness axiomSoundnessCertificate /\
    exists nextFinal finalCertificate : M,
      RawDynamicTruthNativeStagedNextFinalProofAt M
        tail level nextFinal finalCertificate.

Arguments RawDynamicTruthNativeStagedPositiveOrdinarySuccessor M
  : clear implicits.

(** Sequentially invoke the modular callbacks to obtain the exact nested
    staged callback.  Notice that every invocation receives the unchanged
    current package and all earlier graph/proof pairs. *)
Theorem
    raw_dynamicTruthNativeStagedPositiveOrdinarySuccessor_of_callbacks :
    forall (M : RawPAModel),
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacks M ->
  RawDynamicTruthNativeStagedPositiveOrdinarySuccessor M.
Proof.
  intros M
    (hlocalCompiler & hcrossCompiler & hshiftCompiler &
      hsubstitutionCompiler & haxiomSoundnessCompiler & hfinalCompiler).
  intros tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal hcurrent.
  destruct (hlocalCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent) as
    (nextLocal & localCertificate & hnextLocal).
  destruct (hcrossCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent
    nextLocal localCertificate hnextLocal) as
    (nextCrossLevel & crossLevelCertificate & hnextCrossLevel).
  destruct (hshiftCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent
    nextLocal localCertificate nextCrossLevel crossLevelCertificate
    hnextLocal hnextCrossLevel) as
    (nextShift & shiftCertificate & hnextShift).
  destruct (hsubstitutionCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent
    nextLocal localCertificate nextCrossLevel crossLevelCertificate
    nextShift shiftCertificate hnextLocal hnextCrossLevel hnextShift) as
    (nextSubstitution & substitutionCertificate & hnextSubstitution).
  destruct (haxiomSoundnessCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent
    nextLocal localCertificate nextCrossLevel crossLevelCertificate
    nextShift shiftCertificate nextSubstitution substitutionCertificate
    hnextLocal hnextCrossLevel hnextShift hnextSubstitution) as
    (nextAxiomSoundness & axiomSoundnessCertificate &
      hnextAxiomSoundness).
  destruct (hfinalCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent
    nextLocal localCertificate nextCrossLevel crossLevelCertificate
    nextShift shiftCertificate nextSubstitution substitutionCertificate
    nextAxiomSoundness axiomSoundnessCertificate
    hnextLocal hnextCrossLevel hnextShift hnextSubstitution
    hnextAxiomSoundness) as
    (nextFinal & finalCertificate & hnextFinal).
  exists nextLocal, localCertificate. split; [exact hnextLocal |].
  exists nextCrossLevel, crossLevelCertificate.
  split; [exact hnextCrossLevel |].
  exists nextShift, shiftCertificate. split; [exact hnextShift |].
  exists nextSubstitution, substitutionCertificate.
  split; [exact hnextSubstitution |].
  exists nextAxiomSoundness, axiomSoundnessCertificate.
  split; [exact hnextAxiomSoundness |].
  exists nextFinal, finalCertificate. exact hnextFinal.
Qed.

(** Structural endpoint adapter.  The nested callback supplies six exact
    graph/proof pairs.  The completed common-context lift is applied once to
    those same targets, after which they are precisely the witnesses required
    by [RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor]. *)
Theorem
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_staged_ordinary
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeStagedPositiveOrdinarySuccessor M ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor M.
Proof.
  intros M hPA hstaged.
  intros tail level currentLocal currentCrossLevel currentShift
    currentSubstitution currentAxiomSoundness currentFinal
    hcurrentGraphs hcurrentProofs.
  assert (hcurrent :
      RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal).
  {
    split; assumption.
  }
  destruct (hstaged tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent) as
    (nextLocal & localCertificate & hnextLocal &
      nextCrossLevel & crossLevelCertificate & hnextCrossLevel &
      nextShift & shiftCertificate & hnextShift &
      nextSubstitution & substitutionCertificate & hnextSubstitution &
      nextAxiomSoundness & axiomSoundnessCertificate &
      hnextAxiomSoundness & nextFinal & finalCertificate & hnextFinal).
  exists nextLocal, nextCrossLevel, nextShift, nextSubstitution,
    nextAxiomSoundness, nextFinal.
  split.
  - unfold RawDynamicTruthSplicedMasterPositiveGraphWitnessesAt.
    unfold RawDynamicTruthNativeStagedNextLocalProofAt,
      RawDynamicTruthNativeStagedNextCrossLevelProofAt,
      RawDynamicTruthNativeStagedNextShiftProofAt,
      RawDynamicTruthNativeStagedNextSubstitutionProofAt,
      RawDynamicTruthNativeStagedNextAxiomSoundnessProofAt,
      RawDynamicTruthNativePositiveFieldOrdinaryProofAt in *.
    unfold RawDynamicTruthNativeStagedNextFinalProofAt in hnextFinal.
    destruct hnextLocal as [hnextLocalGraph hnextLocalProof].
    destruct hnextCrossLevel as [hnextCrossGraph hnextCrossProof].
    destruct hnextShift as [hnextShiftGraph hnextShiftProof].
    destruct hnextSubstitution as
      [hnextSubstitutionGraph hnextSubstitutionProof].
    destruct hnextAxiomSoundness as
      [hnextAxiomSoundnessGraph hnextAxiomSoundnessProof].
    destruct hnextFinal as [hnextFinalGraph hnextFinalProof].
    repeat split; assumption.
  - (* Re-open the six stage pairs.  They are ordinary certificates of the
       exact graph outputs, so the completed merge theorem can synchronize
       their hidden witnessed contexts without changing a target. *)
    unfold RawDynamicTruthNativeStagedNextLocalProofAt,
      RawDynamicTruthNativeStagedNextCrossLevelProofAt,
      RawDynamicTruthNativeStagedNextShiftProofAt,
      RawDynamicTruthNativeStagedNextSubstitutionProofAt,
      RawDynamicTruthNativeStagedNextAxiomSoundnessProofAt,
      RawDynamicTruthNativePositiveFieldOrdinaryProofAt in *.
    unfold RawDynamicTruthNativeStagedNextFinalProofAt in hnextFinal.
    destruct hnextLocal as [hnextLocalGraph hnextLocalProof].
    destruct hnextCrossLevel as [hnextCrossGraph hnextCrossProof].
    destruct hnextShift as [hnextShiftGraph hnextShiftProof].
    destruct hnextSubstitution as
      [hnextSubstitutionGraph hnextSubstitutionProof].
    destruct hnextAxiomSoundness as
      [hnextAxiomSoundnessGraph hnextAxiomSoundnessProof].
    destruct hnextFinal as [hnextFinalGraph hnextFinalProof].
    apply (raw_sixFieldMasterOrdinaryProofsCommonContextLift_complete
      M hPA nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal).
    unfold RawSixFieldMasterOrdinaryProofsOf.
    exists localCertificate, crossLevelCertificate, shiftCertificate,
      substitutionCertificate, axiomSoundnessCertificate, finalCertificate.
    repeat split; assumption.
Qed.

(** Public adapter from the modular dependency-ordered callbacks. *)
Corollary
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_dependency_ordered_callbacks
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacks M ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor M.
Proof.
  intros M hPA hcallbacks.
  exact
    (raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_staged_ordinary
      M hPA
      (raw_dynamicTruthNativeStagedPositiveOrdinarySuccessor_of_callbacks
        M hcallbacks)).
Qed.

Definition
    RawDynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawDynamicTruthNativeDependencyOrderedPositiveCallbacks M.

(** All-model specialization used by the native endpoint.  This concludes
    only the exact successor callback; proving the six staged compilers is
    intentionally left as the visible arithmetic proof obligation. *)
Corollary
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessorInAllModels_of_dependency_ordered_callbacks
    :
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessorInAllModels.
Proof.
  intros hcallbacks M hPA.
  exact
    (raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_dependency_ordered_callbacks
      M hPA (hcallbacks M hPA)).
Qed.

(** The exact non-circular headline boundary.  Everything after the six
    dependency-ordered proof producers—context synchronization, master
    assembly, represented induction, and final-field projection—is already
    discharged by the native endpoint. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_callbacks
    :
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hcallbacks.
  apply
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_native_compiler.
  exact
    (raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessorInAllModels_of_dependency_ordered_callbacks
      hcallbacks).
Qed.

End PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
