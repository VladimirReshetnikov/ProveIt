(**
  Public dependency-ordered callback for the native shift field.

  The staged shift root module already reduces the represented shift laws to
  one trace-linked implication root.  This file performs the remaining
  callback plumbing without adding a second mathematical premise.

  A callback invocation supplies the current six-field package and exact
  graph/proof pairs for the newly selected local and cross-level fields.  We
  first synchronize the local certificate with the current common context,
  then add the cross-level certificate through the committed witnessed-
  context accumulation theorem.  Thus every premise passed to the shift
  kernel is a local root over one literal context.

  Target selection retains one adequate paired-global orbit and one exact
  shift transform.  The same transform both establishes the public positive
  graph assertion and is passed to the staged proof theorem.  No equality
  between graph outputs, semantic truth-to-proof premise, or context
  identification is introduced.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeShiftPositiveGraph
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeShiftStagedRootCompilation
  RawCodedDynamicTruthNativeStagedPrerequisiteAccumulation.

Module PABoundedRawCodedDynamicTruthNativeShiftStagedCallbackCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeShiftPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeStagedPrerequisiteAccumulation.

(** ------------------------------------------------------------------
    Exact prerequisite accumulation from the callback inputs. *)

(** The helper consumes the complete graph/proof pairs presented by the
    public staged callback.  Only their proof projections are needed for
    context accumulation, but keeping the pairs in the statement fixes
    [nextLocal] and [nextCrossLevel] to the graph-selected targets. *)
Theorem
    raw_dynamicTruthNativeShiftStagedPrerequisites_of_callback_inputs :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal localCertificate nextCrossLevel crossLevelCertificate,
  RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal ->
  RawDynamicTruthNativeStagedNextLocalProofAt M
    tail level nextLocal localCertificate ->
  RawDynamicTruthNativeStagedNextCrossLevelProofAt M
    tail level nextCrossLevel crossLevelCertificate ->
  exists witnessList baseContext
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot : M,
    RawDynamicTruthNativeShiftStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot.
Proof.
  intros M hPA tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal localCertificate nextCrossLevel crossLevelCertificate
    hcurrent hlocal hcrossLevel.
  destruct
    (raw_dynamicTruthNativeCrossLevelStagedPrerequisites_of_current_and_local
      M hPA
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal localCertificate
      (proj2 hcurrent) (proj2 hlocal)) as
    (witnessList & baseContext & currentLocalRoot &
      currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & nextLocalRoot & hlocalPrerequisites).
  destruct
    (raw_dynamicTruthNativeShiftStagedPrerequisites_add_crossLevel
      M hPA witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot crossLevelCertificate
      hlocalPrerequisites (proj2 hcrossLevel)) as
    (mergedWitnessList & mergedContext & mergedCurrentLocalRoot &
      mergedCurrentCrossLevelRoot & mergedCurrentShiftRoot &
      mergedCurrentSubstitutionRoot & mergedCurrentAxiomSoundnessRoot &
      mergedCurrentFinalRoot & mergedNextLocalRoot &
      mergedNextCrossLevelRoot & hshiftPrerequisites).
  exists mergedWitnessList, mergedContext,
    mergedCurrentLocalRoot, mergedCurrentCrossLevelRoot,
    mergedCurrentShiftRoot, mergedCurrentSubstitutionRoot,
    mergedCurrentAxiomSoundnessRoot, mergedCurrentFinalRoot,
    mergedNextLocalRoot, mergedNextCrossLevelRoot.
  exact hshiftPrerequisites.
Qed.

(** ------------------------------------------------------------------
    One exact positive shift selection and proof. *)

(** Pointwise callback body.  The adequate orbit is not forgotten before
    the shift transform is built: both are passed unchanged to the existing
    graph-facing staged proof theorem. *)
Theorem raw_dynamicTruthNativeShiftStagedNextProof_exists :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M ->
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal localCertificate nextCrossLevel crossLevelCertificate,
  RawDynamicTruthNativeStagedPositiveCurrentAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal ->
  RawDynamicTruthNativeStagedNextLocalProofAt M
    tail level nextLocal localCertificate ->
  RawDynamicTruthNativeStagedNextCrossLevelProofAt M
    tail level nextCrossLevel crossLevelCertificate ->
  exists nextShift shiftCertificate : M,
    RawDynamicTruthNativeStagedNextShiftProofAt M
      tail level nextShift shiftCertificate.
Proof.
  intros M hPA hcompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal localCertificate nextCrossLevel crossLevelCertificate
    hcurrent hlocal hcrossLevel.
  destruct
    (raw_dynamicTruthNativeShiftStagedPrerequisites_of_callback_inputs
      M hPA tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal localCertificate nextCrossLevel crossLevelCertificate
      hcurrent hlocal hcrossLevel) as
    (witnessList & baseContext & currentLocalRoot &
      currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & nextLocalRoot & nextCrossLevelRoot &
      hprerequisites).

  (** Select one adequate paired-global orbit at the successor input level. *)
  destruct
    (dynamicTruthPairedGlobalFormulaCodeOrbitGraph_raw_adequate_total
      M hPA tail (raw_succ M level)) as
    (currentGlobalSigma & currentGlobalPi & horbit &
      hcurrentSigma & hcurrentPi).
  assert (hadequateOrbit :
      RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
        tail (raw_succ M level) currentGlobalSigma currentGlobalPi).
  {
    apply (proj2
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M tail
        (raw_succ M level) currentGlobalSigma currentGlobalPi)).
    split.
    - apply (proj1
        (raw_sat_dynamicTruthPairedGlobalFormulaCodeOrbitGraph_iff M tail
          (raw_succ M level) currentGlobalSigma currentGlobalPi)).
      exact horbit.
    - split; assumption.
  }

  (** Apply the native shift transform once.  Its target is used both below
      and in the positive graph witness; no independently selected graph
      output is compared with it. *)
  destruct
    (dynamicTruthNativeShiftFieldTransformGraph_raw_total_on_adequate
      M hPA tail currentGlobalSigma currentGlobalPi level
      hcurrentSigma hcurrentPi) as
    (nextShift & htransformSat & _hnextShiftAdequate).
  pose proof (proj1
    (raw_sat_dynamicTruthNativeShiftFieldTransformGraph_iff M tail
      currentGlobalSigma currentGlobalPi level nextShift)
    htransformSat) as htransform.
  destruct
    (raw_dynamicTruthNativeShiftStagedTransformProof_of_body_implication
      M hPA hcompiler tail level currentGlobalSigma currentGlobalPi
      nextShift witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot
      hadequateOrbit htransform hprerequisites) as
    [shiftCertificate hshiftCertificate].

  exists nextShift, shiftCertificate.
  unfold RawDynamicTruthNativeStagedNextShiftProofAt,
    RawDynamicTruthNativePositiveFieldOrdinaryProofAt.
  split; [|exact hshiftCertificate].
  apply (proj2 (raw_sat_dynamicTruthNativeShiftPositiveGraph_iff
    M tail level nextShift)).
  exists currentGlobalSigma, currentGlobalPi. split.
  - apply (proj1
      (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M tail
        (raw_succ M level) currentGlobalSigma currentGlobalPi)).
    exact hadequateOrbit.
  - exact htransform.
Qed.

(** Public dependency-ordered callback.  Its sole proof-producing premise is
    the trace-linked body-implication compiler from the staged shift kernel. *)
Corollary
    raw_dynamicTruthNativeStagedNextShiftCompiler_of_body_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M ->
  RawDynamicTruthNativeStagedNextShiftCompiler M.
Proof.
  intros M hPA hcompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrent
    nextLocal localCertificate nextCrossLevel crossLevelCertificate
    hlocal hcrossLevel.
  exact
    (raw_dynamicTruthNativeShiftStagedNextProof_exists
      M hPA hcompiler tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal localCertificate nextCrossLevel crossLevelCertificate
      hcurrent hlocal hcrossLevel).
Qed.

End PABoundedRawCodedDynamicTruthNativeShiftStagedCallbackCompilation.
