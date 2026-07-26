(**
  A component-facing successor bridge for the five spliced dynamic fields.

  The public master successor receives an opaque current master code and an
  exact proof certificate.  The component projection module recovers the six
  graph-selected current coordinates and their proof roots in one witnessed
  PA context.  A dependency-ordered dynamic compiler should work at that
  level of detail, not decode an arbitrary certificate again.

  At the next master index [S level], each [dynamicLocalFieldGraph] reduces
  exactly to its positive graph evaluated at predecessor [level].  The
  interface below therefore asks a client only for five positive graph
  witnesses, the compact final-field witness at [S level], and six next proofs
  sharing one context.  This module performs all current-package projection
  and zero/successor-splice bookkeeping needed to recover the standard master
  successor callback.

  No positive field is constructed here.  The exported premise is the exact
  staged compiler obligation still to be discharged.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CompactRestrictedPAConsistencyFormulaCodeGraph
  RawCodedDynamicLocalFieldGraph
  RawCodedDynamicTruthLocalDecisionExclusiveBase
  RawCodedDynamicTruthTransportFieldBaseGraphs
  RawCodedDynamicTruthAxiomSoundnessBaseGraph
  RawCodedDynamicTruthMasterSplicedBasePackage
  RawCodedTruthCertificateMasterInduction
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedTruthCertificateMasterSuccessorBridge
  RawCodedTruthCertificateMasterComponentProjection.

Module PABoundedRawCodedDynamicTruthMasterSplicedSuccessorBridge.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCompactRestrictedPAConsistencyFormulaCodeGraph.
Import PABoundedRawCodedDynamicLocalFieldGraph.
Import PABoundedRawCodedDynamicTruthLocalDecisionExclusiveBase.
Import PABoundedRawCodedDynamicTruthTransportFieldBaseGraphs.
Import PABoundedRawCodedDynamicTruthAxiomSoundnessBaseGraph.
Import PABoundedRawCodedDynamicTruthMasterSplicedBasePackage.
Import PABoundedRawCodedTruthCertificateMasterInduction.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedTruthCertificateMasterSuccessorBridge.
Import PABoundedRawCodedTruthCertificateMasterComponentProjection.

(** The graph witnesses a staged compiler must return at one positive step.
    The first five graphs are read at predecessor [level]; the forced compact
    target is already read at the actual next index [S level]. *)
Definition RawDynamicTruthSplicedMasterPositiveGraphWitnessesAt
    (M : RawPAModel)
    (localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
      substitutionPositiveGraph axiomSoundnessPositiveGraph : formula)
    (tail : nat -> M) (level : M)
    (localField crossLevelField shiftField substitutionField
      axiomSoundnessField finalField : M) : Prop :=
  raw_formula_sat M
    (scons M localField (scons M level tail)) localPositiveGraph /\
  raw_formula_sat M
    (scons M crossLevelField (scons M level tail))
    crossLevelPositiveGraph /\
  raw_formula_sat M
    (scons M shiftField (scons M level tail)) shiftPositiveGraph /\
  raw_formula_sat M
    (scons M substitutionField (scons M level tail))
    substitutionPositiveGraph /\
  raw_formula_sat M
    (scons M axiomSoundnessField (scons M level tail))
    axiomSoundnessPositiveGraph /\
  raw_formula_sat M
    (scons M finalField (scons M (raw_succ M level) tail))
    compactRestrictedPAConsistencyFormulaCodeGraph.

Arguments RawDynamicTruthSplicedMasterPositiveGraphWitnessesAt
  M localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
    substitutionPositiveGraph axiomSoundnessPositiveGraph tail level
    localField crossLevelField shiftField substitutionField
    axiomSoundnessField finalField : clear implicits.

(** Exact dependency-ordered compiler interface.  Current proofs and next
    proofs are both explicitly common-context packages.  The two contexts may
    differ—the compiler may honestly grow a witnessed PA base—but arbitrary
    independent proof certificates cannot be silently merged. *)
Definition RawDynamicTruthSplicedMasterRawPositiveComponentSuccessor
    (M : RawPAModel)
    (localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
      substitutionPositiveGraph axiomSoundnessPositiveGraph : formula)
    : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal,
    RawSixFieldMasterGraphWitnessesAt M
      (dynamicTruthSplicedLocalFieldGraph localPositiveGraph)
      (dynamicTruthSplicedCrossLevelFieldGraph crossLevelPositiveGraph)
      (dynamicTruthSplicedShiftFieldGraph shiftPositiveGraph)
      (dynamicTruthSplicedSubstitutionFieldGraph
        substitutionPositiveGraph)
      (dynamicTruthSplicedAxiomSoundnessFieldGraph
        axiomSoundnessPositiveGraph)
      tail level currentLocal currentCrossLevel currentShift
      currentSubstitution currentAxiomSoundness currentFinal ->
    RawSixFieldMasterCommonContextProofsOf M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal ->
    exists nextLocal nextCrossLevel nextShift nextSubstitution
        nextAxiomSoundness nextFinal : M,
      RawDynamicTruthSplicedMasterPositiveGraphWitnessesAt M
        localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
        substitutionPositiveGraph axiomSoundnessPositiveGraph
        tail level nextLocal nextCrossLevel nextShift nextSubstitution
        nextAxiomSoundness nextFinal /\
      RawSixFieldMasterCommonContextProofsOf M
        nextLocal nextCrossLevel nextShift nextSubstitution
        nextAxiomSoundness nextFinal.

Arguments RawDynamicTruthSplicedMasterRawPositiveComponentSuccessor
  M localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
    substitutionPositiveGraph axiomSoundnessPositiveGraph : clear implicits.

(** Lift the staged component interface to the public raw-component
    successor.  Current fields are recovered from the exact graph/proof pair;
    next positive witnesses are transported through the five successor views. *)
Theorem
    raw_dynamicTruthSplicedMasterRawComponentSuccessor_of_positive_components
  : forall (M : RawPAModel), RawPASatisfies M -> forall
      localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
      substitutionPositiveGraph axiomSoundnessPositiveGraph,
  RawDynamicTruthSplicedMasterRawPositiveComponentSuccessor M
    localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
    substitutionPositiveGraph axiomSoundnessPositiveGraph ->
  RawSixFieldMasterRawComponentSuccessor M
    (dynamicTruthSplicedLocalFieldGraph localPositiveGraph)
    (dynamicTruthSplicedCrossLevelFieldGraph crossLevelPositiveGraph)
    (dynamicTruthSplicedShiftFieldGraph shiftPositiveGraph)
    (dynamicTruthSplicedSubstitutionFieldGraph substitutionPositiveGraph)
    (dynamicTruthSplicedAxiomSoundnessFieldGraph
      axiomSoundnessPositiveGraph).
Proof.
  intros M hPA localPositiveGraph crossLevelPositiveGraph
    shiftPositiveGraph substitutionPositiveGraph
    axiomSoundnessPositiveGraph hcompiler.
  intros tail level currentMaster currentCertificate
    hcurrentGraph hcurrentProof.
  destruct
    (raw_sixFieldMaster_current_components_of_graph_and_proof M hPA
      (dynamicTruthSplicedLocalFieldGraph localPositiveGraph)
      (dynamicTruthSplicedCrossLevelFieldGraph crossLevelPositiveGraph)
      (dynamicTruthSplicedShiftFieldGraph shiftPositiveGraph)
      (dynamicTruthSplicedSubstitutionFieldGraph
        substitutionPositiveGraph)
      (dynamicTruthSplicedAxiomSoundnessFieldGraph
        axiomSoundnessPositiveGraph)
      tail level currentMaster currentCertificate
      hcurrentGraph hcurrentProof) as
    (currentLocal & currentCrossLevel & currentShift &
      currentSubstitution & currentAxiomSoundness & currentFinal &
      hcurrentGraphs & hcurrentProofs).
  destruct (hcompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal hcurrentGraphs hcurrentProofs) as
    (nextLocal & nextCrossLevel & nextShift & nextSubstitution &
      nextAxiomSoundness & nextFinal & hpositive & hnextProofs).
  exists nextLocal, nextCrossLevel, nextShift, nextSubstitution,
    nextAxiomSoundness, nextFinal.
  split; [| exact hnextProofs].
  unfold RawDynamicTruthSplicedMasterPositiveGraphWitnessesAt in hpositive.
  destruct hpositive as
    (hlocal & hcross & hshift & hsubstitution & haxiom & hfinal).
  unfold RawSixFieldMasterGraphWitnessesAt.
  repeat split.
  - apply (proj2 (raw_dynamicLocalFieldGraph_succ_iff M hPA
      dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph
      localPositiveGraph tail level nextLocal)).
    exact hlocal.
  - apply (proj2 (raw_dynamicLocalFieldGraph_succ_iff M hPA
      dynamicTruthCrossLevelBaseFieldGraph crossLevelPositiveGraph
      tail level nextCrossLevel)).
    exact hcross.
  - apply (proj2 (raw_dynamicLocalFieldGraph_succ_iff M hPA
      dynamicTruthShiftBaseFieldGraph shiftPositiveGraph
      tail level nextShift)).
    exact hshift.
  - apply (proj2 (raw_dynamicLocalFieldGraph_succ_iff M hPA
      dynamicTruthSubstitutionBaseFieldGraph substitutionPositiveGraph
      tail level nextSubstitution)).
    exact hsubstitution.
  - apply (proj2 (raw_dynamicLocalFieldGraph_succ_iff M hPA
      dynamicTruthAxiomSoundnessBaseFieldGraph
      axiomSoundnessPositiveGraph tail level nextAxiomSoundness)).
    exact haxiom.
  - exact hfinal.
Qed.

(** Public package-successor callback, ready for the generic master
    induction once the staged positive compiler above is constructed. *)
Corollary
    raw_dynamicTruthSplicedMasterPackageSuccessor_of_positive_components
  : forall (M : RawPAModel), RawPASatisfies M -> forall
      localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
      substitutionPositiveGraph axiomSoundnessPositiveGraph,
  RawDynamicTruthSplicedMasterRawPositiveComponentSuccessor M
    localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
    substitutionPositiveGraph axiomSoundnessPositiveGraph ->
  RawSixFieldMasterPackageSuccessor M
    (dynamicTruthSplicedMasterGraph
      localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
      substitutionPositiveGraph axiomSoundnessPositiveGraph).
Proof.
  intros M hPA localPositiveGraph crossLevelPositiveGraph
    shiftPositiveGraph substitutionPositiveGraph
    axiomSoundnessPositiveGraph hcompiler.
  unfold dynamicTruthSplicedMasterGraph.
  apply (raw_sixFieldMasterPackageSuccessor_of_raw_components M hPA).
  exact
    (raw_dynamicTruthSplicedMasterRawComponentSuccessor_of_positive_components
      M hPA localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
      substitutionPositiveGraph axiomSoundnessPositiveGraph hcompiler).
Qed.

End PABoundedRawCodedDynamicTruthMasterSplicedSuccessorBridge.
