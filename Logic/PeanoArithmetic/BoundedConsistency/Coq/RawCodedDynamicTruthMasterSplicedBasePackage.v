(**
  The exact master base package for zero/positive spliced field graphs.

  A master coordinate cannot use its fixed level-zero graph at every model
  index: its positive values are carrier-indexed formula codes.  The generic
  [dynamicLocalFieldGraph] supplies the required nonstandard-safe splice,
  evaluating a fixed base graph at zero and a positive graph at the selected
  predecessor of a successor index.

  This module lifts the already checked five-coordinate base package through
  that splice.  The positive graphs remain arbitrary parameters; no positive
  totality or proof theorem is assumed merely to establish the zero callback.
  Consequently the exported master graph is ready to receive the eventual
  positive local, cross-level, shift, substitution, and axiom-soundness
  graphs without changing its base proof.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedDynamicLocalFieldGraph
  RawCodedDynamicTruthLocalDecisionExclusiveBase
  RawCodedDynamicTruthTransportFieldBaseGraphs
  RawCodedDynamicTruthAxiomSoundnessBaseGraph
  RawCodedDynamicTruthMasterBasePackage
  RawCodedTruthCertificateMasterAssembler
  RawCodedTruthCertificateMasterInduction
  RawCodedTruthCertificateMasterBaseBridge.

Module PABoundedRawCodedDynamicTruthMasterSplicedBasePackage.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedDynamicLocalFieldGraph.
Import PABoundedRawCodedDynamicTruthLocalDecisionExclusiveBase.
Import PABoundedRawCodedDynamicTruthTransportFieldBaseGraphs.
Import PABoundedRawCodedDynamicTruthAxiomSoundnessBaseGraph.
Import PABoundedRawCodedDynamicTruthMasterBasePackage.
Import PABoundedRawCodedTruthCertificateMasterAssembler.
Import PABoundedRawCodedTruthCertificateMasterInduction.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.

(** The five master coordinates share one splice operation but retain their
    distinct checked zero graphs. *)
Definition dynamicTruthSplicedLocalFieldGraph
    (positiveGraph : formula) : formula :=
  dynamicLocalFieldGraph
    dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph positiveGraph.

Definition dynamicTruthSplicedCrossLevelFieldGraph
    (positiveGraph : formula) : formula :=
  dynamicLocalFieldGraph dynamicTruthCrossLevelBaseFieldGraph positiveGraph.

Definition dynamicTruthSplicedShiftFieldGraph
    (positiveGraph : formula) : formula :=
  dynamicLocalFieldGraph dynamicTruthShiftBaseFieldGraph positiveGraph.

Definition dynamicTruthSplicedSubstitutionFieldGraph
    (positiveGraph : formula) : formula :=
  dynamicLocalFieldGraph dynamicTruthSubstitutionBaseFieldGraph positiveGraph.

Definition dynamicTruthSplicedAxiomSoundnessFieldGraph
    (positiveGraph : formula) : formula :=
  dynamicLocalFieldGraph dynamicTruthAxiomSoundnessBaseFieldGraph positiveGraph.

(** Lift one exact quoted-code witness through the zero view of the generic
    splice.  This helper keeps all five component proofs visibly identical. *)
Lemma raw_dynamicTruthSplicedField_zero_of_base : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseGraph positiveGraph fieldFormula tail,
  raw_formula_sat M
    (scons M (rawQuotedFormulaCode M fieldFormula)
      (scons M (raw_zero M) tail)) baseGraph ->
  raw_formula_sat M
    (scons M (rawQuotedFormulaCode M fieldFormula)
      (scons M (raw_zero M) tail))
    (dynamicLocalFieldGraph baseGraph positiveGraph).
Proof.
  intros M hPA baseGraph positiveGraph fieldFormula tail hbase.
  apply (proj2 (raw_dynamicLocalFieldGraph_zero_iff M hPA
    baseGraph positiveGraph tail
    (rawQuotedFormulaCode M fieldFormula))).
  exact hbase.
Qed.

(** Exact standard-[BProv] package for the five spliced graphs.  The proof
    terms are the already checked base derivations; only their graph views
    are transported through the zero branch. *)
Theorem raw_dynamicTruthMasterSplicedBaseBProvComponentPackage : forall
    localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
      substitutionPositiveGraph axiomSoundnessPositiveGraph,
  forall (M : RawPAModel), RawPASatisfies M ->
  RawSixFieldMasterZeroBProvComponentPackage M
    (dynamicTruthSplicedLocalFieldGraph localPositiveGraph)
    (dynamicTruthSplicedCrossLevelFieldGraph crossLevelPositiveGraph)
    (dynamicTruthSplicedShiftFieldGraph shiftPositiveGraph)
    (dynamicTruthSplicedSubstitutionFieldGraph substitutionPositiveGraph)
    (dynamicTruthSplicedAxiomSoundnessFieldGraph
      axiomSoundnessPositiveGraph)
    dynamicTruthLocalDecisionExclusiveBaseFormula
    dynamicTruthCrossLevelBaseFieldFormula
    dynamicTruthShiftBaseFieldFormula
    dynamicTruthSubstitutionBaseFieldFormula
    dynamicTruthAxiomSoundnessBaseFieldFormula.
Proof.
  intros localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
    substitutionPositiveGraph axiomSoundnessPositiveGraph M hPA.
  pose proof (raw_dynamicTruthMasterBaseBProvComponentPackage M hPA)
    as hbase.
  unfold RawSixFieldMasterZeroBProvComponentPackage in hbase |- *.
  destruct hbase as
    (hlocal & hcross & hshift & hsubstitution & haxiom &
      hlocalProof & hcrossProof & hshiftProof & hsubstitutionProof &
      haxiomProof).
  repeat split.
  - intro tail.
    apply (raw_dynamicTruthSplicedField_zero_of_base M hPA
      dynamicTruthLocalDecisionExclusiveBaseFormulaCodeGraph
      localPositiveGraph dynamicTruthLocalDecisionExclusiveBaseFormula).
    exact (hlocal tail).
  - intro tail.
    apply (raw_dynamicTruthSplicedField_zero_of_base M hPA
      dynamicTruthCrossLevelBaseFieldGraph crossLevelPositiveGraph
      dynamicTruthCrossLevelBaseFieldFormula).
    exact (hcross tail).
  - intro tail.
    apply (raw_dynamicTruthSplicedField_zero_of_base M hPA
      dynamicTruthShiftBaseFieldGraph shiftPositiveGraph
      dynamicTruthShiftBaseFieldFormula).
    exact (hshift tail).
  - intro tail.
    apply (raw_dynamicTruthSplicedField_zero_of_base M hPA
      dynamicTruthSubstitutionBaseFieldGraph substitutionPositiveGraph
      dynamicTruthSubstitutionBaseFieldFormula).
    exact (hsubstitution tail).
  - intro tail.
    apply (raw_dynamicTruthSplicedField_zero_of_base M hPA
      dynamicTruthAxiomSoundnessBaseFieldGraph
      axiomSoundnessPositiveGraph dynamicTruthAxiomSoundnessBaseFieldFormula).
    exact (haxiom tail).
  - exact hlocalProof.
  - exact hcrossProof.
  - exact hshiftProof.
  - exact hsubstitutionProof.
  - exact haxiomProof.
Qed.

(** Public zero-component package in the standard derivation branch. *)
Theorem raw_dynamicTruthMasterSplicedBaseComponentPackage : forall
    localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
      substitutionPositiveGraph axiomSoundnessPositiveGraph,
  forall (M : RawPAModel), RawPASatisfies M ->
  RawSixFieldMasterZeroComponentPackage M
    (dynamicTruthSplicedLocalFieldGraph localPositiveGraph)
    (dynamicTruthSplicedCrossLevelFieldGraph crossLevelPositiveGraph)
    (dynamicTruthSplicedShiftFieldGraph shiftPositiveGraph)
    (dynamicTruthSplicedSubstitutionFieldGraph substitutionPositiveGraph)
    (dynamicTruthSplicedAxiomSoundnessFieldGraph
      axiomSoundnessPositiveGraph).
Proof.
  intros localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
    substitutionPositiveGraph axiomSoundnessPositiveGraph M hPA.
  right.
  exists dynamicTruthLocalDecisionExclusiveBaseFormula,
    dynamicTruthCrossLevelBaseFieldFormula,
    dynamicTruthShiftBaseFieldFormula,
    dynamicTruthSubstitutionBaseFieldFormula,
    dynamicTruthAxiomSoundnessBaseFieldFormula.
  exact (raw_dynamicTruthMasterSplicedBaseBProvComponentPackage
    localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
    substitutionPositiveGraph axiomSoundnessPositiveGraph M hPA).
Qed.

(** The concrete master graph whose zero callback has just been discharged.
    Each parameter is read at the predecessor of a positive master index. *)
Definition dynamicTruthSplicedMasterGraph
    (localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
      substitutionPositiveGraph axiomSoundnessPositiveGraph : formula)
    : formula :=
  concreteSixFieldMasterGraph
    (dynamicTruthSplicedLocalFieldGraph localPositiveGraph)
    (dynamicTruthSplicedCrossLevelFieldGraph crossLevelPositiveGraph)
    (dynamicTruthSplicedShiftFieldGraph shiftPositiveGraph)
    (dynamicTruthSplicedSubstitutionFieldGraph substitutionPositiveGraph)
    (dynamicTruthSplicedAxiomSoundnessFieldGraph
      axiomSoundnessPositiveGraph).

(** Exact master-induction base callback for arbitrary future positive
    graphs.  No successor theorem is smuggled into this result. *)
Theorem raw_dynamicTruthSplicedMasterPackageBase : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
      substitutionPositiveGraph axiomSoundnessPositiveGraph,
  RawSixFieldMasterPackageBase M
    (dynamicTruthSplicedMasterGraph
      localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
      substitutionPositiveGraph axiomSoundnessPositiveGraph).
Proof.
  intros M hPA localPositiveGraph crossLevelPositiveGraph
    shiftPositiveGraph substitutionPositiveGraph
    axiomSoundnessPositiveGraph.
  unfold dynamicTruthSplicedMasterGraph.
  apply (raw_sixFieldMasterPackageBase_of_components M hPA).
  exact (raw_dynamicTruthMasterSplicedBaseComponentPackage
    localPositiveGraph crossLevelPositiveGraph shiftPositiveGraph
    substitutionPositiveGraph axiomSoundnessPositiveGraph M hPA).
Qed.

End PABoundedRawCodedDynamicTruthMasterSplicedBasePackage.
