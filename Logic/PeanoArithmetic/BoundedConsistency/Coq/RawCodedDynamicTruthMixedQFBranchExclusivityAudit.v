(** Kernel-facing audit for the eleven mixed QF/non-QF matrix cells. *)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruth
  RawCodedDynamicTruthQFBranchExclusivity
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthBooleanBranchExclusivity
  RawCodedDynamicTruthQuantifierBranchExclusivity
  RawCodedPAProvability
  RawCodedDynamicTruthMixedQFBranchExclusivity.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthMixedQFBranchExclusivityAudit.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedDynamicTruthQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBooleanBranchExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedDynamicTruthMixedQFBranchExclusivity.

(** Exact finite coverage.  Logical dependence gives seven replay cells and
    four unconditional quantifier cells.  Carrier-code dependence gives a
    different partition: nine fixed cells and two opaque lower-dependent
    cells. *)
Check DynamicTruthMixedQFCell.
Check dynamicTruthMixedQFCells.
Check dynamicTruthMixedQFReplayCells.
Check dynamicTruthMixedQFQuantifierCells.
Check dynamicTruthMixedQFFixedCodeCells.
Check dynamicTruthMixedQFOpaqueCodeCells.

Goal length dynamicTruthMixedQFCells = 11.
Proof. exact dynamicTruthMixedQFCells_length. Qed.

Goal length dynamicTruthMixedQFReplayCells = 7.
Proof. exact dynamicTruthMixedQFReplayCells_length. Qed.

Goal length dynamicTruthMixedQFQuantifierCells = 4.
Proof. exact dynamicTruthMixedQFQuantifierCells_length. Qed.

Goal length dynamicTruthMixedQFFixedCodeCells = 9.
Proof. exact dynamicTruthMixedQFFixedCodeCells_length. Qed.

Goal length dynamicTruthMixedQFOpaqueCodeCells = 2.
Proof. exact dynamicTruthMixedQFOpaqueCodeCells_length. Qed.

Goal forall cell,
  In cell dynamicTruthMixedQFReplayCells \/
  In cell dynamicTruthMixedQFQuantifierCells.
Proof. exact dynamicTruthMixedQFCells_partition. Qed.

Goal forall cell,
  In cell dynamicTruthMixedQFFixedCodeCells \/
  In cell dynamicTruthMixedQFOpaqueCodeCells.
Proof. exact dynamicTruthMixedQFCodeCells_partition. Qed.

Goal forall cell,
  In cell dynamicTruthMixedQFReplayCells ->
  ~ In cell dynamicTruthMixedQFQuantifierCells.
Proof. exact dynamicTruthMixedQFLogicalPartitions_disjoint. Qed.

Goal forall cell,
  In cell dynamicTruthMixedQFFixedCodeCells ->
  ~ In cell dynamicTruthMixedQFOpaqueCodeCells.
Proof. exact dynamicTruthMixedQFCodePartitions_disjoint. Qed.

(** The two opaque cells are nevertheless in the unconditional logical
    partition.  Opacity here concerns nonstandard syntax compilation, not
    an extra semantic premise. *)
Goal dynamicTruthMixedQFOpaqueCodeCells =
  [ DTMQFSigmaQFPiEx; DTMQFSigmaAllPiQF ].
Proof. reflexivity. Qed.

Goal In DTMQFSigmaQFPiEx dynamicTruthMixedQFQuantifierCells /\
  In DTMQFSigmaAllPiQF dynamicTruthMixedQFQuantifierCells.
Proof. cbn; intuition. Qed.

(** Literal representative formulae exhibit the conditional/unconditional
    distinction. *)
Goal forall lowerPi lowerSigma,
  dynamicTruthMixedQFCellFormula DTMQFSigmaQFPiImp
    lowerPi lowerSigma =
  pImp dynamicTruthMixedQFReplayExclusivityFormula
    (pImp dynamicTruthSigmaQFEx8BranchFormula
      (pImp dynamicTruthPiImpEx8BranchFormula pBot)).
Proof. reflexivity. Qed.

Goal forall lowerPi lowerSigma,
  dynamicTruthMixedQFCellFormula DTMQFSigmaQFPiAll
    lowerPi lowerSigma =
  pImp dynamicTruthSigmaQFEx8BranchFormula
    (pImp dynamicTruthPiAllEx8BranchFormula pBot).
Proof. reflexivity. Qed.

Goal forall lowerPi lowerSigma,
  dynamicTruthMixedQFCellFormula DTMQFSigmaQFPiEx
    lowerPi lowerSigma =
  pImp dynamicTruthSigmaQFEx8BranchFormula
    (pImp (dynamicTruthPiExistentialEx8BranchFormula lowerSigma) pBot).
Proof. reflexivity. Qed.

Goal forall lowerPi lowerSigma,
  dynamicTruthMixedQFCellFormula DTMQFSigmaAllPiQF
    lowerPi lowerSigma =
  pImp (dynamicTruthSigmaUniversalEx8BranchFormula lowerPi)
    (pImp dynamicTruthPiQFEx8BranchFormula pBot).
Proof. reflexivity. Qed.

(** Semantic and ordinary PA proof surfaces cover all eleven constructors.
    The seven replay cases prove an implication from the exact replay
    formula; the four quantified cases contain no such antecedent. *)
Check RawDynamicTruthMixedQFReplayExclusiveAt.
Check raw_sat_dynamicTruthMixedQFReplayExclusivityFormula_iff.
Check dynamicTruthMixedQFCellFormula_raw_valid.
Check PA_proves_dynamicTruthMixedQFCellFormula.

Goal forall cell lowerPi lowerSigma,
  Formula.BProv Formula.Ax_s []
    (dynamicTruthMixedQFCellFormula cell lowerPi lowerSigma).
Proof. exact PA_proves_dynamicTruthMixedQFCellFormula. Qed.

(** Carrier quotation and represented proof compilation. *)
Check rawDynamicTruthMixedQFSigmaBranchCode.
Check rawDynamicTruthMixedQFPiBranchCode.
Check rawDynamicTruthMixedQFReplayExclusivityCode.
Check rawDynamicTruthMixedQFCollisionCode.
Check rawDynamicTruthMixedQFCellCode.
Check rawDynamicTruthMixedQFSigmaBranchCode_eq_quoted.
Check rawDynamicTruthMixedQFPiBranchCode_eq_quoted.
Check rawDynamicTruthMixedQFCellCode_eq_quoted.
Check rawDynamicTruthMixedQFCellCode_eq_numeral.
Check raw_codedPAProofOf_dynamicTruthMixedQFCell.

(** Arbitrary carrier inputs are already solved for exactly nine cells. *)
Check rawDynamicTruthMixedQFCellCode_fixed_lower_irrelevant.
Check raw_codedPAProofOf_dynamicTruthMixedQFFixedCell.

Goal forall (M : RawPAModel), RawPASatisfies M -> forall cell,
  In cell dynamicTruthMixedQFFixedCodeCells -> forall
    lowerPiApplication lowerSigmaApplication,
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthMixedQFCellCode M cell
        lowerPiApplication lowerSigmaApplication) certificate.
Proof. exact raw_codedPAProofOf_dynamicTruthMixedQFFixedCell. Qed.

(** Common-context collision consumes a replay root only for the seven
    Boolean cells.  The four quantifier constructors store [unit]; their
    smart constructor checks finite classification at its boundary but no
    proof evidence remains in the collision input. *)
Check RawDynamicTruthMixedQFCellPremiseRoots.
Check RDTMQFReplayPremiseRoot.
Check RDTMQFQuantifierNoPremise.
Check rawDynamicTruthMixedQFCellCollisionRoot.
Check raw_codedPALocalProofOf_dynamicTruthMixedQFCellCollision.

(** The complete arbitrary-carrier compiler reduces to precisely two
    clauses: Pi-Ex at arbitrary lower-Sigma code and Sigma-All at arbitrary
    lower-Pi code. *)
Check RawDynamicTruthMixedQFOpaqueQuantifierCellProofCompiler.
Check RawDynamicTruthMixedQFCellProofCompilerTotal.
Check raw_dynamicTruthMixedQFCellProofCompilerTotal_of_opaque.

(** Trusted-kernel audit of the substantive endpoints. *)
Print Assumptions dynamicTruthMixedQFCellFormula_raw_valid.
Print Assumptions PA_proves_dynamicTruthMixedQFCellFormula.
Print Assumptions raw_codedPAProofOf_dynamicTruthMixedQFCell.
Print Assumptions rawDynamicTruthMixedQFCellCode_fixed_lower_irrelevant.
Print Assumptions raw_codedPAProofOf_dynamicTruthMixedQFFixedCell.
Print Assumptions
  raw_codedPALocalProofOf_dynamicTruthMixedQFCellCollision.
Print Assumptions
  raw_dynamicTruthMixedQFCellProofCompilerTotal_of_opaque.

End PABoundedRawCodedDynamicTruthMixedQFBranchExclusivityAudit.
