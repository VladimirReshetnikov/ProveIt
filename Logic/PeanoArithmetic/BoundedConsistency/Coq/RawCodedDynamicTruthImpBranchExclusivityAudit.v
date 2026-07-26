(** Audit of the two conditional implication constructor cells. *)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruth
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthImpBranchExclusivity.

Module PABoundedRawCodedDynamicTruthImpBranchExclusivityAudit.

Import PA.
Import PAHierarchyReduction.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.

(** The predecessor premise is an explicit earlier-state-table law. *)
Check dynamicTruthImpPredecessorStateExclusivityFormula.
Check RawDynamicTruthImpPredecessorStateExclusiveAt.
Check raw_sat_dynamicTruthImpPredecessorStateExclusivityFormula_iff.

(** Literal native branches, with eight existential row witnesses each. *)
Check dynamicTruthSigmaImpFalseLeftEx8BranchFormula.
Check dynamicTruthSigmaImpTrueRightEx8BranchFormula.
Check dynamicTruthPiImpEx8BranchFormula.
Check RawDynamicTruthSigmaImpFalseLeftEx8BranchAt.
Check RawDynamicTruthSigmaImpTrueRightEx8BranchAt.
Check RawDynamicTruthPiImpEx8BranchAt.
Check raw_sat_dynamicTruthSigmaImpFalseLeftEx8BranchFormula_iff.
Check raw_sat_dynamicTruthSigmaImpTrueRightEx8BranchFormula_iff.
Check raw_sat_dynamicTruthPiImpEx8BranchFormula_iff.

(** The two conditional matrix cells and their PA proofs. *)
Check dynamicTruthImpFalseLeftConditionalCellFormula.
Check dynamicTruthImpTrueRightConditionalCellFormula.
Check raw_sat_dynamicTruthImpFalseLeftConditionalCellFormula_iff.
Check raw_sat_dynamicTruthImpTrueRightConditionalCellFormula_iff.
Check dynamicTruthImpFalseLeftConditionalCellFormula_raw_valid.
Check dynamicTruthImpTrueRightConditionalCellFormula_raw_valid.
Check PA_proves_dynamicTruthImpFalseLeftConditionalCellFormula.
Check PA_proves_dynamicTruthImpTrueRightConditionalCellFormula.

(** Transparent carrier-code layer. *)
Check rawDynamicTruthImpPredecessorStateExclusivityCode.
Check rawDynamicTruthSigmaImpFalseLeftRowCode.
Check rawDynamicTruthSigmaImpTrueRightRowCode.
Check rawDynamicTruthPiImpRowCode.
Check rawDynamicTruthSigmaImpFalseLeftEx8BranchCode.
Check rawDynamicTruthSigmaImpTrueRightEx8BranchCode.
Check rawDynamicTruthPiImpEx8BranchCode.
Check rawDynamicTruthImpFalseLeftConditionalCellCode.
Check rawDynamicTruthImpTrueRightConditionalCellCode.
Check rawDynamicTruthImpPredecessorStateExclusivityCode_eq_quoted.
Check rawDynamicTruthSigmaImpFalseLeftEx8BranchCode_eq_quoted.
Check rawDynamicTruthSigmaImpTrueRightEx8BranchCode_eq_quoted.
Check rawDynamicTruthPiImpEx8BranchCode_eq_quoted.
Check rawDynamicTruthImpFalseLeftConditionalCellCode_eq_quoted.
Check rawDynamicTruthImpTrueRightConditionalCellCode_eq_quoted.
Check rawDynamicTruthImpPredecessorStateExclusivityCode_eq_numeral.
Check rawDynamicTruthSigmaImpFalseLeftEx8BranchCode_eq_numeral.
Check rawDynamicTruthSigmaImpTrueRightEx8BranchCode_eq_numeral.
Check rawDynamicTruthPiImpEx8BranchCode_eq_numeral.
Check rawDynamicTruthImpFalseLeftConditionalCellCode_eq_numeral.
Check rawDynamicTruthImpTrueRightConditionalCellCode_eq_numeral.

(** Represented and common-context proof endpoints. *)
Check raw_codedPAProofOf_dynamicTruthImpFalseLeftConditionalCell.
Check raw_codedPAProofOf_dynamicTruthImpTrueRightConditionalCell.
Check rawDynamicTruthImpConditionalCellCollisionRoot.
Check raw_codedPALocalProofOf_dynamicTruthImpConditionalCellCollision.
Check rawDynamicTruthImpFalseLeftConditionalCellCollisionRoot.
Check rawDynamicTruthImpTrueRightConditionalCellCollisionRoot.
Check
  raw_codedPALocalProofOf_dynamicTruthImpFalseLeftConditionalCellCollision.
Check
  raw_codedPALocalProofOf_dynamicTruthImpTrueRightConditionalCellCollision.
Check raw_dynamicTruthImpConditionalCellCollision_under_assumptions.
Check
  raw_dynamicTruthImpFalseLeftConditionalCellCollision_under_assumptions.
Check
  raw_dynamicTruthImpTrueRightConditionalCellCollision_under_assumptions.
Check raw_dynamicTruthImpFalseLeftConditionalCell_local_base.
Check raw_dynamicTruthImpTrueRightConditionalCell_local_base.
Check
  raw_dynamicTruthImpFalseLeftConditionalCellCollision_in_witnessed_base.
Check
  raw_dynamicTruthImpTrueRightConditionalCellCollision_in_witnessed_base.

(** Definitional-shape audits: these ensure the implementation really uses
    the native row leaves rather than lookalike re-encodings. *)
Goal dynamicTruthSigmaImpFalseLeftEx8BranchFormula =
  fixedLevelEx8 dynamicTruthSigmaRowImpFalseLeftFormula.
Proof. reflexivity. Qed.

Goal dynamicTruthSigmaImpTrueRightEx8BranchFormula =
  fixedLevelEx8 dynamicTruthSigmaRowImpTrueRightFormula.
Proof. reflexivity. Qed.

Goal dynamicTruthPiImpEx8BranchFormula =
  fixedLevelEx8 dynamicTruthPiRowImpFormula.
Proof. reflexivity. Qed.

Goal dynamicTruthImpFalseLeftConditionalCellFormula =
  pImp dynamicTruthImpPredecessorStateExclusivityFormula
    (pImp (fixedLevelEx8 dynamicTruthSigmaRowImpFalseLeftFormula)
      (pImp (fixedLevelEx8 dynamicTruthPiRowImpFormula) pBot)).
Proof. reflexivity. Qed.

Goal dynamicTruthImpTrueRightConditionalCellFormula =
  pImp dynamicTruthImpPredecessorStateExclusivityFormula
    (pImp (fixedLevelEx8 dynamicTruthSigmaRowImpTrueRightFormula)
      (pImp (fixedLevelEx8 dynamicTruthPiRowImpFormula) pBot)).
Proof. reflexivity. Qed.

Goal forall (M : RawPAModel),
  rawDynamicTruthImpFalseLeftConditionalCellCode M =
  rawFormulaImpCode M
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M)
      (rawFormulaImpCode M (rawDynamicTruthPiImpEx8BranchCode M)
        (rawFormulaBotCode M))).
Proof. reflexivity. Qed.

Goal forall (M : RawPAModel),
  rawDynamicTruthImpTrueRightConditionalCellCode M =
  rawFormulaImpCode M
    (rawDynamicTruthImpPredecessorStateExclusivityCode M)
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaImpTrueRightEx8BranchCode M)
      (rawFormulaImpCode M (rawDynamicTruthPiImpEx8BranchCode M)
        (rawFormulaBotCode M))).
Proof. reflexivity. Qed.

(** Assumption audit.  In particular, none of these checks supplies the
    predecessor exclusivity root required by the guarded collision theorem. *)
Print Assumptions dynamicTruthImpFalseLeftConditionalCellFormula_raw_valid.
Print Assumptions dynamicTruthImpTrueRightConditionalCellFormula_raw_valid.
Print Assumptions PA_proves_dynamicTruthImpFalseLeftConditionalCellFormula.
Print Assumptions PA_proves_dynamicTruthImpTrueRightConditionalCellFormula.
Print Assumptions
  raw_codedPALocalProofOf_dynamicTruthImpConditionalCellCollision.
Print Assumptions
  raw_dynamicTruthImpFalseLeftConditionalCellCollision_under_assumptions.
Print Assumptions
  raw_dynamicTruthImpTrueRightConditionalCellCollision_under_assumptions.
Print Assumptions
  raw_dynamicTruthImpFalseLeftConditionalCellCollision_in_witnessed_base.
Print Assumptions
  raw_dynamicTruthImpTrueRightConditionalCellCollision_in_witnessed_base.

End PABoundedRawCodedDynamicTruthImpBranchExclusivityAudit.
