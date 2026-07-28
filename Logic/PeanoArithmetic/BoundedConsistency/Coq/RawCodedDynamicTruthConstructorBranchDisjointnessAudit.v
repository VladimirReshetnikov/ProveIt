(** Public-surface and assumption audit for constructor-disjoint row cells. *)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruth
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthConstructorBranchDisjointness.

Module PABoundedRawCodedDynamicTruthConstructorBranchDisjointnessAudit.

Import ListNotations.

Import PA.
Import PAHierarchyReduction.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthConstructorBranchDisjointness.

(** Generic constructor separation. *)
Check RawFormulaPrincipalConstructor.
Check RawFormulaPrincipalBinary.
Check RawFormulaPrincipalUnary.
Check RawFormulaHasPrincipalConstructor.
Check raw_formulaPrincipalConstructors_disjoint.

(** The finite non-QF row interfaces. *)
Check DynamicTruthSigmaConstructorBranch.
Check DTSigmaImpFalseLeft.
Check DTSigmaImpTrueRight.
Check DTSigmaAnd.
Check DTSigmaOr.
Check DTSigmaEx.
Check DTSigmaAll.
Check DynamicTruthPiConstructorBranch.
Check DTPiImp.
Check DTPiAnd.
Check DTPiOr.
Check DTPiAll.
Check DTPiEx.
Check dynamicTruthSigmaBranchPrincipal.
Check dynamicTruthPiBranchPrincipal.
Check DynamicTruthConstructorBranchesDisjoint.
Check DynamicTruthFixedConstructorCell.
Check dynamicTruthFixedConstructorCells.
Check dynamicTruthFixedConstructorCells_length.
Check dynamicTruthFixedConstructorCells_spec.
Check dynamicTruthSigmaConstructorBranchBody.
Check dynamicTruthPiConstructorBranchBody.
Check dynamicTruthSigmaConstructorEx8BranchFormula.
Check dynamicTruthPiConstructorEx8BranchFormula.
Check dynamicTruthSigmaConstructorBranchBody_fixed_lower_irrelevant.
Check dynamicTruthPiConstructorBranchBody_fixed_lower_irrelevant.
Check dynamicTruthSigmaConstructorEx8BranchFormula_fixed_lower_irrelevant.
Check dynamicTruthPiConstructorEx8BranchFormula_fixed_lower_irrelevant.
Check raw_sat_dynamicTruthSigmaConstructorEx8Branch_principal.
Check raw_sat_dynamicTruthPiConstructorEx8Branch_principal.

(** The general schema covers each metatheoretic lower formula.  It is not a
    carrier-parametric compiler for the Sigma-All and Pi-Ex branch bodies. *)
Check dynamicTruthConstructorBranchDisjointnessFormula.
Check dynamicTruthFixedConstructorBranchDisjointnessFormula.
Check
  dynamicTruthConstructorBranchDisjointnessFormula_fixed_lower_irrelevant.
Check dynamicTruthConstructorBranchDisjointnessFormula_raw_valid.
Check PA_proves_dynamicTruthConstructorBranchDisjointnessFormula.
Check PA_proves_dynamicTruthFixedConstructorCell.
Check PA_proves_dynamicTruthFixedConstructorBranchDisjointnessFormula.
Check PA_proves_dynamicTruthSigmaImpFalseLeft_disjoint_cell.
Check PA_proves_dynamicTruthSigmaImpTrueRight_disjoint_cell.
Check PA_proves_dynamicTruthSigmaAnd_disjoint_cell.
Check PA_proves_dynamicTruthSigmaOr_disjoint_cell.
Check PA_proves_dynamicTruthSigmaEx_disjoint_cell.
Check PA_proves_dynamicTruthSigmaAll_disjoint_cell.

(** The ready subset has exactly sixteen cells.  In particular, every cell
    involving Sigma-All or Pi-Ex is outside this lower-independent subset,
    even when its standard-formula instance is covered by the general
    theorem above. *)
Goal length dynamicTruthFixedConstructorCells = 16.
Proof. exact dynamicTruthFixedConstructorCells_length. Qed.

Goal forall piBranch,
  ~ DynamicTruthFixedConstructorCell DTSigmaAll piBranch.
Proof.
  intros piBranch (hfixed & _).
  apply hfixed. reflexivity.
Qed.

Goal forall sigmaBranch,
  ~ DynamicTruthFixedConstructorCell sigmaBranch DTPiEx.
Proof.
  intros sigmaBranch (_ & hfixed & _).
  apply hfixed. reflexivity.
Qed.

Goal In (DTSigmaEx, DTPiAll) dynamicTruthFixedConstructorCells.
Proof. cbn. tauto. Qed.

Goal ~ In (DTSigmaAll, DTPiEx) dynamicTruthFixedConstructorCells.
Proof.
  intro hcell.
  apply dynamicTruthFixedConstructorCells_spec in hcell.
  exact ((proj1 hcell) eq_refl).
Qed.

(** Concrete instances exercise binary/binary, binary/unary,
    unary/binary, and unary/unary separation. *)
Goal forall lowerPi lowerSigma,
  Formula.BProv Formula.Ax_s []
    (dynamicTruthConstructorBranchDisjointnessFormula
      DTSigmaImpFalseLeft lowerPi DTPiAnd lowerSigma).
Proof.
  intros lowerPi lowerSigma.
  apply PA_proves_dynamicTruthSigmaImpFalseLeft_disjoint_cell.
  discriminate.
Qed.

Goal forall lowerPi lowerSigma,
  Formula.BProv Formula.Ax_s []
    (dynamicTruthConstructorBranchDisjointnessFormula
      DTSigmaAnd lowerPi DTPiAll lowerSigma).
Proof.
  intros lowerPi lowerSigma.
  apply PA_proves_dynamicTruthSigmaAnd_disjoint_cell.
  discriminate.
Qed.

Goal forall lowerPi lowerSigma,
  Formula.BProv Formula.Ax_s []
    (dynamicTruthConstructorBranchDisjointnessFormula
      DTSigmaEx lowerPi DTPiOr lowerSigma).
Proof.
  intros lowerPi lowerSigma.
  apply PA_proves_dynamicTruthSigmaEx_disjoint_cell.
  discriminate.
Qed.

Goal forall lowerPi lowerSigma,
  Formula.BProv Formula.Ax_s []
    (dynamicTruthConstructorBranchDisjointnessFormula
      DTSigmaEx lowerPi DTPiAll lowerSigma).
Proof.
  intros lowerPi lowerSigma.
  apply PA_proves_dynamicTruthSigmaEx_disjoint_cell.
  discriminate.
Qed.

(** Exact quotation and represented/local proof endpoints. *)
Check rawDynamicTruthSigmaConstructorEx8BranchCode.
Check rawDynamicTruthPiConstructorEx8BranchCode.
Check rawDynamicTruthConstructorBranchDisjointnessCode.
Check rawDynamicTruthFixedConstructorBranchDisjointnessCode.
Check
  rawDynamicTruthSigmaConstructorEx8BranchCode_fixed_lower_irrelevant.
Check rawDynamicTruthPiConstructorEx8BranchCode_fixed_lower_irrelevant.
Check
  rawDynamicTruthConstructorBranchDisjointnessCode_fixed_lower_irrelevant.
Check rawDynamicTruthSigmaConstructorEx8BranchCode_eq_quoted.
Check rawDynamicTruthPiConstructorEx8BranchCode_eq_quoted.
Check rawDynamicTruthConstructorBranchDisjointnessCode_eq_quoted.
Check rawDynamicTruthConstructorBranchDisjointnessCode_eq_numeral.
Check raw_codedPAProofOf_dynamicTruthConstructorBranchDisjointness.
Check raw_codedPAProofOf_dynamicTruthFixedConstructorCell.
Check rawDynamicTruthConstructorBranchCollisionRoot.
Check raw_codedPALocalProofOf_dynamicTruthConstructorBranchCollision.
Check rawDynamicTruthConstructorCellCollisionRoot.
Check raw_codedPALocalProofOf_dynamicTruthConstructorCellCollision.
Check raw_dynamicTruthConstructorCellCollision_under_assumptions.
Check raw_dynamicTruthConstructorBranchDisjointness_local_base.
Check raw_dynamicTruthConstructorCellCollision_in_witnessed_base.

(** The displayed formula and code retain the literal native Ex8 branches. *)
Goal forall lowerPi lowerSigma,
  dynamicTruthConstructorBranchDisjointnessFormula
    DTSigmaAnd lowerPi DTPiAll lowerSigma =
  pImp (fixedLevelEx8 dynamicTruthSigmaRowAndFormula)
    (pImp (fixedLevelEx8 dynamicTruthPiRowAllFormula) pBot).
Proof. reflexivity. Qed.

Goal forall (M : RawPAModel) lowerPi lowerSigma,
  rawDynamicTruthConstructorBranchDisjointnessCode M
    DTSigmaAnd lowerPi DTPiAll lowerSigma =
  rawFormulaImpCode M
    (rawFixedFormulaNumeralCode M
      (fixedLevelEx8 dynamicTruthSigmaRowAndFormula))
    (rawFormulaImpCode M
      (rawFixedFormulaNumeralCode M
        (fixedLevelEx8 dynamicTruthPiRowAllFormula))
      (rawFormulaBotCode M)).
Proof. reflexivity. Qed.

(** Kernel audit. *)
Print Assumptions raw_formulaPrincipalConstructors_disjoint.
Print Assumptions
  raw_sat_dynamicTruthSigmaConstructorEx8Branch_principal.
Print Assumptions
  raw_sat_dynamicTruthPiConstructorEx8Branch_principal.
Print Assumptions
  dynamicTruthConstructorBranchDisjointnessFormula_raw_valid.
Print Assumptions
  PA_proves_dynamicTruthConstructorBranchDisjointnessFormula.
Print Assumptions PA_proves_dynamicTruthFixedConstructorCell.
Print Assumptions
  PA_proves_dynamicTruthFixedConstructorBranchDisjointnessFormula.
Print Assumptions
  raw_codedPAProofOf_dynamicTruthConstructorBranchDisjointness.
Print Assumptions raw_codedPAProofOf_dynamicTruthFixedConstructorCell.
Print Assumptions
  raw_codedPALocalProofOf_dynamicTruthConstructorCellCollision.
Print Assumptions
  raw_dynamicTruthConstructorCellCollision_under_assumptions.
Print Assumptions
  raw_dynamicTruthConstructorCellCollision_in_witnessed_base.

End PABoundedRawCodedDynamicTruthConstructorBranchDisjointnessAudit.
