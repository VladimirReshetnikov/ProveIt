(** Audit of the two conditional quantifier-diagonal cells. *)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruth
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedDynamicTruthQuantifierBranchExclusivity.

Module PABoundedRawCodedDynamicTruthQuantifierBranchExclusivityAudit.

Import PA.
Import PAHierarchyReduction.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.

(** Literal native branch syntax. *)
Check dynamicTruthSigmaEx8BranchFormula.
Check dynamicTruthPiExistentialLeafFormula.
Check dynamicTruthPiExistentialEx8BranchFormula.
Check dynamicTruthSigmaUniversalLeafFormula.
Check dynamicTruthSigmaUniversalEx8BranchFormula.
Check dynamicTruthPiAllEx8BranchFormula.

Goal dynamicTruthSigmaEx8BranchFormula =
  fixedLevelEx8 dynamicTruthSigmaRowExFormula.
Proof. reflexivity. Qed.

Goal forall lowerSigma,
  dynamicTruthPiExistentialEx8BranchFormula
    (Formula.rename dynamicTruthPiCoqLowerApplicationRenaming lowerSigma) =
  fixedLevelEx8
    (pAnd dynamicTruthPiRowExistentialPrefixFormula
      (fixedLevelNoBinderCounterexampleTermAt
        (Formula.rename dynamicTruthPiCoqLowerApplicationRenaming lowerSigma)
        (tVar 9) (tVar 8) (tVar 10))).
Proof. reflexivity. Qed.

Goal forall lowerPi,
  dynamicTruthSigmaUniversalEx8BranchFormula
    (Formula.rename dynamicTruthCoqLowerApplicationRenaming lowerPi) =
  fixedLevelEx8
    (pAnd dynamicTruthSigmaRowUniversalPrefixFormula
      (fixedLevelNoBinderCounterexampleTermAt
        (Formula.rename dynamicTruthCoqLowerApplicationRenaming lowerPi)
        (tVar 9) (tVar 8) (tVar 10))).
Proof. reflexivity. Qed.

Goal dynamicTruthPiAllEx8BranchFormula =
  fixedLevelEx8 dynamicTruthPiRowAllFormula.
Proof. reflexivity. Qed.

(** The missing cross-level facts are visible formula antecedents. *)
Check dynamicTruthPiExistentialCounterexampleFormula.
Check dynamicTruthSigmaUniversalCounterexampleFormula.
Check dynamicTruthQuantifierAll8.
Check dynamicTruthSigmaExPiExCrossLevelPremiseFormula.
Check dynamicTruthSigmaAllPiAllCrossLevelPremiseFormula.
Check dynamicTruthSigmaExPiExConditionalCellFormula.
Check dynamicTruthSigmaAllPiAllConditionalCellFormula.

Goal forall lowerApplication,
  dynamicTruthSigmaExPiExCrossLevelPremiseFormula lowerApplication =
  pImp dynamicTruthSigmaEx8BranchFormula
    (dynamicTruthQuantifierAll8
      (pImp dynamicTruthPiRowExistentialPrefixFormula
        (dynamicTruthPiExistentialCounterexampleFormula
          lowerApplication))).
Proof. reflexivity. Qed.

Goal forall lowerApplication,
  dynamicTruthSigmaAllPiAllCrossLevelPremiseFormula lowerApplication =
  pImp dynamicTruthPiAllEx8BranchFormula
    (dynamicTruthQuantifierAll8
      (pImp dynamicTruthSigmaRowUniversalPrefixFormula
        (dynamicTruthSigmaUniversalCounterexampleFormula
          lowerApplication))).
Proof. reflexivity. Qed.

(** Fixed conditional PA theorems. *)
Check dynamicTruthSigmaExPiExConditionalCellFormula_raw_valid.
Check dynamicTruthSigmaAllPiAllConditionalCellFormula_raw_valid.
Check PA_proves_dynamicTruthSigmaExPiExConditionalCellFormula.
Check PA_proves_dynamicTruthSigmaAllPiAllConditionalCellFormula.

(** Carrier-polynomial layer.  Only [M] and carrier elements occur in these
    public types; there is no metatheoretic formula decoder. *)
Check rawDynamicTruthSigmaEx8BranchCode.
Check rawDynamicTruthPiExistentialEx8BranchCode.
Check rawDynamicTruthSigmaUniversalEx8BranchCode.
Check rawDynamicTruthPiAllEx8BranchCode.
Check rawDynamicTruthPiExistentialCounterexampleCode.
Check rawDynamicTruthSigmaUniversalCounterexampleCode.
Check rawDynamicTruthQuantifierAll8Code.
Check rawDynamicTruthSigmaExPiExCrossLevelPremiseCode.
Check rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode.
Check rawDynamicTruthSigmaExPiExConditionalCellCode.
Check rawDynamicTruthSigmaAllPiAllConditionalCellCode.
Check rawDynamicTruthPiExistentialEx8BranchCode_eq_native.
Check rawDynamicTruthSigmaUniversalEx8BranchCode_eq_native.

Goal forall (M : RawPAModel) lowerApplication,
  rawDynamicTruthPiExistentialEx8BranchCode M lowerApplication =
  rawDynamicTruthPiFormulaEx8Code M
    (rawCoqDynamicTruthPiExistentialLeafTemplateCode M lowerApplication).
Proof. reflexivity. Qed.

Goal forall (M : RawPAModel) lowerApplication,
  rawDynamicTruthSigmaUniversalEx8BranchCode M lowerApplication =
  rawFormulaEx8Code M
    (rawCoqDynamicTruthSigmaUniversalLeafTemplateCode M lowerApplication).
Proof. reflexivity. Qed.

Check rawDynamicTruthSigmaEx8BranchCode_eq_quoted.
Check rawDynamicTruthPiExistentialEx8BranchCode_eq_quoted.
Check rawDynamicTruthSigmaUniversalEx8BranchCode_eq_quoted.
Check rawDynamicTruthPiAllEx8BranchCode_eq_quoted.
Check rawDynamicTruthPiExistentialCounterexampleCode_eq_quoted.
Check rawDynamicTruthSigmaUniversalCounterexampleCode_eq_quoted.
Check rawDynamicTruthSigmaExPiExCrossLevelPremiseCode_eq_quoted.
Check rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode_eq_quoted.
Check rawDynamicTruthSigmaExPiExConditionalCellCode_eq_quoted.
Check rawDynamicTruthSigmaAllPiAllConditionalCellCode_eq_quoted.
Check raw_codedPAProofOf_dynamicTruthSigmaExPiExConditionalCell_standard.
Check raw_codedPAProofOf_dynamicTruthSigmaAllPiAllConditionalCell_standard.

(** The arbitrary-carrier compilation obligation remains explicit. *)
Check RawDynamicTruthQuantifierConditionalCellCompilerTotal.

(** Exact common-context endpoints and restricted-branch projection reuse. *)
Check rawDynamicTruthQuantifierConditionalCellCollisionRoot.
Check
  raw_codedPALocalProofOf_dynamicTruthQuantifierConditionalCellCollision.
Check rawDynamicTruthSigmaExPiExConditionalCellCollisionRoot.
Check rawDynamicTruthSigmaAllPiAllConditionalCellCollisionRoot.
Check raw_codedPALocalProofOf_dynamicTruthSigmaExPiExCollision.
Check raw_codedPALocalProofOf_dynamicTruthSigmaAllPiAllCollision.
Check rawDynamicTruthSigmaRestrictedUniversalBranchRoot.
Check rawDynamicTruthPiRestrictedExistentialBranchRoot.
Check
  raw_codedPALocalProofOf_dynamicTruthSigmaRestrictedUniversalBranch.
Check
  raw_codedPALocalProofOf_dynamicTruthPiRestrictedExistentialBranch.

(** Assumption audit.  In particular, the local collision endpoints take a
    cross-level premise root as an argument instead of postulating one. *)
Print Assumptions dynamicTruthSigmaExPiExConditionalCellFormula_raw_valid.
Print Assumptions dynamicTruthSigmaAllPiAllConditionalCellFormula_raw_valid.
Print Assumptions PA_proves_dynamicTruthSigmaExPiExConditionalCellFormula.
Print Assumptions PA_proves_dynamicTruthSigmaAllPiAllConditionalCellFormula.
Print Assumptions
  raw_codedPAProofOf_dynamicTruthSigmaExPiExConditionalCell_standard.
Print Assumptions
  raw_codedPAProofOf_dynamicTruthSigmaAllPiAllConditionalCell_standard.
Print Assumptions raw_codedPALocalProofOf_dynamicTruthSigmaExPiExCollision.
Print Assumptions raw_codedPALocalProofOf_dynamicTruthSigmaAllPiAllCollision.
Print Assumptions
  raw_codedPALocalProofOf_dynamicTruthSigmaRestrictedUniversalBranch.
Print Assumptions
  raw_codedPALocalProofOf_dynamicTruthPiRestrictedExistentialBranch.

End PABoundedRawCodedDynamicTruthQuantifierBranchExclusivityAudit.
