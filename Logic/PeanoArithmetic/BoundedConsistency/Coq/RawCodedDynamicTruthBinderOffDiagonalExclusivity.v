(**
  Carrier-parametric interface for the eight binder off-diagonal cells.

  The native Sigma/Pi successor rows have eight constructor-disjoint cells
  that were not covered by the fixed-formula compiler: four cells whose
  Sigma side is the universal branch and five whose Pi side is the
  existential branch, with their common universal/existential cell counted
  once.  Those two branch bodies contain an arbitrary carrier code for the
  preceding truth application.  This file therefore constructs their codes
  directly from the literal successor-row polynomials; it never decodes that
  carrier element into a metatheoretic [formula].

  Constructor separation itself is a fixed PA fact.  We isolate it through
  fixed principal-witness formulas and prove all eight principal collisions
  in PA.  What is not silently assumed is the proof-code transformation

      Ex8 (principal /\ opaque-lower-part)  ->  Ex8 principal.

  Compiling that transformation over a nonstandard opaque formula requires
  the formula/context shift traces used by eight existential eliminations.
  The public projection interface below asks precisely for the two local
  projection endpoints.  Given them and a local copy of the fixed principal
  collision, the final theorem constructs the exact curried pair implication
  expected by [RawCodedPALocalFiniteDisjunctionPairFamily].  Thus the missing
  resource is an explicit object proof, never semantic validity.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTotality
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthConstructorBranchDisjointness
  RawCodedPAProvability
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedProofAssumptionLeaf
  RawCodedProofBinaryConstructors
  RawCodedProofImpIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofFiniteDisjunctionMatrix.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthBinderOffDiagonalExclusivity.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthConstructorBranchDisjointness.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofFiniteDisjunctionMatrix.

(** ------------------------------------------------------------------
    Exact enumeration of the eight cells. *)

Inductive DynamicTruthBinderOffDiagonalCell : Type :=
| DTBODSigmaAllPiImp
| DTBODSigmaAllPiAnd
| DTBODSigmaAllPiOr
| DTBODSigmaAllPiEx
| DTBODSigmaImpFalseLeftPiEx
| DTBODSigmaImpTrueRightPiEx
| DTBODSigmaAndPiEx
| DTBODSigmaOrPiEx.

Definition dynamicTruthBinderOffDiagonalSigmaBranch
    (cell : DynamicTruthBinderOffDiagonalCell)
    : DynamicTruthSigmaConstructorBranch :=
  match cell with
  | DTBODSigmaAllPiImp
  | DTBODSigmaAllPiAnd
  | DTBODSigmaAllPiOr
  | DTBODSigmaAllPiEx => DTSigmaAll
  | DTBODSigmaImpFalseLeftPiEx => DTSigmaImpFalseLeft
  | DTBODSigmaImpTrueRightPiEx => DTSigmaImpTrueRight
  | DTBODSigmaAndPiEx => DTSigmaAnd
  | DTBODSigmaOrPiEx => DTSigmaOr
  end.

Definition dynamicTruthBinderOffDiagonalPiBranch
    (cell : DynamicTruthBinderOffDiagonalCell)
    : DynamicTruthPiConstructorBranch :=
  match cell with
  | DTBODSigmaAllPiImp => DTPiImp
  | DTBODSigmaAllPiAnd => DTPiAnd
  | DTBODSigmaAllPiOr => DTPiOr
  | DTBODSigmaAllPiEx
  | DTBODSigmaImpFalseLeftPiEx
  | DTBODSigmaImpTrueRightPiEx
  | DTBODSigmaAndPiEx
  | DTBODSigmaOrPiEx => DTPiEx
  end.

Definition dynamicTruthBinderOffDiagonalCells :
    list DynamicTruthBinderOffDiagonalCell :=
  [ DTBODSigmaAllPiImp;
    DTBODSigmaAllPiAnd;
    DTBODSigmaAllPiOr;
    DTBODSigmaAllPiEx;
    DTBODSigmaImpFalseLeftPiEx;
    DTBODSigmaImpTrueRightPiEx;
    DTBODSigmaAndPiEx;
    DTBODSigmaOrPiEx ].

Lemma dynamicTruthBinderOffDiagonalCells_length :
  length dynamicTruthBinderOffDiagonalCells = 8.
Proof. reflexivity. Qed.

Lemma dynamicTruthBinderOffDiagonalCells_complete : forall cell,
  In cell dynamicTruthBinderOffDiagonalCells.
Proof. intros []; cbn; intuition. Qed.

Lemma dynamicTruthBinderOffDiagonal_branches_disjoint : forall cell,
  DynamicTruthConstructorBranchesDisjoint
    (dynamicTruthBinderOffDiagonalSigmaBranch cell)
    (dynamicTruthBinderOffDiagonalPiBranch cell).
Proof. intros []; cbn; discriminate. Qed.

Lemma dynamicTruthBinderOffDiagonal_touches_binder : forall cell,
  dynamicTruthBinderOffDiagonalSigmaBranch cell = DTSigmaAll \/
  dynamicTruthBinderOffDiagonalPiBranch cell = DTPiEx.
Proof. intros []; cbn; intuition. Qed.

(** ------------------------------------------------------------------
    Literal carrier branch codes.

    Fixed branches retain their already audited standard code.  Only the
    two lower-dependent branches are rebuilt, and their lower applications
    occur as carrier arguments of the raw row constructors. *)

Definition rawDynamicTruthSigmaCarrierConstructorEx8BranchCode
    (M : RawPAModel) (branch : DynamicTruthSigmaConstructorBranch)
    (lowerPiApplication : M) : M :=
  match branch with
  | DTSigmaAll =>
      rawFormulaEx8Code M
        (rawDynamicTruthSigmaUniversalCode M lowerPiApplication)
  | _ =>
      rawDynamicTruthSigmaConstructorEx8BranchCode M branch pBot
  end.

Definition rawDynamicTruthPiCarrierConstructorEx8BranchCode
    (M : RawPAModel) (branch : DynamicTruthPiConstructorBranch)
    (lowerSigmaApplication : M) : M :=
  match branch with
  | DTPiEx =>
      rawDynamicTruthPiFormulaEx8Code M
        (rawDynamicTruthPiExistentialCode M lowerSigmaApplication)
  | _ =>
      rawDynamicTruthPiConstructorEx8BranchCode M branch pBot
  end.

Definition rawDynamicTruthBinderOffDiagonalSigmaBranchCode
    (M : RawPAModel) (cell : DynamicTruthBinderOffDiagonalCell)
    (lowerPiApplication : M) : M :=
  rawDynamicTruthSigmaCarrierConstructorEx8BranchCode M
    (dynamicTruthBinderOffDiagonalSigmaBranch cell)
    lowerPiApplication.

Definition rawDynamicTruthBinderOffDiagonalPiBranchCode
    (M : RawPAModel) (cell : DynamicTruthBinderOffDiagonalCell)
    (lowerSigmaApplication : M) : M :=
  rawDynamicTruthPiCarrierConstructorEx8BranchCode M
    (dynamicTruthBinderOffDiagonalPiBranch cell)
    lowerSigmaApplication.

Lemma rawDynamicTruthSigmaCarrierAllBranchCode_literal : forall
    (M : RawPAModel) lowerPiApplication,
  rawDynamicTruthSigmaCarrierConstructorEx8BranchCode M
    DTSigmaAll lowerPiApplication =
  rawFormulaEx8Code M
    (rawDynamicTruthSigmaUniversalCode M lowerPiApplication).
Proof. reflexivity. Qed.

Lemma rawDynamicTruthPiCarrierExBranchCode_literal : forall
    (M : RawPAModel) lowerSigmaApplication,
  rawDynamicTruthPiCarrierConstructorEx8BranchCode M
    DTPiEx lowerSigmaApplication =
  rawDynamicTruthPiFormulaEx8Code M
    (rawDynamicTruthPiExistentialCode M lowerSigmaApplication).
Proof. reflexivity. Qed.

Lemma rawDynamicTruthSigmaCarrierConstructorEx8BranchCode_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall branch lowerPi,
  RawCodedFormulaAtomicallyAdequate M lowerPi ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthSigmaCarrierConstructorEx8BranchCode
      M branch lowerPi).
Proof.
  intros M hPA branch lowerPi hlower.
  destruct branch; cbn
    [rawDynamicTruthSigmaCarrierConstructorEx8BranchCode].
  all: try apply raw_fixedFormulaNumeral_atomically_adequate; try exact hPA.
  unfold rawFormulaEx8Code.
  repeat apply raw_formulaExCode_atomically_adequate; try exact hPA.
  unfold rawDynamicTruthSigmaUniversalCode.
  apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
  - exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthSigmaRowUniversalPrefixFormula).
  - exact (rawDynamicTruthSigmaNoBinderCode_atomically_adequate
      M hPA lowerPi hlower).
Qed.

Lemma rawDynamicTruthPiCarrierConstructorEx8BranchCode_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall branch lowerSigma,
  RawCodedFormulaAtomicallyAdequate M lowerSigma ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthPiCarrierConstructorEx8BranchCode
      M branch lowerSigma).
Proof.
  intros M hPA branch lowerSigma hlower.
  destruct branch; cbn
    [rawDynamicTruthPiCarrierConstructorEx8BranchCode].
  all: try apply raw_fixedFormulaNumeral_atomically_adequate; try exact hPA.
  unfold rawDynamicTruthPiFormulaEx8Code.
  repeat apply raw_formulaExCode_atomically_adequate; try exact hPA.
  unfold rawDynamicTruthPiExistentialCode.
  apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
  - exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthPiRowExistentialPrefixFormula).
  - exact (rawDynamicTruthPiNoBinderCode_atomically_adequate
      M hPA lowerSigma hlower).
Qed.

Corollary rawDynamicTruthBinderOffDiagonalSigmaBranchCode_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall cell lowerPi,
  RawCodedFormulaAtomicallyAdequate M lowerPi ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthBinderOffDiagonalSigmaBranchCode M cell lowerPi).
Proof.
  intros M hPA cell lowerPi hlower.
  apply rawDynamicTruthSigmaCarrierConstructorEx8BranchCode_adequate;
    assumption.
Qed.

Corollary rawDynamicTruthBinderOffDiagonalPiBranchCode_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall cell lowerSigma,
  RawCodedFormulaAtomicallyAdequate M lowerSigma ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthBinderOffDiagonalPiBranchCode M cell lowerSigma).
Proof.
  intros M hPA cell lowerSigma hlower.
  apply rawDynamicTruthPiCarrierConstructorEx8BranchCode_adequate;
    assumption.
Qed.

(** ------------------------------------------------------------------
    Fixed principal-witness formulas and their PA collision. *)

Definition dynamicTruthSigmaPrincipalBody
    (branch : DynamicTruthSigmaConstructorBranch) : formula :=
  match branch with
  | DTSigmaImpFalseLeft | DTSigmaImpTrueRight =>
      formulaImpCodeTermAt (tVar 10) (tVar 6) (tVar 4)
  | DTSigmaAnd =>
      formulaAndCodeTermAt (tVar 10) (tVar 6) (tVar 4)
  | DTSigmaOr =>
      formulaOrCodeTermAt (tVar 10) (tVar 6) (tVar 4)
  | DTSigmaEx => formulaExCodeTermAt (tVar 10) (tVar 6)
  | DTSigmaAll => formulaAllCodeTermAt (tVar 10) (tVar 6)
  end.

Definition dynamicTruthPiPrincipalBody
    (branch : DynamicTruthPiConstructorBranch) : formula :=
  match branch with
  | DTPiImp => formulaImpCodeTermAt (tVar 10) (tVar 6) (tVar 4)
  | DTPiAnd => formulaAndCodeTermAt (tVar 10) (tVar 6) (tVar 4)
  | DTPiOr => formulaOrCodeTermAt (tVar 10) (tVar 6) (tVar 4)
  | DTPiAll => formulaAllCodeTermAt (tVar 10) (tVar 6)
  | DTPiEx => formulaExCodeTermAt (tVar 10) (tVar 6)
  end.

Definition dynamicTruthSigmaPrincipalEx8Formula
    (branch : DynamicTruthSigmaConstructorBranch) : formula :=
  fixedLevelEx8 (dynamicTruthSigmaPrincipalBody branch).

Definition dynamicTruthPiPrincipalEx8Formula
    (branch : DynamicTruthPiConstructorBranch) : formula :=
  fixedLevelEx8 (dynamicTruthPiPrincipalBody branch).

Lemma raw_sat_dynamicTruthSigmaPrincipalEx8Formula_principal : forall
    (M : RawPAModel) e branch,
  raw_formula_sat M e (dynamicTruthSigmaPrincipalEx8Formula branch) ->
  RawFormulaHasPrincipalConstructor M
    (dynamicTruthSigmaBranchPrincipal branch) (e 2).
Proof.
  intros M e branch hprincipal.
  destruct branch;
    unfold dynamicTruthSigmaPrincipalEx8Formula,
      dynamicTruthSigmaPrincipalBody, fixedLevelEx8 in hprincipal;
    cbn [raw_formula_sat] in hprincipal;
    destruct hprincipal as
      (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & hcode).
  - apply (proj1 (raw_sat_formulaImpCodeTermAt_iff M _ _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode. exists a1, a3. exact hcode.
  - apply (proj1 (raw_sat_formulaImpCodeTermAt_iff M _ _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode. exists a1, a3. exact hcode.
  - apply (proj1 (raw_sat_formulaAndCodeTermAt_iff M _ _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode. exists a1, a3. exact hcode.
  - apply (proj1 (raw_sat_formulaOrCodeTermAt_iff M _ _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode. exists a1, a3. exact hcode.
  - apply (proj1 (raw_sat_formulaExCodeTermAt_iff M _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode. exists a1. exact hcode.
  - apply (proj1 (raw_sat_formulaAllCodeTermAt_iff M _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode. exists a1. exact hcode.
Qed.

Lemma raw_sat_dynamicTruthPiPrincipalEx8Formula_principal : forall
    (M : RawPAModel) e branch,
  raw_formula_sat M e (dynamicTruthPiPrincipalEx8Formula branch) ->
  RawFormulaHasPrincipalConstructor M
    (dynamicTruthPiBranchPrincipal branch) (e 2).
Proof.
  intros M e branch hprincipal.
  destruct branch;
    unfold dynamicTruthPiPrincipalEx8Formula,
      dynamicTruthPiPrincipalBody, fixedLevelEx8 in hprincipal;
    cbn [raw_formula_sat] in hprincipal;
    destruct hprincipal as
      (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & hcode).
  - apply (proj1 (raw_sat_formulaImpCodeTermAt_iff M _ _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode. exists a1, a3. exact hcode.
  - apply (proj1 (raw_sat_formulaAndCodeTermAt_iff M _ _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode. exists a1, a3. exact hcode.
  - apply (proj1 (raw_sat_formulaOrCodeTermAt_iff M _ _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode. exists a1, a3. exact hcode.
  - apply (proj1 (raw_sat_formulaAllCodeTermAt_iff M _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode. exists a1. exact hcode.
  - apply (proj1 (raw_sat_formulaExCodeTermAt_iff M _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode. exists a1. exact hcode.
Qed.

Definition dynamicTruthBinderPrincipalCollisionFormula
    (cell : DynamicTruthBinderOffDiagonalCell) : formula :=
  pImp
    (dynamicTruthSigmaPrincipalEx8Formula
      (dynamicTruthBinderOffDiagonalSigmaBranch cell))
    (pImp
      (dynamicTruthPiPrincipalEx8Formula
        (dynamicTruthBinderOffDiagonalPiBranch cell))
      pBot).

Theorem dynamicTruthBinderPrincipalCollisionFormula_raw_valid : forall cell,
  forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (dynamicTruthBinderPrincipalCollisionFormula cell).
Proof.
  intros cell M hPA e.
  unfold dynamicTruthBinderPrincipalCollisionFormula.
  cbn [raw_formula_sat]. intros hsigma hpi.
  exact (raw_formulaPrincipalConstructors_disjoint M hPA
    (dynamicTruthSigmaBranchPrincipal
      (dynamicTruthBinderOffDiagonalSigmaBranch cell))
    (dynamicTruthPiBranchPrincipal
      (dynamicTruthBinderOffDiagonalPiBranch cell))
    (e 2)
    (dynamicTruthBinderOffDiagonal_branches_disjoint cell)
    (raw_sat_dynamicTruthSigmaPrincipalEx8Formula_principal
      M e (dynamicTruthBinderOffDiagonalSigmaBranch cell) hsigma)
    (raw_sat_dynamicTruthPiPrincipalEx8Formula_principal
      M e (dynamicTruthBinderOffDiagonalPiBranch cell) hpi)).
Qed.

Theorem PA_proves_dynamicTruthBinderPrincipalCollisionFormula : forall cell,
  Formula.BProv Formula.Ax_s []
    (dynamicTruthBinderPrincipalCollisionFormula cell).
Proof.
  intros cell.
  apply PA_proves_constructorDisjoint_open_formula_of_raw_valid.
  exact (dynamicTruthBinderPrincipalCollisionFormula_raw_valid cell).
Qed.

Definition rawDynamicTruthBinderSigmaPrincipalCode
    (M : RawPAModel) (cell : DynamicTruthBinderOffDiagonalCell) : M :=
  rawFixedFormulaNumeralCode M
    (dynamicTruthSigmaPrincipalEx8Formula
      (dynamicTruthBinderOffDiagonalSigmaBranch cell)).

Definition rawDynamicTruthBinderPiPrincipalCode
    (M : RawPAModel) (cell : DynamicTruthBinderOffDiagonalCell) : M :=
  rawFixedFormulaNumeralCode M
    (dynamicTruthPiPrincipalEx8Formula
      (dynamicTruthBinderOffDiagonalPiBranch cell)).

Definition rawDynamicTruthBinderPrincipalCollisionCode
    (M : RawPAModel) (cell : DynamicTruthBinderOffDiagonalCell) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthBinderSigmaPrincipalCode M cell)
    (rawFormulaImpCode M
      (rawDynamicTruthBinderPiPrincipalCode M cell)
      (rawFormulaBotCode M)).

Lemma rawDynamicTruthBinderPrincipalCollisionCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall cell,
  rawDynamicTruthBinderPrincipalCollisionCode M cell =
  rawQuotedFormulaCode M
    (dynamicTruthBinderPrincipalCollisionFormula cell).
Proof.
  intros M hPA cell.
  unfold rawDynamicTruthBinderPrincipalCollisionCode,
    rawDynamicTruthBinderSigmaPrincipalCode,
    rawDynamicTruthBinderPiPrincipalCode,
    dynamicTruthBinderPrincipalCollisionFormula.
  rewrite !rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  reflexivity.
Qed.

Theorem raw_codedPAProofOf_dynamicTruthBinderPrincipalCollision : forall
    (M : RawPAModel), RawPASatisfies M -> forall cell,
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthBinderPrincipalCollisionCode M cell)
      certificate.
Proof.
  intros M hPA cell.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    (dynamicTruthBinderPrincipalCollisionFormula cell)
    (PA_proves_dynamicTruthBinderPrincipalCollisionFormula cell))
    as [certificate hcertificate].
  exists certificate.
  rewrite rawDynamicTruthBinderPrincipalCollisionCode_eq_quoted
    by exact hPA.
  rewrite (rawQuotedFormulaCode_standard M hPA).
  exact hcertificate.
Qed.

(** ------------------------------------------------------------------
    Narrow carrier projection interface.

    Both endpoints live in the exact common matrix context.  A later
    compiler may discharge them by eight existential eliminations using the
    checked shift traces of the lower applications. *)

Definition RawDynamicTruthBinderPrincipalProjectionInterfaceAt
    (M : RawPAModel) (context : M)
    (cell : DynamicTruthBinderOffDiagonalCell)
    (lowerPiApplication lowerSigmaApplication : M) : Prop :=
  exists sigmaProjectionRoot piProjectionRoot : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthBinderOffDiagonalSigmaBranchCode M cell
          lowerPiApplication)
        (rawDynamicTruthBinderSigmaPrincipalCode M cell))
      sigmaProjectionRoot /\
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthBinderOffDiagonalPiBranchCode M cell
          lowerSigmaApplication)
        (rawDynamicTruthBinderPiPrincipalCode M cell))
      piProjectionRoot.

Arguments RawDynamicTruthBinderPrincipalProjectionInterfaceAt
  M context cell lowerPiApplication lowerSigmaApplication : clear implicits.

Definition RawDynamicTruthBinderPrincipalCollisionAvailableAt
    (M : RawPAModel) (context : M)
    (cell : DynamicTruthBinderOffDiagonalCell) : Prop :=
  exists principalCollisionRoot : M,
    RawCodedPALocalProofOf M context
      (rawDynamicTruthBinderPrincipalCollisionCode M cell)
      principalCollisionRoot.

Arguments RawDynamicTruthBinderPrincipalCollisionAvailableAt
  M context cell : clear implicits.

Definition RawDynamicTruthBinderOffDiagonalProofInputsAt
    (M : RawPAModel) (context : M)
    (cell : DynamicTruthBinderOffDiagonalCell)
    (lowerPiApplication lowerSigmaApplication : M) : Prop :=
  RawDynamicTruthBinderPrincipalProjectionInterfaceAt
    M context cell lowerPiApplication lowerSigmaApplication /\
  RawDynamicTruthBinderPrincipalCollisionAvailableAt M context cell.

Arguments RawDynamicTruthBinderOffDiagonalProofInputsAt
  M context cell lowerPiApplication lowerSigmaApplication : clear implicits.

(** The exact pair-family target code. *)
Definition rawDynamicTruthBinderOffDiagonalPairCollisionCode
    (M : RawPAModel) (cell : DynamicTruthBinderOffDiagonalCell)
    (lowerPiApplication lowerSigmaApplication : M) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthBinderOffDiagonalSigmaBranchCode M cell
      lowerPiApplication)
    (rawFormulaImpCode M
      (rawDynamicTruthBinderOffDiagonalPiBranchCode M cell
        lowerSigmaApplication)
      (rawFormulaBotCode M)).

(** Compose the two principal projections with the fixed constructor
    collision.  Every context extension is performed by the guarded
    adequacy-based transplant theorem; no weakening step is implicit. *)
Theorem raw_codedPALocalProofOf_dynamicTruthBinderOffDiagonalPairCollision :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context cell lowerPiApplication lowerSigmaApplication,
  RawContextListRealizable M context ->
  RawCodedFormulaAtomicallyAdequate M lowerPiApplication ->
  RawCodedFormulaAtomicallyAdequate M lowerSigmaApplication ->
  RawDynamicTruthBinderOffDiagonalProofInputsAt
    M context cell lowerPiApplication lowerSigmaApplication ->
  exists pairRoot : M,
    RawCodedPALocalProofOf M context
      (rawDynamicTruthBinderOffDiagonalPairCollisionCode M cell
        lowerPiApplication lowerSigmaApplication)
      pairRoot.
Proof.
  intros M hPA context cell lowerPi lowerSigma hcontext
    hlowerPi hlowerSigma
    ((sigmaProjectionRoot & piProjectionRoot &
        hsigmaProjection & hpiProjection) &
      (principalCollisionRoot & hprincipalCollision)).
  set (sigmaBranch :=
    rawDynamicTruthBinderOffDiagonalSigmaBranchCode M cell lowerPi).
  set (piBranch :=
    rawDynamicTruthBinderOffDiagonalPiBranchCode M cell lowerSigma).
  set (sigmaPrincipal :=
    rawDynamicTruthBinderSigmaPrincipalCode M cell).
  set (piPrincipal :=
    rawDynamicTruthBinderPiPrincipalCode M cell).
  assert (hsigmaAdequate : RawCodedFormulaAtomicallyAdequate M sigmaBranch).
  {
    unfold sigmaBranch.
    exact (rawDynamicTruthBinderOffDiagonalSigmaBranchCode_adequate
      M hPA cell lowerPi hlowerPi).
  }
  assert (hpiAdequate : RawCodedFormulaAtomicallyAdequate M piBranch).
  {
    unfold piBranch.
    exact (rawDynamicTruthBinderOffDiagonalPiBranchCode_adequate
      M hPA cell lowerSigma hlowerSigma).
  }
  set (sigmaContext := rawListNode M sigmaBranch context).
  assert (hsigmaContext : RawContextListRealizable M sigmaContext).
  {
    unfold sigmaContext.
    exact (raw_contextList_cons_realizable M hPA
      context sigmaBranch hcontext).
  }
  fold sigmaBranch sigmaPrincipal in hsigmaProjection.
  fold piBranch piPrincipal in hpiProjection.
  fold sigmaPrincipal piPrincipal in hprincipalCollision.
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    context sigmaBranch
    (rawFormulaImpCode M sigmaBranch sigmaPrincipal)
    sigmaProjectionRoot hsigmaAdequate hcontext hsigmaProjection)
    as [sigmaProjectionSigma hsigmaProjectionSigma].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    context sigmaBranch
    (rawFormulaImpCode M piBranch piPrincipal)
    piProjectionRoot hsigmaAdequate hcontext hpiProjection)
    as [piProjectionSigma hpiProjectionSigma].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    context sigmaBranch
    (rawFormulaImpCode M sigmaPrincipal
      (rawFormulaImpCode M piPrincipal (rawFormulaBotCode M)))
    principalCollisionRoot hsigmaAdequate hcontext hprincipalCollision)
    as [principalCollisionSigma hprincipalCollisionSigma].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    context sigmaBranch hcontext) as hsigmaHead.
  pose proof (raw_codedPALocalProofOf_impE M hPA sigmaContext
    sigmaBranch sigmaPrincipal sigmaProjectionSigma
    (rawProofAssumptionRoot M sigmaContext sigmaBranch)
    hsigmaProjectionSigma hsigmaHead) as hsigmaPrincipalSigma.
  set (piContext := rawListNode M piBranch sigmaContext).
  assert (hpiContext : RawContextListRealizable M piContext).
  {
    unfold piContext.
    exact (raw_contextList_cons_realizable M hPA
      sigmaContext piBranch hsigmaContext).
  }
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    sigmaContext piBranch sigmaPrincipal
    (rawProofImpERoot M sigmaContext sigmaBranch sigmaPrincipal
      sigmaProjectionSigma
      (rawProofAssumptionRoot M sigmaContext sigmaBranch))
    hpiAdequate hsigmaContext hsigmaPrincipalSigma)
    as [sigmaPrincipalPi hsigmaPrincipalPi].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    sigmaContext piBranch
    (rawFormulaImpCode M piBranch piPrincipal)
    piProjectionSigma hpiAdequate hsigmaContext hpiProjectionSigma)
    as [piProjectionPi hpiProjectionPi].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    sigmaContext piBranch
    (rawFormulaImpCode M sigmaPrincipal
      (rawFormulaImpCode M piPrincipal (rawFormulaBotCode M)))
    principalCollisionSigma hpiAdequate hsigmaContext
    hprincipalCollisionSigma)
    as [principalCollisionPi hprincipalCollisionPi].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    sigmaContext piBranch hsigmaContext) as hpiHead.
  pose proof (raw_codedPALocalProofOf_impE M hPA piContext
    piBranch piPrincipal piProjectionPi
    (rawProofAssumptionRoot M piContext piBranch)
    hpiProjectionPi hpiHead) as hpiPrincipalPi.
  pose proof (raw_codedPALocalProofOf_impE M hPA piContext
    sigmaPrincipal
    (rawFormulaImpCode M piPrincipal (rawFormulaBotCode M))
    principalCollisionPi sigmaPrincipalPi
    hprincipalCollisionPi hsigmaPrincipalPi) as hpiPrincipalToBottom.
  pose proof (raw_codedPALocalProofOf_impE M hPA piContext
    piPrincipal (rawFormulaBotCode M)
    (rawProofImpERoot M piContext sigmaPrincipal
      (rawFormulaImpCode M piPrincipal (rawFormulaBotCode M))
      principalCollisionPi sigmaPrincipalPi)
    (rawProofImpERoot M piContext piBranch piPrincipal
      piProjectionPi
      (rawProofAssumptionRoot M piContext piBranch))
    hpiPrincipalToBottom hpiPrincipalPi) as hbottom.
  pose proof (raw_codedPALocalProofOf_impI M hPA sigmaContext
    piBranch (rawFormulaBotCode M)
    (rawProofImpERoot M piContext piPrincipal (rawFormulaBotCode M)
      (rawProofImpERoot M piContext sigmaPrincipal
        (rawFormulaImpCode M piPrincipal (rawFormulaBotCode M))
        principalCollisionPi sigmaPrincipalPi)
      (rawProofImpERoot M piContext piBranch piPrincipal
        piProjectionPi
        (rawProofAssumptionRoot M piContext piBranch)))
    hbottom) as hpiImplication.
  exists (rawProofImpIRoot M context sigmaBranch
    (rawFormulaImpCode M piBranch (rawFormulaBotCode M))
    (rawProofImpIRoot M sigmaContext piBranch (rawFormulaBotCode M)
      (rawProofImpERoot M piContext piPrincipal (rawFormulaBotCode M)
        (rawProofImpERoot M piContext sigmaPrincipal
          (rawFormulaImpCode M piPrincipal (rawFormulaBotCode M))
          principalCollisionPi sigmaPrincipalPi)
        (rawProofImpERoot M piContext piBranch piPrincipal
          piProjectionPi
          (rawProofAssumptionRoot M piContext piBranch))))).
  unfold rawDynamicTruthBinderOffDiagonalPairCollisionCode.
  fold sigmaBranch piBranch.
  exact (raw_codedPALocalProofOf_impI M hPA context sigmaBranch
    (rawFormulaImpCode M piBranch (rawFormulaBotCode M))
    (rawProofImpIRoot M sigmaContext piBranch (rawFormulaBotCode M)
      (rawProofImpERoot M piContext piPrincipal (rawFormulaBotCode M)
        (rawProofImpERoot M piContext sigmaPrincipal
          (rawFormulaImpCode M piPrincipal (rawFormulaBotCode M))
          principalCollisionPi sigmaPrincipalPi)
        (rawProofImpERoot M piContext piBranch piPrincipal
          piProjectionPi
          (rawProofAssumptionRoot M piContext piBranch))))
    hpiImplication).
Qed.

(** This is the literal one-cell shape consumed by the finite matrix
    assembler, without any additional wrapper or formula translation. *)
Corollary raw_dynamicTruthBinderOffDiagonal_matrix_pair : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context cell lowerPiApplication lowerSigmaApplication,
  RawContextListRealizable M context ->
  RawCodedFormulaAtomicallyAdequate M lowerPiApplication ->
  RawCodedFormulaAtomicallyAdequate M lowerSigmaApplication ->
  RawDynamicTruthBinderOffDiagonalProofInputsAt
    M context cell lowerPiApplication lowerSigmaApplication ->
  exists pairRoot : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthBinderOffDiagonalSigmaBranchCode M cell
          lowerPiApplication)
        (rawFormulaImpCode M
          (rawDynamicTruthBinderOffDiagonalPiBranchCode M cell
            lowerSigmaApplication)
          (rawFormulaBotCode M)))
      pairRoot.
Proof.
  intros M hPA context cell lowerPi lowerSigma
    hcontext hlowerPi hlowerSigma hinputs.
  exact (raw_codedPALocalProofOf_dynamicTruthBinderOffDiagonalPairCollision
    M hPA context cell lowerPi lowerSigma
    hcontext hlowerPi hlowerSigma hinputs).
Qed.

(** Singleton rows make the compatibility with the generic matrix predicate
    completely explicit.  Larger native rows obtain this same member by
    selecting the corresponding [cell] in their pair-family callback. *)
Corollary raw_dynamicTruthBinderOffDiagonal_singleton_pair_family : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context cell lowerPiApplication lowerSigmaApplication,
  RawContextListRealizable M context ->
  RawCodedFormulaAtomicallyAdequate M lowerPiApplication ->
  RawCodedFormulaAtomicallyAdequate M lowerSigmaApplication ->
  RawDynamicTruthBinderOffDiagonalProofInputsAt
    M context cell lowerPiApplication lowerSigmaApplication ->
  RawCodedPALocalFiniteDisjunctionPairFamily M context
    [rawDynamicTruthBinderOffDiagonalSigmaBranchCode M cell
      lowerPiApplication]
    [rawDynamicTruthBinderOffDiagonalPiBranchCode M cell
      lowerSigmaApplication]
    (rawFormulaBotCode M).
Proof.
  intros M hPA context cell lowerPi lowerSigma
    hcontext hlowerPi hlowerSigma hinputs
    left hleft right hright.
  cbn in hleft, hright.
  destruct hleft as [hleft | hleft]; [subst left | contradiction].
  destruct hright as [hright | hright]; [subst right | contradiction].
  exact (raw_dynamicTruthBinderOffDiagonal_matrix_pair M hPA
    context cell lowerPi lowerSigma
    hcontext hlowerPi hlowerSigma hinputs).
Qed.

End PABoundedRawCodedDynamicTruthBinderOffDiagonalExclusivity.
