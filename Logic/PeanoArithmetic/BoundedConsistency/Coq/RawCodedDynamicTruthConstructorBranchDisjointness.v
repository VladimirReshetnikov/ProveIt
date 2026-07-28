(**
  Constructor-disjoint cells of the native dynamic-truth successor rows.

  Every non-quantifier-free row branch starts by asserting that the common
  formula root has a particular outer constructor.  Distinct constructor
  tags, and binary versus unary arity, are already contradictory in every
  PA model.  This file packages that observation once and applies it to the
  literal eight-witness Sigma and Pi branches.

  The implication/implication, conjunction/conjunction,
  disjunction/disjunction, existential/existential, and
  universal/universal cells are deliberately absent: their contradiction
  depends on lower truth information.  Quantifier-free cells are absent as
  well.

  There is an important standard/nonstandard boundary.  The final Sigma-All
  and Pi-Ex branches contain the preceding truth formula as syntax.  A
  metatheoretic [formula] argument therefore gives a PA theorem for every
  *standard* preceding formula, but it does not compile a branch containing
  an arbitrary carrier-coded lower application.  Only the sixteen cells
  enumerated by [dynamicTruthFixedConstructorCells] below are immediately
  lower-independent and ready for the carrier-level dynamic matrix.  The
  other eight off-diagonal cells still need a carrier-parametric principal-
  projection proof constructor.  No complete local matrix is claimed here.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation
  PolynomialPairInjectivity
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTotality
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedPAProvability
  RawCodedRestrictedPAProof
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedProofAssumptionLeaf
  RawCodedProofBinaryConstructors
  RawCodedPAProofImpICertificates
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedDynamicTruthPairedSuccessorAdequacy.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthConstructorBranchDisjointness.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPAProofImpICertificates.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.

(** ------------------------------------------------------------------
    One arity-and-tag separation theorem. *)

Inductive RawFormulaPrincipalConstructor : Type :=
| RawFormulaPrincipalBinary (tag : nat)
| RawFormulaPrincipalUnary (tag : nat).

Definition RawFormulaHasPrincipalConstructor (M : RawPAModel)
    (kind : RawFormulaPrincipalConstructor) (root : M) : Prop :=
  match kind with
  | RawFormulaPrincipalBinary tag =>
      exists left right : M,
        root = rawCodeList3 M (rawNumeralValue M tag) left right
  | RawFormulaPrincipalUnary tag =>
      exists child : M,
        root = rawCodeList2 M (rawNumeralValue M tag) child
  end.

Arguments RawFormulaHasPrincipalConstructor M kind root : clear implicits.

(** Equality of constructor codes exposes both list arity and the standard
    numeral tag.  Keeping this proof generic is the main economy of the
    module: all literal branch instances below use this one lemma. *)
Theorem raw_formulaPrincipalConstructors_disjoint : forall
    (M : RawPAModel), RawPASatisfies M -> forall leftKind rightKind root,
  leftKind <> rightKind ->
  RawFormulaHasPrincipalConstructor M leftKind root ->
  RawFormulaHasPrincipalConstructor M rightKind root -> False.
Proof.
  intros M hPA leftKind rightKind root hdifferent.
  destruct leftKind as [leftTag | leftTag];
    destruct rightKind as [rightTag | rightTag];
    unfold RawFormulaHasPrincipalConstructor.
  - intros (left & right & hleft) (left' & right' & hright).
    assert (hcode :
        rawCodeList3 M (rawNumeralValue M leftTag) left right =
        rawCodeList3 M (rawNumeralValue M rightTag) left' right').
    { rewrite <- hleft, <- hright. reflexivity. }
    destruct (raw_codeList3_injective M
      (rawListNode_injective M hPA) _ _ _ _ _ _ hcode)
      as [htag _].
    apply (rawNumeralValue_injective M hPA leftTag rightTag) in htag.
    subst rightTag. apply hdifferent. reflexivity.
  - intros (left & right & hleft) (child & hright).
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M rightTag) child
      (rawNumeralValue M leftTag) left right).
    rewrite <- hleft, <- hright. reflexivity.
  - intros (child & hleft) (left & right & hright).
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M leftTag) child
      (rawNumeralValue M rightTag) left right).
    rewrite <- hleft, <- hright. reflexivity.
  - intros (leftChild & hleft) (rightChild & hright).
    assert (hcode :
        rawCodeList2 M (rawNumeralValue M leftTag) leftChild =
        rawCodeList2 M (rawNumeralValue M rightTag) rightChild).
    { rewrite <- hleft, <- hright. reflexivity. }
    destruct (raw_codeList2_injective M
      (rawListNode_injective M hPA) _ _ _ _ hcode) as [htag _].
    apply (rawNumeralValue_injective M hPA leftTag rightTag) in htag.
    subst rightTag. apply hdifferent. reflexivity.
Qed.

(** ------------------------------------------------------------------
    A finite name for each non-QF branch and its principal constructor. *)

Inductive DynamicTruthSigmaConstructorBranch : Type :=
| DTSigmaImpFalseLeft
| DTSigmaImpTrueRight
| DTSigmaAnd
| DTSigmaOr
| DTSigmaEx
| DTSigmaAll.

Inductive DynamicTruthPiConstructorBranch : Type :=
| DTPiImp
| DTPiAnd
| DTPiOr
| DTPiAll
| DTPiEx.

Definition dynamicTruthSigmaBranchPrincipal
    (branch : DynamicTruthSigmaConstructorBranch)
    : RawFormulaPrincipalConstructor :=
  match branch with
  | DTSigmaImpFalseLeft | DTSigmaImpTrueRight =>
      RawFormulaPrincipalBinary 2
  | DTSigmaAnd => RawFormulaPrincipalBinary 3
  | DTSigmaOr => RawFormulaPrincipalBinary 4
  | DTSigmaEx => RawFormulaPrincipalUnary 6
  | DTSigmaAll => RawFormulaPrincipalUnary 5
  end.

Definition dynamicTruthPiBranchPrincipal
    (branch : DynamicTruthPiConstructorBranch)
    : RawFormulaPrincipalConstructor :=
  match branch with
  | DTPiImp => RawFormulaPrincipalBinary 2
  | DTPiAnd => RawFormulaPrincipalBinary 3
  | DTPiOr => RawFormulaPrincipalBinary 4
  | DTPiAll => RawFormulaPrincipalUnary 5
  | DTPiEx => RawFormulaPrincipalUnary 6
  end.

Definition DynamicTruthConstructorBranchesDisjoint
    (sigmaBranch : DynamicTruthSigmaConstructorBranch)
    (piBranch : DynamicTruthPiConstructorBranch) : Prop :=
  dynamicTruthSigmaBranchPrincipal sigmaBranch <>
  dynamicTruthPiBranchPrincipal piBranch.

(** A cell is fixed exactly when neither side is the branch whose body
    embeds the preceding truth formula.  Combining fixedness with principal
    disjointness leaves sixteen cells. *)
Definition DynamicTruthFixedConstructorCell
    (sigmaBranch : DynamicTruthSigmaConstructorBranch)
    (piBranch : DynamicTruthPiConstructorBranch) : Prop :=
  sigmaBranch <> DTSigmaAll /\
  piBranch <> DTPiEx /\
  DynamicTruthConstructorBranchesDisjoint sigmaBranch piBranch.

Definition dynamicTruthFixedConstructorCells :
    list (DynamicTruthSigmaConstructorBranch *
      DynamicTruthPiConstructorBranch) :=
  [ (DTSigmaImpFalseLeft, DTPiAnd);
    (DTSigmaImpFalseLeft, DTPiOr);
    (DTSigmaImpFalseLeft, DTPiAll);
    (DTSigmaImpTrueRight, DTPiAnd);
    (DTSigmaImpTrueRight, DTPiOr);
    (DTSigmaImpTrueRight, DTPiAll);
    (DTSigmaAnd, DTPiImp);
    (DTSigmaAnd, DTPiOr);
    (DTSigmaAnd, DTPiAll);
    (DTSigmaOr, DTPiImp);
    (DTSigmaOr, DTPiAnd);
    (DTSigmaOr, DTPiAll);
    (DTSigmaEx, DTPiImp);
    (DTSigmaEx, DTPiAnd);
    (DTSigmaEx, DTPiOr);
    (DTSigmaEx, DTPiAll) ].

Lemma dynamicTruthFixedConstructorCells_length :
  length dynamicTruthFixedConstructorCells = 16.
Proof. reflexivity. Qed.

Lemma dynamicTruthFixedConstructorCells_spec : forall sigmaBranch piBranch,
  In (sigmaBranch, piBranch) dynamicTruthFixedConstructorCells <->
  DynamicTruthFixedConstructorCell sigmaBranch piBranch.
Proof.
  intros sigmaBranch piBranch.
  destruct sigmaBranch, piBranch;
    unfold dynamicTruthFixedConstructorCells,
      DynamicTruthFixedConstructorCell,
      DynamicTruthConstructorBranchesDisjoint;
    simpl;
    intuition (try discriminate).
Qed.

(** The last branch in either row includes a lower formula application.
    Supplying that formula explicitly keeps these definitions literal while
    the five fixed alternatives simply ignore the parameter. *)
Definition dynamicTruthSigmaConstructorBranchBody
    (branch : DynamicTruthSigmaConstructorBranch)
    (lowerPi : formula) : formula :=
  match branch with
  | DTSigmaImpFalseLeft => dynamicTruthSigmaRowImpFalseLeftFormula
  | DTSigmaImpTrueRight => dynamicTruthSigmaRowImpTrueRightFormula
  | DTSigmaAnd => dynamicTruthSigmaRowAndFormula
  | DTSigmaOr => dynamicTruthSigmaRowOrFormula
  | DTSigmaEx => dynamicTruthSigmaRowExFormula
  | DTSigmaAll =>
      pAnd dynamicTruthSigmaRowUniversalPrefixFormula
        (fixedLevelNoBinderCounterexampleTermAt
          (Formula.rename dynamicTruthCoqLowerApplicationRenaming lowerPi)
          (tVar 9) (tVar 8) (tVar 10))
  end.

Definition dynamicTruthPiConstructorBranchBody
    (branch : DynamicTruthPiConstructorBranch)
    (lowerSigma : formula) : formula :=
  match branch with
  | DTPiImp => dynamicTruthPiRowImpFormula
  | DTPiAnd => dynamicTruthPiRowAndFormula
  | DTPiOr => dynamicTruthPiRowOrFormula
  | DTPiAll => dynamicTruthPiRowAllFormula
  | DTPiEx =>
      pAnd dynamicTruthPiRowExistentialPrefixFormula
        (fixedLevelNoBinderCounterexampleTermAt
          (Formula.rename dynamicTruthPiCoqLowerApplicationRenaming
            lowerSigma)
          (tVar 9) (tVar 8) (tVar 10))
  end.

Definition dynamicTruthSigmaConstructorEx8BranchFormula
    (branch : DynamicTruthSigmaConstructorBranch)
    (lowerPi : formula) : formula :=
  fixedLevelEx8
    (dynamicTruthSigmaConstructorBranchBody branch lowerPi).

Definition dynamicTruthPiConstructorEx8BranchFormula
    (branch : DynamicTruthPiConstructorBranch)
    (lowerSigma : formula) : formula :=
  fixedLevelEx8
    (dynamicTruthPiConstructorBranchBody branch lowerSigma).

(** On the enumerated fixed subset the apparent lower-formula arguments are
    provably irrelevant.  These equalities are what permits the sixteen
    cells to be instantiated without decoding a nonstandard predecessor
    formula into a metatheoretic syntax tree. *)
Lemma dynamicTruthSigmaConstructorBranchBody_fixed_lower_irrelevant :
    forall branch,
  branch <> DTSigmaAll -> forall lowerPi lowerPi',
  dynamicTruthSigmaConstructorBranchBody branch lowerPi =
  dynamicTruthSigmaConstructorBranchBody branch lowerPi'.
Proof.
  intros branch hfixed lowerPi lowerPi'.
  destruct branch; cbn; try reflexivity.
  exfalso. apply hfixed. reflexivity.
Qed.

Lemma dynamicTruthPiConstructorBranchBody_fixed_lower_irrelevant :
    forall branch,
  branch <> DTPiEx -> forall lowerSigma lowerSigma',
  dynamicTruthPiConstructorBranchBody branch lowerSigma =
  dynamicTruthPiConstructorBranchBody branch lowerSigma'.
Proof.
  intros branch hfixed lowerSigma lowerSigma'.
  destruct branch; cbn; try reflexivity.
  exfalso. apply hfixed. reflexivity.
Qed.

Lemma dynamicTruthSigmaConstructorEx8BranchFormula_fixed_lower_irrelevant :
    forall branch,
  branch <> DTSigmaAll -> forall lowerPi lowerPi',
  dynamicTruthSigmaConstructorEx8BranchFormula branch lowerPi =
  dynamicTruthSigmaConstructorEx8BranchFormula branch lowerPi'.
Proof.
  intros branch hfixed lowerPi lowerPi'.
  unfold dynamicTruthSigmaConstructorEx8BranchFormula.
  now rewrite (dynamicTruthSigmaConstructorBranchBody_fixed_lower_irrelevant
    branch hfixed lowerPi lowerPi').
Qed.

Lemma dynamicTruthPiConstructorEx8BranchFormula_fixed_lower_irrelevant :
    forall branch,
  branch <> DTPiEx -> forall lowerSigma lowerSigma',
  dynamicTruthPiConstructorEx8BranchFormula branch lowerSigma =
  dynamicTruthPiConstructorEx8BranchFormula branch lowerSigma'.
Proof.
  intros branch hfixed lowerSigma lowerSigma'.
  unfold dynamicTruthPiConstructorEx8BranchFormula.
  now rewrite (dynamicTruthPiConstructorBranchBody_fixed_lower_irrelevant
    branch hfixed lowerSigma lowerSigma').
Qed.

(** ------------------------------------------------------------------
    Literal branch satisfaction exposes the common outer root [e 2]. *)

Lemma raw_sat_dynamicTruthSigmaConstructorEx8Branch_principal : forall
    (M : RawPAModel) e branch lowerPi,
  raw_formula_sat M e
    (dynamicTruthSigmaConstructorEx8BranchFormula branch lowerPi) ->
  RawFormulaHasPrincipalConstructor M
    (dynamicTruthSigmaBranchPrincipal branch) (e 2).
Proof.
  intros M e branch lowerPi hbranch.
  destruct branch;
    unfold dynamicTruthSigmaConstructorEx8BranchFormula,
      dynamicTruthSigmaConstructorBranchBody,
      fixedLevelEx8 in hbranch;
    cbn [raw_formula_sat] in hbranch.
  - destruct hbranch as
      (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & hcode & _).
    apply (proj1 (raw_sat_formulaImpCodeTermAt_iff M _ _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode.
    exists a1, a3. exact hcode.
  - destruct hbranch as
      (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & hcode & _).
    apply (proj1 (raw_sat_formulaImpCodeTermAt_iff M _ _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode.
    exists a1, a3. exact hcode.
  - destruct hbranch as
      (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & hcode & _).
    apply (proj1 (raw_sat_formulaAndCodeTermAt_iff M _ _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode.
    exists a1, a3. exact hcode.
  - destruct hbranch as
      (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & hcode & _).
    apply (proj1 (raw_sat_formulaOrCodeTermAt_iff M _ _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode.
    exists a1, a3. exact hcode.
  - destruct hbranch as
      (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & hcode & _).
    apply (proj1 (raw_sat_formulaExCodeTermAt_iff M _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode.
    exists a1. exact hcode.
  - destruct hbranch as
      (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & hcode & _).
    apply (proj1 (raw_sat_formulaAllCodeTermAt_iff M _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode.
    exists a1. exact hcode.
Qed.

Lemma raw_sat_dynamicTruthPiConstructorEx8Branch_principal : forall
    (M : RawPAModel) e branch lowerSigma,
  raw_formula_sat M e
    (dynamicTruthPiConstructorEx8BranchFormula branch lowerSigma) ->
  RawFormulaHasPrincipalConstructor M
    (dynamicTruthPiBranchPrincipal branch) (e 2).
Proof.
  intros M e branch lowerSigma hbranch.
  destruct branch;
    unfold dynamicTruthPiConstructorEx8BranchFormula,
      dynamicTruthPiConstructorBranchBody,
      fixedLevelEx8 in hbranch;
    cbn [raw_formula_sat] in hbranch.
  - destruct hbranch as
      (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & hcode & _).
    apply (proj1 (raw_sat_formulaImpCodeTermAt_iff M _ _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode.
    exists a1, a3. exact hcode.
  - destruct hbranch as
      (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & hcode & _).
    apply (proj1 (raw_sat_formulaAndCodeTermAt_iff M _ _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode.
    exists a1, a3. exact hcode.
  - destruct hbranch as
      (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & hcode & _).
    apply (proj1 (raw_sat_formulaOrCodeTermAt_iff M _ _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode.
    exists a1, a3. exact hcode.
  - destruct hbranch as
      (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & hcode & _).
    apply (proj1 (raw_sat_formulaAllCodeTermAt_iff M _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode.
    exists a1. exact hcode.
  - destruct hbranch as
      (a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & hcode & _).
    apply (proj1 (raw_sat_formulaExCodeTermAt_iff M _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode.
    exists a1. exact hcode.
Qed.

(** ------------------------------------------------------------------
    One fixed PA theorem schema for all unequal constructor classes. *)

Definition dynamicTruthConstructorBranchDisjointnessFormula
    (sigmaBranch : DynamicTruthSigmaConstructorBranch)
    (lowerPi : formula)
    (piBranch : DynamicTruthPiConstructorBranch)
    (lowerSigma : formula) : formula :=
  pImp (dynamicTruthSigmaConstructorEx8BranchFormula sigmaBranch lowerPi)
    (pImp (dynamicTruthPiConstructorEx8BranchFormula piBranch lowerSigma)
      pBot).

(** Canonical representative of a fixed cell.  [pBot] is only a dummy
    lower formula; the invariance theorem immediately below proves that it
    disappears for every pair in the sixteen-cell enumeration. *)
Definition dynamicTruthFixedConstructorBranchDisjointnessFormula
    (sigmaBranch : DynamicTruthSigmaConstructorBranch)
    (piBranch : DynamicTruthPiConstructorBranch) : formula :=
  dynamicTruthConstructorBranchDisjointnessFormula
    sigmaBranch pBot piBranch pBot.

Lemma dynamicTruthConstructorBranchDisjointnessFormula_fixed_lower_irrelevant :
    forall sigmaBranch piBranch,
  DynamicTruthFixedConstructorCell sigmaBranch piBranch ->
  forall lowerPi lowerSigma,
  dynamicTruthConstructorBranchDisjointnessFormula
    sigmaBranch lowerPi piBranch lowerSigma =
  dynamicTruthFixedConstructorBranchDisjointnessFormula
    sigmaBranch piBranch.
Proof.
  intros sigmaBranch piBranch (hsigma & hpi & _)
    lowerPi lowerSigma.
  unfold dynamicTruthConstructorBranchDisjointnessFormula,
    dynamicTruthFixedConstructorBranchDisjointnessFormula.
  rewrite (dynamicTruthSigmaConstructorEx8BranchFormula_fixed_lower_irrelevant
    sigmaBranch hsigma lowerPi pBot).
  rewrite (dynamicTruthPiConstructorEx8BranchFormula_fixed_lower_irrelevant
    piBranch hpi lowerSigma pBot).
  reflexivity.
Qed.

Theorem dynamicTruthConstructorBranchDisjointnessFormula_raw_valid : forall
    sigmaBranch lowerPi piBranch lowerSigma,
  DynamicTruthConstructorBranchesDisjoint sigmaBranch piBranch ->
  forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (dynamicTruthConstructorBranchDisjointnessFormula
      sigmaBranch lowerPi piBranch lowerSigma).
Proof.
  intros sigmaBranch lowerPi piBranch lowerSigma hdifferent M hPA e.
  unfold dynamicTruthConstructorBranchDisjointnessFormula.
  cbn [raw_formula_sat]. intros hsigma hpi.
  exact (raw_formulaPrincipalConstructors_disjoint M hPA
    (dynamicTruthSigmaBranchPrincipal sigmaBranch)
    (dynamicTruthPiBranchPrincipal piBranch) (e 2) hdifferent
    (raw_sat_dynamicTruthSigmaConstructorEx8Branch_principal
      M e sigmaBranch lowerPi hsigma)
    (raw_sat_dynamicTruthPiConstructorEx8Branch_principal
      M e piBranch lowerSigma hpi)).
Qed.

(** Completeness is applied to the standard seal and the seal is then
    eliminated.  This compact wrapper is useful for every open fixed schema
    in this file. *)
Lemma PA_proves_constructorDisjoint_open_formula_of_raw_valid :
    forall target : formula,
  (forall (M : RawPAModel), RawPASatisfies M -> forall e,
    raw_formula_sat M e target) ->
  Formula.BProv Formula.Ax_s [] target.
Proof.
  intros target hvalid.
  assert (hclosed : Formula.BProv Formula.Ax_s [] (Formula.sealPA target)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA e.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner. exact (hvalid M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s [] target (fun n => n) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

Theorem PA_proves_dynamicTruthConstructorBranchDisjointnessFormula : forall
    sigmaBranch lowerPi piBranch lowerSigma,
  DynamicTruthConstructorBranchesDisjoint sigmaBranch piBranch ->
  Formula.BProv Formula.Ax_s []
    (dynamicTruthConstructorBranchDisjointnessFormula
      sigmaBranch lowerPi piBranch lowerSigma).
Proof.
  intros sigmaBranch lowerPi piBranch lowerSigma hdifferent.
  apply PA_proves_constructorDisjoint_open_formula_of_raw_valid.
  exact (dynamicTruthConstructorBranchDisjointnessFormula_raw_valid
    sigmaBranch lowerPi piBranch lowerSigma hdifferent).
Qed.

(** The matrix-ready portion of the result.  Membership both exposes the
    exact sixteen-cell classification and rules out the two branches whose
    syntax contains a metatheoretic lower formula. *)
Theorem PA_proves_dynamicTruthFixedConstructorCell : forall
    sigmaBranch piBranch,
  In (sigmaBranch, piBranch) dynamicTruthFixedConstructorCells ->
  forall lowerPi lowerSigma,
  Formula.BProv Formula.Ax_s []
    (dynamicTruthConstructorBranchDisjointnessFormula
      sigmaBranch lowerPi piBranch lowerSigma).
Proof.
  intros sigmaBranch piBranch hcell lowerPi lowerSigma.
  apply PA_proves_dynamicTruthConstructorBranchDisjointnessFormula.
  apply dynamicTruthFixedConstructorCells_spec in hcell.
  exact (proj2 (proj2 hcell)).
Qed.

Corollary PA_proves_dynamicTruthFixedConstructorBranchDisjointnessFormula :
    forall sigmaBranch piBranch,
  In (sigmaBranch, piBranch) dynamicTruthFixedConstructorCells ->
  Formula.BProv Formula.Ax_s []
    (dynamicTruthFixedConstructorBranchDisjointnessFormula
      sigmaBranch piBranch).
Proof.
  intros sigmaBranch piBranch hcell.
  exact (PA_proves_dynamicTruthFixedConstructorCell
    sigmaBranch piBranch hcell pBot pBot).
Qed.

(** Family-level instances make the excluded diagonal explicit for all
    standard-formula specializations.  The sixteen-element fixed list above,
    not this wider family, is the carrier-level matrix-ready interface. *)
Corollary PA_proves_dynamicTruthSigmaImpFalseLeft_disjoint_cell : forall
    lowerPi piBranch lowerSigma,
  piBranch <> DTPiImp ->
  Formula.BProv Formula.Ax_s []
    (dynamicTruthConstructorBranchDisjointnessFormula
      DTSigmaImpFalseLeft lowerPi piBranch lowerSigma).
Proof.
  intros lowerPi piBranch lowerSigma hbranch.
  apply PA_proves_dynamicTruthConstructorBranchDisjointnessFormula.
  destruct piBranch; cbn in *; try contradiction; discriminate.
Qed.

Corollary PA_proves_dynamicTruthSigmaImpTrueRight_disjoint_cell : forall
    lowerPi piBranch lowerSigma,
  piBranch <> DTPiImp ->
  Formula.BProv Formula.Ax_s []
    (dynamicTruthConstructorBranchDisjointnessFormula
      DTSigmaImpTrueRight lowerPi piBranch lowerSigma).
Proof.
  intros lowerPi piBranch lowerSigma hbranch.
  apply PA_proves_dynamicTruthConstructorBranchDisjointnessFormula.
  destruct piBranch; cbn in *; try contradiction; discriminate.
Qed.

Corollary PA_proves_dynamicTruthSigmaAnd_disjoint_cell : forall
    lowerPi piBranch lowerSigma,
  piBranch <> DTPiAnd ->
  Formula.BProv Formula.Ax_s []
    (dynamicTruthConstructorBranchDisjointnessFormula
      DTSigmaAnd lowerPi piBranch lowerSigma).
Proof.
  intros lowerPi piBranch lowerSigma hbranch.
  apply PA_proves_dynamicTruthConstructorBranchDisjointnessFormula.
  destruct piBranch; cbn in *; try contradiction; discriminate.
Qed.

Corollary PA_proves_dynamicTruthSigmaOr_disjoint_cell : forall
    lowerPi piBranch lowerSigma,
  piBranch <> DTPiOr ->
  Formula.BProv Formula.Ax_s []
    (dynamicTruthConstructorBranchDisjointnessFormula
      DTSigmaOr lowerPi piBranch lowerSigma).
Proof.
  intros lowerPi piBranch lowerSigma hbranch.
  apply PA_proves_dynamicTruthConstructorBranchDisjointnessFormula.
  destruct piBranch; cbn in *; try contradiction; discriminate.
Qed.

Corollary PA_proves_dynamicTruthSigmaEx_disjoint_cell : forall
    lowerPi piBranch lowerSigma,
  piBranch <> DTPiEx ->
  Formula.BProv Formula.Ax_s []
    (dynamicTruthConstructorBranchDisjointnessFormula
      DTSigmaEx lowerPi piBranch lowerSigma).
Proof.
  intros lowerPi piBranch lowerSigma hbranch.
  apply PA_proves_dynamicTruthConstructorBranchDisjointnessFormula.
  destruct piBranch; cbn in *; try contradiction; discriminate.
Qed.

Corollary PA_proves_dynamicTruthSigmaAll_disjoint_cell : forall
    lowerPi piBranch lowerSigma,
  piBranch <> DTPiAll ->
  Formula.BProv Formula.Ax_s []
    (dynamicTruthConstructorBranchDisjointnessFormula
      DTSigmaAll lowerPi piBranch lowerSigma).
Proof.
  intros lowerPi piBranch lowerSigma hbranch.
  apply PA_proves_dynamicTruthConstructorBranchDisjointnessFormula.
  destruct piBranch; cbn in *; try contradiction; discriminate.
Qed.

(** ------------------------------------------------------------------
    Exact carrier codes and represented ordinary proofs. *)

Definition rawDynamicTruthSigmaConstructorEx8BranchCode
    (M : RawPAModel) (branch : DynamicTruthSigmaConstructorBranch)
    (lowerPi : formula) : M :=
  rawFixedFormulaNumeralCode M
    (dynamicTruthSigmaConstructorEx8BranchFormula branch lowerPi).

Definition rawDynamicTruthPiConstructorEx8BranchCode
    (M : RawPAModel) (branch : DynamicTruthPiConstructorBranch)
    (lowerSigma : formula) : M :=
  rawFixedFormulaNumeralCode M
    (dynamicTruthPiConstructorEx8BranchFormula branch lowerSigma).

Definition rawDynamicTruthConstructorBranchDisjointnessCode
    (M : RawPAModel)
    (sigmaBranch : DynamicTruthSigmaConstructorBranch)
    (lowerPi : formula)
    (piBranch : DynamicTruthPiConstructorBranch)
    (lowerSigma : formula) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthSigmaConstructorEx8BranchCode M sigmaBranch lowerPi)
    (rawFormulaImpCode M
      (rawDynamicTruthPiConstructorEx8BranchCode M piBranch lowerSigma)
      (rawFormulaBotCode M)).

Definition rawDynamicTruthFixedConstructorBranchDisjointnessCode
    (M : RawPAModel)
    (sigmaBranch : DynamicTruthSigmaConstructorBranch)
    (piBranch : DynamicTruthPiConstructorBranch) : M :=
  rawDynamicTruthConstructorBranchDisjointnessCode M
    sigmaBranch pBot piBranch pBot.

Lemma rawDynamicTruthSigmaConstructorEx8BranchCode_fixed_lower_irrelevant :
    forall (M : RawPAModel) branch,
  branch <> DTSigmaAll -> forall lowerPi lowerPi',
  rawDynamicTruthSigmaConstructorEx8BranchCode M branch lowerPi =
  rawDynamicTruthSigmaConstructorEx8BranchCode M branch lowerPi'.
Proof.
  intros M branch hfixed lowerPi lowerPi'.
  unfold rawDynamicTruthSigmaConstructorEx8BranchCode.
  now rewrite (dynamicTruthSigmaConstructorEx8BranchFormula_fixed_lower_irrelevant
    branch hfixed lowerPi lowerPi').
Qed.

Lemma rawDynamicTruthPiConstructorEx8BranchCode_fixed_lower_irrelevant :
    forall (M : RawPAModel) branch,
  branch <> DTPiEx -> forall lowerSigma lowerSigma',
  rawDynamicTruthPiConstructorEx8BranchCode M branch lowerSigma =
  rawDynamicTruthPiConstructorEx8BranchCode M branch lowerSigma'.
Proof.
  intros M branch hfixed lowerSigma lowerSigma'.
  unfold rawDynamicTruthPiConstructorEx8BranchCode.
  now rewrite (dynamicTruthPiConstructorEx8BranchFormula_fixed_lower_irrelevant
    branch hfixed lowerSigma lowerSigma').
Qed.

Lemma rawDynamicTruthConstructorBranchDisjointnessCode_fixed_lower_irrelevant :
    forall (M : RawPAModel) sigmaBranch piBranch,
  DynamicTruthFixedConstructorCell sigmaBranch piBranch ->
  forall lowerPi lowerSigma,
  rawDynamicTruthConstructorBranchDisjointnessCode M
    sigmaBranch lowerPi piBranch lowerSigma =
  rawDynamicTruthFixedConstructorBranchDisjointnessCode M
    sigmaBranch piBranch.
Proof.
  intros M sigmaBranch piBranch (hsigma & hpi & _)
    lowerPi lowerSigma.
  unfold rawDynamicTruthConstructorBranchDisjointnessCode,
    rawDynamicTruthFixedConstructorBranchDisjointnessCode.
  rewrite (rawDynamicTruthSigmaConstructorEx8BranchCode_fixed_lower_irrelevant
    M sigmaBranch hsigma lowerPi pBot).
  rewrite (rawDynamicTruthPiConstructorEx8BranchCode_fixed_lower_irrelevant
    M piBranch hpi lowerSigma pBot).
  reflexivity.
Qed.

Lemma rawDynamicTruthSigmaConstructorEx8BranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall branch lowerPi,
  rawDynamicTruthSigmaConstructorEx8BranchCode M branch lowerPi =
  rawQuotedFormulaCode M
    (dynamicTruthSigmaConstructorEx8BranchFormula branch lowerPi).
Proof.
  intros M hPA branch lowerPi.
  unfold rawDynamicTruthSigmaConstructorEx8BranchCode.
  apply rawFixedFormulaNumeralCode_eq_quoted. exact hPA.
Qed.

Lemma rawDynamicTruthPiConstructorEx8BranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall branch lowerSigma,
  rawDynamicTruthPiConstructorEx8BranchCode M branch lowerSigma =
  rawQuotedFormulaCode M
    (dynamicTruthPiConstructorEx8BranchFormula branch lowerSigma).
Proof.
  intros M hPA branch lowerSigma.
  unfold rawDynamicTruthPiConstructorEx8BranchCode.
  apply rawFixedFormulaNumeralCode_eq_quoted. exact hPA.
Qed.

Lemma rawDynamicTruthConstructorBranchDisjointnessCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sigmaBranch lowerPi piBranch lowerSigma,
  rawDynamicTruthConstructorBranchDisjointnessCode M
    sigmaBranch lowerPi piBranch lowerSigma =
  rawQuotedFormulaCode M
    (dynamicTruthConstructorBranchDisjointnessFormula
      sigmaBranch lowerPi piBranch lowerSigma).
Proof.
  intros M hPA sigmaBranch lowerPi piBranch lowerSigma.
  unfold rawDynamicTruthConstructorBranchDisjointnessCode,
    dynamicTruthConstructorBranchDisjointnessFormula.
  rewrite rawDynamicTruthSigmaConstructorEx8BranchCode_eq_quoted
    by exact hPA.
  rewrite rawDynamicTruthPiConstructorEx8BranchCode_eq_quoted
    by exact hPA.
  reflexivity.
Qed.

Lemma rawDynamicTruthConstructorBranchDisjointnessCode_eq_numeral : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sigmaBranch lowerPi piBranch lowerSigma,
  rawDynamicTruthConstructorBranchDisjointnessCode M
    sigmaBranch lowerPi piBranch lowerSigma =
  rawNumeralValue M
    (formulaCode (dynamicTruthConstructorBranchDisjointnessFormula
      sigmaBranch lowerPi piBranch lowerSigma)).
Proof.
  intros M hPA sigmaBranch lowerPi piBranch lowerSigma.
  rewrite rawDynamicTruthConstructorBranchDisjointnessCode_eq_quoted
    by exact hPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Theorem raw_codedPAProofOf_dynamicTruthConstructorBranchDisjointness : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sigmaBranch lowerPi piBranch lowerSigma,
  DynamicTruthConstructorBranchesDisjoint sigmaBranch piBranch ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthConstructorBranchDisjointnessCode M
        sigmaBranch lowerPi piBranch lowerSigma) certificate.
Proof.
  intros M hPA sigmaBranch lowerPi piBranch lowerSigma hdifferent.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    (dynamicTruthConstructorBranchDisjointnessFormula
      sigmaBranch lowerPi piBranch lowerSigma)
    (PA_proves_dynamicTruthConstructorBranchDisjointnessFormula
      sigmaBranch lowerPi piBranch lowerSigma hdifferent))
    as [certificate hcertificate].
  exists certificate.
  rewrite rawDynamicTruthConstructorBranchDisjointnessCode_eq_numeral
    by exact hPA.
  exact hcertificate.
Qed.

Corollary raw_codedPAProofOf_dynamicTruthFixedConstructorCell : forall
    (M : RawPAModel), RawPASatisfies M -> forall sigmaBranch piBranch,
  In (sigmaBranch, piBranch) dynamicTruthFixedConstructorCells ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthFixedConstructorBranchDisjointnessCode M
        sigmaBranch piBranch) certificate.
Proof.
  intros M hPA sigmaBranch piBranch hcell.
  apply dynamicTruthFixedConstructorCells_spec in hcell.
  destruct hcell as (_ & _ & hdifferent).
  exact (raw_codedPAProofOf_dynamicTruthConstructorBranchDisjointness
    M hPA sigmaBranch pBot piBranch pBot hdifferent).
Qed.

(** ------------------------------------------------------------------
    Common-context local collision and guarded branch insertion. *)

Definition rawDynamicTruthConstructorBranchCollisionRoot
    (M : RawPAModel)
    (context sigmaBranch piBranch implicationRoot sigmaRoot piRoot : M)
    : M :=
  rawProofImpERoot M context piBranch (rawFormulaBotCode M)
    (rawProofImpERoot M context sigmaBranch
      (rawFormulaImpCode M piBranch (rawFormulaBotCode M))
      implicationRoot sigmaRoot)
    piRoot.

Arguments rawDynamicTruthConstructorBranchCollisionRoot
  M context sigmaBranch piBranch implicationRoot sigmaRoot piRoot
    : clear implicits.

Theorem raw_codedPALocalProofOf_dynamicTruthConstructorBranchCollision :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context sigmaBranch piBranch implicationRoot sigmaRoot piRoot,
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M sigmaBranch
      (rawFormulaImpCode M piBranch (rawFormulaBotCode M)))
    implicationRoot ->
  RawCodedPALocalProofOf M context sigmaBranch sigmaRoot ->
  RawCodedPALocalProofOf M context piBranch piRoot ->
  RawCodedPALocalProofOf M context (rawFormulaBotCode M)
    (rawDynamicTruthConstructorBranchCollisionRoot M context
      sigmaBranch piBranch implicationRoot sigmaRoot piRoot).
Proof.
  intros M hPA context sigmaBranch piBranch implicationRoot
    sigmaRoot piRoot himp hsigma hpi.
  unfold rawDynamicTruthConstructorBranchCollisionRoot.
  apply (raw_codedPALocalProofOf_impE M hPA context
    piBranch (rawFormulaBotCode M)); [|exact hpi].
  exact (raw_codedPALocalProofOf_impE M hPA context sigmaBranch
    (rawFormulaImpCode M piBranch (rawFormulaBotCode M))
    implicationRoot sigmaRoot himp hsigma).
Qed.

Definition rawDynamicTruthConstructorCellCollisionRoot
    (M : RawPAModel) (context : M)
    (sigmaBranch : DynamicTruthSigmaConstructorBranch)
    (lowerPi : formula)
    (piBranch : DynamicTruthPiConstructorBranch)
    (lowerSigma : formula)
    (implicationRoot sigmaRoot piRoot : M) : M :=
  rawDynamicTruthConstructorBranchCollisionRoot M context
    (rawDynamicTruthSigmaConstructorEx8BranchCode M sigmaBranch lowerPi)
    (rawDynamicTruthPiConstructorEx8BranchCode M piBranch lowerSigma)
    implicationRoot sigmaRoot piRoot.

Arguments rawDynamicTruthConstructorCellCollisionRoot
  M context sigmaBranch lowerPi piBranch lowerSigma
    implicationRoot sigmaRoot piRoot : clear implicits.

Corollary raw_codedPALocalProofOf_dynamicTruthConstructorCellCollision :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context sigmaBranch lowerPi piBranch lowerSigma
      implicationRoot sigmaRoot piRoot,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthConstructorBranchDisjointnessCode M
      sigmaBranch lowerPi piBranch lowerSigma) implicationRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthSigmaConstructorEx8BranchCode M sigmaBranch lowerPi)
    sigmaRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthPiConstructorEx8BranchCode M piBranch lowerSigma)
    piRoot ->
  RawCodedPALocalProofOf M context (rawFormulaBotCode M)
    (rawDynamicTruthConstructorCellCollisionRoot M context
      sigmaBranch lowerPi piBranch lowerSigma
      implicationRoot sigmaRoot piRoot).
Proof.
  intros M hPA context sigmaBranch lowerPi piBranch lowerSigma
    implicationRoot sigmaRoot piRoot himp hsigma hpi.
  unfold rawDynamicTruthConstructorCellCollisionRoot,
    rawDynamicTruthConstructorBranchDisjointnessCode.
  exact (raw_codedPALocalProofOf_dynamicTruthConstructorBranchCollision
    M hPA context
    (rawDynamicTruthSigmaConstructorEx8BranchCode M sigmaBranch lowerPi)
    (rawDynamicTruthPiConstructorEx8BranchCode M piBranch lowerSigma)
    implicationRoot sigmaRoot piRoot himp hsigma hpi).
Qed.

(** The guarded theorem builds the literal nested assumption context used by
    finite row-disjunction elimination.  Atomic adequacy follows because the
    two branch codes are standard formula numerals.  For Sigma-All or Pi-Ex
    this remains a standard-lower-formula endpoint, rather than an endpoint
    over an arbitrary carrier lower-application code. *)
Theorem raw_dynamicTruthConstructorCellCollision_under_assumptions : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sigmaBranch lowerPi piBranch lowerSigma context implicationRoot,
  RawContextListRealizable M context ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthConstructorBranchDisjointnessCode M
      sigmaBranch lowerPi piBranch lowerSigma) implicationRoot ->
  exists collisionRoot : M,
    RawCodedPALocalProofOf M
      (rawListNode M
        (rawDynamicTruthPiConstructorEx8BranchCode M piBranch lowerSigma)
        (rawListNode M
          (rawDynamicTruthSigmaConstructorEx8BranchCode M
            sigmaBranch lowerPi)
          context))
      (rawFormulaBotCode M) collisionRoot.
Proof.
  intros M hPA sigmaBranch lowerPi piBranch lowerSigma
    context implicationRoot hcontext himp.
  set (sigmaCode := rawDynamicTruthSigmaConstructorEx8BranchCode M
    sigmaBranch lowerPi).
  set (piCode := rawDynamicTruthPiConstructorEx8BranchCode M
    piBranch lowerSigma).
  assert (hsigmaAdequate : RawCodedFormulaAtomicallyAdequate M sigmaCode).
  {
    unfold sigmaCode.
    rewrite rawDynamicTruthSigmaConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite (rawQuotedFormulaCode_standard M hPA).
    exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      (dynamicTruthSigmaConstructorEx8BranchFormula
        sigmaBranch lowerPi)).
  }
  assert (hpiAdequate : RawCodedFormulaAtomicallyAdequate M piCode).
  {
    unfold piCode.
    rewrite rawDynamicTruthPiConstructorEx8BranchCode_eq_quoted
      by exact hPA.
    rewrite (rawQuotedFormulaCode_standard M hPA).
    exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      (dynamicTruthPiConstructorEx8BranchFormula
        piBranch lowerSigma)).
  }
  set (sigmaContext := rawListNode M sigmaCode context).
  assert (hsigmaContext : RawContextListRealizable M sigmaContext).
  {
    unfold sigmaContext.
    exact (raw_contextList_cons_realizable M hPA
      context sigmaCode hcontext).
  }
  unfold rawDynamicTruthConstructorBranchDisjointnessCode in himp.
  fold sigmaCode piCode in himp.
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    context sigmaCode
    (rawFormulaImpCode M sigmaCode
      (rawFormulaImpCode M piCode (rawFormulaBotCode M)))
    implicationRoot hsigmaAdequate hcontext himp)
    as [implicationSigma himpSigma].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    context sigmaCode hcontext) as hsigmaHead.
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    sigmaContext piCode
    (rawFormulaImpCode M sigmaCode
      (rawFormulaImpCode M piCode (rawFormulaBotCode M)))
    implicationSigma hpiAdequate hsigmaContext himpSigma)
    as [implicationBoth himpBoth].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    sigmaContext piCode sigmaCode
    (rawProofAssumptionRoot M sigmaContext sigmaCode)
    hpiAdequate hsigmaContext hsigmaHead)
    as [sigmaBoth hsigmaBoth].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    sigmaContext piCode hsigmaContext) as hpiHead.
  exists (rawDynamicTruthConstructorBranchCollisionRoot M
    (rawListNode M piCode sigmaContext) sigmaCode piCode
    implicationBoth sigmaBoth
    (rawProofAssumptionRoot M
      (rawListNode M piCode sigmaContext) piCode)).
  exact (raw_codedPALocalProofOf_dynamicTruthConstructorBranchCollision
    M hPA (rawListNode M piCode sigmaContext) sigmaCode piCode
    implicationBoth sigmaBoth
    (rawProofAssumptionRoot M
      (rawListNode M piCode sigmaContext) piCode)
    himpBoth hsigmaBoth hpiHead).
Qed.

(** The ordinary represented proof exposes an honest PA-witnessed common
    base.  This endpoint is useful independently of any particular matrix
    enumeration. *)
Theorem raw_dynamicTruthConstructorBranchDisjointness_local_base : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sigmaBranch lowerPi piBranch lowerSigma,
  DynamicTruthConstructorBranchesDisjoint sigmaBranch piBranch ->
  exists witnessList baseContext implicationRoot : M,
    RawCodedPAAxiomWitnessContext M witnessList baseContext /\
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthConstructorBranchDisjointnessCode M
        sigmaBranch lowerPi piBranch lowerSigma) implicationRoot.
Proof.
  intros M hPA sigmaBranch lowerPi piBranch lowerSigma hdifferent.
  destruct (raw_codedPAProofOf_dynamicTruthConstructorBranchDisjointness
    M hPA sigmaBranch lowerPi piBranch lowerSigma hdifferent)
    as [certificate hcertificate].
  destruct hcertificate as
    (witnessList & implicationRoot & baseContext &
      _ & hwitness & hcoverage & hendpoint).
  exists witnessList, baseContext, implicationRoot.
  split; [exact hwitness |]. split; assumption.
Qed.

Theorem raw_dynamicTruthConstructorCellCollision_in_witnessed_base : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sigmaBranch lowerPi piBranch lowerSigma,
  DynamicTruthConstructorBranchesDisjoint sigmaBranch piBranch ->
  exists witnessList baseContext collisionRoot : M,
    RawCodedPAAxiomWitnessContext M witnessList baseContext /\
    RawCodedPALocalProofOf M
      (rawListNode M
        (rawDynamicTruthPiConstructorEx8BranchCode M piBranch lowerSigma)
        (rawListNode M
          (rawDynamicTruthSigmaConstructorEx8BranchCode M
            sigmaBranch lowerPi)
          baseContext))
      (rawFormulaBotCode M) collisionRoot.
Proof.
  intros M hPA sigmaBranch lowerPi piBranch lowerSigma hdifferent.
  destruct (raw_dynamicTruthConstructorBranchDisjointness_local_base
    M hPA sigmaBranch lowerPi piBranch lowerSigma hdifferent)
    as (witnessList & baseContext & implicationRoot &
      hwitness & himplication).
  assert (hcontext : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitness).
  }
  destruct (raw_dynamicTruthConstructorCellCollision_under_assumptions
    M hPA sigmaBranch lowerPi piBranch lowerSigma
    baseContext implicationRoot hcontext himplication)
    as [collisionRoot hcollision].
  exists witnessList, baseContext, collisionRoot.
  split; assumption.
Qed.

End PABoundedRawCodedDynamicTruthConstructorBranchDisjointness.
