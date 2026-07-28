(**
  The eleven mixed quantifier-free cells of the native dynamic-truth matrix.

  The Sigma row has seven alternatives and the Pi row has six.  After the
  aligned QF/QF cell and the thirty constructor/constructor cells are
  removed, exactly eleven cells have a QF branch on one side:

      Sigma-QF against the five non-QF Pi branches, and
      the six non-QF Sigma branches against Pi-QF.

  Four of these cells touch a quantifier.  They are unconditional: the
  closed rank-zero traversal has no universal or existential production
  rule.  The remaining seven cells are Boolean replay cells.  A rank-zero
  truth table exposes a child bit, while the opposite structural branch
  exposes a synchronized predecessor-state member.  We therefore state the
  exact two-direction replay invariant needed by those seven cells.  This is
  deliberately narrower than assuming the whole predecessor state is sound
  or the whole successor matrix is exclusive.

  Every formula below is the literal native eight-witness branch formula.
  The carrier code interface at the end retains opaque lower applications
  for Sigma-All and Pi-Ex, and proves quotation alignment whenever those
  carrier inputs are standard quoted formulae.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedRankZeroTruthTraversal
  RawCodedRankZeroTruthElimination
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthLaws
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthQFBranchExclusivity
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthBooleanBranchExclusivity
  RawCodedDynamicTruthQuantifierBranchExclusivity
  RawCodedDynamicTruthBinderOffDiagonalExclusivity
  RawCodedPAProvability
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthMixedQFBranchExclusivity.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedRankZeroTruthElimination.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthLaws.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBooleanBranchExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBinderOffDiagonalExclusivity.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.

(** ------------------------------------------------------------------
    Exact finite classification: 3 + 4 replay cells and 2 + 2 terminal
    quantifier cells. *)

Inductive DynamicTruthMixedQFCell : Type :=
| DTMQFSigmaQFPiImp
| DTMQFSigmaQFPiAnd
| DTMQFSigmaQFPiOr
| DTMQFSigmaQFPiAll
| DTMQFSigmaQFPiEx
| DTMQFSigmaImpFalseLeftPiQF
| DTMQFSigmaImpTrueRightPiQF
| DTMQFSigmaAndPiQF
| DTMQFSigmaOrPiQF
| DTMQFSigmaExPiQF
| DTMQFSigmaAllPiQF.

Definition dynamicTruthMixedQFCells : list DynamicTruthMixedQFCell :=
  [ DTMQFSigmaQFPiImp;
    DTMQFSigmaQFPiAnd;
    DTMQFSigmaQFPiOr;
    DTMQFSigmaQFPiAll;
    DTMQFSigmaQFPiEx;
    DTMQFSigmaImpFalseLeftPiQF;
    DTMQFSigmaImpTrueRightPiQF;
    DTMQFSigmaAndPiQF;
    DTMQFSigmaOrPiQF;
    DTMQFSigmaExPiQF;
    DTMQFSigmaAllPiQF ].

Definition dynamicTruthMixedQFReplayCells : list DynamicTruthMixedQFCell :=
  [ DTMQFSigmaQFPiImp;
    DTMQFSigmaQFPiAnd;
    DTMQFSigmaQFPiOr;
    DTMQFSigmaImpFalseLeftPiQF;
    DTMQFSigmaImpTrueRightPiQF;
    DTMQFSigmaAndPiQF;
    DTMQFSigmaOrPiQF ].

Definition dynamicTruthMixedQFQuantifierCells :
    list DynamicTruthMixedQFCell :=
  [ DTMQFSigmaQFPiAll;
    DTMQFSigmaQFPiEx;
    DTMQFSigmaExPiQF;
    DTMQFSigmaAllPiQF ].

(** Code dependence cuts across the logical split above.  Nine cells ignore
    both lower-application carrier arguments.  The Pi-Ex and Sigma-All cells
    are the only two whose literal native branch code retains one such
    argument. *)
Definition dynamicTruthMixedQFFixedCodeCells :
    list DynamicTruthMixedQFCell :=
  [ DTMQFSigmaQFPiImp;
    DTMQFSigmaQFPiAnd;
    DTMQFSigmaQFPiOr;
    DTMQFSigmaQFPiAll;
    DTMQFSigmaImpFalseLeftPiQF;
    DTMQFSigmaImpTrueRightPiQF;
    DTMQFSigmaAndPiQF;
    DTMQFSigmaOrPiQF;
    DTMQFSigmaExPiQF ].

Definition dynamicTruthMixedQFOpaqueCodeCells :
    list DynamicTruthMixedQFCell :=
  [ DTMQFSigmaQFPiEx; DTMQFSigmaAllPiQF ].

Lemma dynamicTruthMixedQFCells_length :
  length dynamicTruthMixedQFCells = 11.
Proof. reflexivity. Qed.

Lemma dynamicTruthMixedQFReplayCells_length :
  length dynamicTruthMixedQFReplayCells = 7.
Proof. reflexivity. Qed.

Lemma dynamicTruthMixedQFQuantifierCells_length :
  length dynamicTruthMixedQFQuantifierCells = 4.
Proof. reflexivity. Qed.

Lemma dynamicTruthMixedQFFixedCodeCells_length :
  length dynamicTruthMixedQFFixedCodeCells = 9.
Proof. reflexivity. Qed.

Lemma dynamicTruthMixedQFOpaqueCodeCells_length :
  length dynamicTruthMixedQFOpaqueCodeCells = 2.
Proof. reflexivity. Qed.

Lemma dynamicTruthMixedQFCells_complete : forall cell,
  In cell dynamicTruthMixedQFCells.
Proof. intros []; cbn; intuition. Qed.

Lemma dynamicTruthMixedQFCells_partition : forall cell,
  In cell dynamicTruthMixedQFReplayCells \/
  In cell dynamicTruthMixedQFQuantifierCells.
Proof. intros []; cbn; intuition. Qed.

Lemma dynamicTruthMixedQFCodeCells_partition : forall cell,
  In cell dynamicTruthMixedQFFixedCodeCells \/
  In cell dynamicTruthMixedQFOpaqueCodeCells.
Proof. intros []; cbn; intuition. Qed.

Lemma dynamicTruthMixedQFLogicalPartitions_disjoint : forall cell,
  In cell dynamicTruthMixedQFReplayCells ->
  ~ In cell dynamicTruthMixedQFQuantifierCells.
Proof. intros []; cbn; intuition congruence. Qed.

Lemma dynamicTruthMixedQFLogicalPartitions_disjoint_rev : forall cell,
  In cell dynamicTruthMixedQFQuantifierCells ->
  ~ In cell dynamicTruthMixedQFReplayCells.
Proof.
  intros cell hQuantifier hReplay.
  exact (dynamicTruthMixedQFLogicalPartitions_disjoint
    cell hReplay hQuantifier).
Qed.

Lemma dynamicTruthMixedQFCodePartitions_disjoint : forall cell,
  In cell dynamicTruthMixedQFFixedCodeCells ->
  ~ In cell dynamicTruthMixedQFOpaqueCodeCells.
Proof. intros []; cbn; intuition congruence. Qed.

(** ------------------------------------------------------------------
    Literal formula branches.  Only Sigma-All and Pi-Ex depend on a lower
    application; all other arguments are retained merely so these maps have
    one uniform type. *)

Definition dynamicTruthMixedQFSigmaBranchFormula
    (cell : DynamicTruthMixedQFCell) (lowerPiApplication : formula)
    : formula :=
  match cell with
  | DTMQFSigmaQFPiImp
  | DTMQFSigmaQFPiAnd
  | DTMQFSigmaQFPiOr
  | DTMQFSigmaQFPiAll
  | DTMQFSigmaQFPiEx => dynamicTruthSigmaQFEx8BranchFormula
  | DTMQFSigmaImpFalseLeftPiQF =>
      dynamicTruthSigmaImpFalseLeftEx8BranchFormula
  | DTMQFSigmaImpTrueRightPiQF =>
      dynamicTruthSigmaImpTrueRightEx8BranchFormula
  | DTMQFSigmaAndPiQF => dynamicTruthSigmaAndEx8BranchFormula
  | DTMQFSigmaOrPiQF => dynamicTruthSigmaOrEx8BranchFormula
  | DTMQFSigmaExPiQF => dynamicTruthSigmaEx8BranchFormula
  | DTMQFSigmaAllPiQF =>
      dynamicTruthSigmaUniversalEx8BranchFormula lowerPiApplication
  end.

Definition dynamicTruthMixedQFPiBranchFormula
    (cell : DynamicTruthMixedQFCell) (lowerSigmaApplication : formula)
    : formula :=
  match cell with
  | DTMQFSigmaQFPiImp => dynamicTruthPiImpEx8BranchFormula
  | DTMQFSigmaQFPiAnd => dynamicTruthPiAndEx8BranchFormula
  | DTMQFSigmaQFPiOr => dynamicTruthPiOrEx8BranchFormula
  | DTMQFSigmaQFPiAll => dynamicTruthPiAllEx8BranchFormula
  | DTMQFSigmaQFPiEx =>
      dynamicTruthPiExistentialEx8BranchFormula lowerSigmaApplication
  | DTMQFSigmaImpFalseLeftPiQF
  | DTMQFSigmaImpTrueRightPiQF
  | DTMQFSigmaAndPiQF
  | DTMQFSigmaOrPiQF
  | DTMQFSigmaExPiQF
  | DTMQFSigmaAllPiQF => dynamicTruthPiQFEx8BranchFormula
  end.

(** ------------------------------------------------------------------
    The exact rank-zero/state replay premise.

    Native state bits use [0] for a Sigma truth member and [1] for a Pi
    falsity member, whereas rank-zero outputs use [1] for truth and [0] for
    falsity.  Hence the two genuinely contradictory pairs are

      rank-zero 1 / state 1, and state 0 / rank-zero 0.

    Two universal binders range over the state index and child code.  The
    surrounding row carrier remains at the same outer positions used by the
    predecessor-state exclusivity formula.
*)

Definition dynamicTruthMixedQFTruthToPiReplayFormula : formula :=
  pAll (pAll
    (pImp
      (rankZeroTruthCertificateTermAt
        (tVar 0) (Term.numeral 1) (tVar 3) (tVar 2))
      (pImp
        (dynamicTruthStateMemberTermAt
          (tVar 14) (tVar 13) (tVar 12) (tVar 11)
          (tVar 10) (tVar 9) (tVar 8) (tVar 7)
          (tVar 6) (tVar 1) (Term.numeral 1) (tVar 0)
          (tVar 3) (tVar 2))
        pBot))).

Definition dynamicTruthMixedQFSigmaToFalsityReplayFormula : formula :=
  pAll (pAll
    (pImp
      (dynamicTruthStateMemberTermAt
        (tVar 14) (tVar 13) (tVar 12) (tVar 11)
        (tVar 10) (tVar 9) (tVar 8) (tVar 7)
        (tVar 6) (tVar 1) tZero (tVar 0)
        (tVar 3) (tVar 2))
      (pImp
        (rankZeroTruthCertificateTermAt
          (tVar 0) tZero (tVar 3) (tVar 2))
        pBot))).

Definition dynamicTruthMixedQFReplayExclusivityFormula : formula :=
  pAnd dynamicTruthMixedQFTruthToPiReplayFormula
    dynamicTruthMixedQFSigmaToFalsityReplayFormula.

Definition RawDynamicTruthMixedQFReplayExclusiveAt
    (M : RawPAModel)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      current assignmentCode assignmentStep : M) : Prop :=
  (forall index child : M,
    RawRankZeroTruthCertificate M child (rawNumeralValue M 1)
      assignmentCode assignmentStep ->
    RawDynamicTruthStateMember M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      current index (rawNumeralValue M 1) child
      assignmentCode assignmentStep -> False) /\
  (forall index child : M,
    RawDynamicTruthStateMember M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      current index (raw_zero M) child
      assignmentCode assignmentStep ->
    RawRankZeroTruthCertificate M child (raw_zero M)
      assignmentCode assignmentStep -> False).

Arguments RawDynamicTruthMixedQFReplayExclusiveAt
  M modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    current assignmentCode assignmentStep : clear implicits.

Lemma raw_sat_dynamicTruthMixedQFReplayExclusivityFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e dynamicTruthMixedQFReplayExclusivityFormula <->
  RawDynamicTruthMixedQFReplayExclusiveAt M
    (e 12) (e 11) (e 10) (e 9)
    (e 8) (e 7) (e 6) (e 5)
    (e 4) (e 1) (e 0).
Proof.
  intros M e.
  unfold dynamicTruthMixedQFReplayExclusivityFormula,
    dynamicTruthMixedQFTruthToPiReplayFormula,
    dynamicTruthMixedQFSigmaToFalsityReplayFormula,
    RawDynamicTruthMixedQFReplayExclusiveAt.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_rankZeroTruthCertificateTermAt_iff.
  repeat setoid_rewrite raw_sat_dynamicTruthStateMemberTermAt_iff.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

(** Replay cells carry the exact premise above; quantified cells need no
    premise because rank-zero syntax already rejects their parent code. *)
Definition dynamicTruthMixedQFCellFormula
    (cell : DynamicTruthMixedQFCell)
    (lowerPiApplication lowerSigmaApplication : formula) : formula :=
  let collision :=
    pImp (dynamicTruthMixedQFSigmaBranchFormula cell lowerPiApplication)
      (pImp
        (dynamicTruthMixedQFPiBranchFormula cell lowerSigmaApplication)
        pBot) in
  match cell with
  | DTMQFSigmaQFPiImp
  | DTMQFSigmaQFPiAnd
  | DTMQFSigmaQFPiOr
  | DTMQFSigmaImpFalseLeftPiQF
  | DTMQFSigmaImpTrueRightPiQF
  | DTMQFSigmaAndPiQF
  | DTMQFSigmaOrPiQF =>
      pImp dynamicTruthMixedQFReplayExclusivityFormula collision
  | DTMQFSigmaQFPiAll
  | DTMQFSigmaQFPiEx
  | DTMQFSigmaExPiQF
  | DTMQFSigmaAllPiQF => collision
  end.

(** ------------------------------------------------------------------
    Semantic proof of all eleven cells.  The seven Boolean cases expose a
    rank-zero child table and call exactly one half of the replay premise.
    The four quantifier cases stop immediately at the rank-zero grammar. *)

Theorem dynamicTruthMixedQFCellFormula_raw_valid : forall
    cell lowerPiApplication lowerSigmaApplication
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (dynamicTruthMixedQFCellFormula cell
      lowerPiApplication lowerSigmaApplication).
Proof.
  intros cell lowerPiApplication lowerSigmaApplication M hPA e.
  destruct cell; cbn [dynamicTruthMixedQFCellFormula
    dynamicTruthMixedQFSigmaBranchFormula
    dynamicTruthMixedQFPiBranchFormula raw_formula_sat].
  - rewrite raw_sat_dynamicTruthMixedQFReplayExclusivityFormula_iff.
    rewrite raw_sat_dynamicTruthSigmaQFEx8BranchFormula_iff.
    rewrite raw_sat_dynamicTruthPiImpEx8BranchFormula_iff.
    intros [htruthPi hsigmaFalse] hsigma hpi.
    destruct hsigma as
      (s0 & s1 & s2 & s3 & s4 & s5 & s6 & s7 & hparent).
    destruct hpi as
      (leftIndex & left & rightIndex & right & p4 & p5 & p6 & p7 &
       hcode & hleft & hright & _).
    rewrite hcode in hparent.
    destruct (raw_rankZeroTruthCertificate_imp_view M hPA
      (rawFormulaImpCode M left right) (rawNumeralValue M 1)
      (e 1) (e 0) left right eq_refl hparent) as
      (leftOutput & rightOutput & hleftZero & hrightZero & htable).
    destruct (raw_impTruth_one_elim M hPA leftOutput rightOutput htable)
      as [hleftOutput | hrightOutput].
    + subst leftOutput. exact (hsigmaFalse leftIndex left hleft hleftZero).
    + subst rightOutput. exact (htruthPi rightIndex right hrightZero hright).
  - rewrite raw_sat_dynamicTruthMixedQFReplayExclusivityFormula_iff.
    rewrite raw_sat_dynamicTruthSigmaQFEx8BranchFormula_iff.
    rewrite raw_sat_dynamicTruthPiAndEx8BranchFormula_iff.
    intros [htruthPi _] hsigma hpi.
    destruct hsigma as
      (s0 & s1 & s2 & s3 & s4 & s5 & s6 & s7 & hparent).
    destruct hpi as
      (leftIndex & left & rightIndex & right & p4 & p5 & p6 & p7 &
       hcode & [hleft | hright]).
    all: rewrite hcode in hparent.
    all: destruct (raw_rankZeroTruthCertificate_and_view M hPA
      (rawFormulaAndCode M left right) (rawNumeralValue M 1)
      (e 1) (e 0) left right eq_refl hparent) as
      (leftOutput & rightOutput & hleftZero & hrightZero & htable).
    all: destruct (raw_andTruth_one_elim M hPA
      leftOutput rightOutput htable) as [hleftOutput hrightOutput].
    + subst leftOutput. exact (htruthPi leftIndex left hleftZero hleft).
    + subst rightOutput. exact (htruthPi rightIndex right hrightZero hright).
  - rewrite raw_sat_dynamicTruthMixedQFReplayExclusivityFormula_iff.
    rewrite raw_sat_dynamicTruthSigmaQFEx8BranchFormula_iff.
    rewrite raw_sat_dynamicTruthPiOrEx8BranchFormula_iff.
    intros [htruthPi _] hsigma hpi.
    destruct hsigma as
      (s0 & s1 & s2 & s3 & s4 & s5 & s6 & s7 & hparent).
    destruct hpi as
      (leftIndex & left & rightIndex & right & p4 & p5 & p6 & p7 &
       hcode & hleft & hright).
    rewrite hcode in hparent.
    destruct (raw_rankZeroTruthCertificate_or_view M hPA
      (rawFormulaOrCode M left right) (rawNumeralValue M 1)
      (e 1) (e 0) left right eq_refl hparent) as
      (leftOutput & rightOutput & hleftZero & hrightZero & htable).
    destruct (raw_orTruth_one_elim M hPA leftOutput rightOutput htable)
      as [hleftOutput | hrightOutput].
    + subst leftOutput. exact (htruthPi leftIndex left hleftZero hleft).
    + subst rightOutput. exact (htruthPi rightIndex right hrightZero hright).
  - rewrite raw_sat_dynamicTruthSigmaQFEx8BranchFormula_iff.
    intros hsigma hpi.
    destruct hsigma as
      (s0 & s1 & s2 & s3 & s4 & s5 & s6 & s7 & hparent).
    unfold dynamicTruthPiAllEx8BranchFormula,
      dynamicTruthPiRowAllFormula, fixedLevelEx8,
      fixedLevelAnd3 in hpi.
    cbn [raw_formula_sat] in hpi.
    destruct hpi as (p0 & child & p2 & p3 & p4 & p5 & p6 & p7 & hcode & _).
    apply (proj1 (raw_sat_formulaAllCodeTermAt_iff M _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode.
    rewrite hcode in hparent.
    exact (raw_rankZeroTruthCertificate_all_false M hPA child
      (rawNumeralValue M 1) (e 1) (e 0) hparent).
  - rewrite raw_sat_dynamicTruthSigmaQFEx8BranchFormula_iff.
    intros hsigma hpi.
    destruct hsigma as
      (s0 & s1 & s2 & s3 & s4 & s5 & s6 & s7 & hparent).
    unfold dynamicTruthPiExistentialEx8BranchFormula,
      dynamicTruthPiExistentialLeafFormula,
      dynamicTruthPiRowExistentialPrefixFormula,
      fixedLevelEx8 in hpi.
    cbn [raw_formula_sat] in hpi.
    destruct hpi as (p0 & child & p2 & p3 & p4 & p5 & p6 & p7 & hcode & _).
    apply (proj1 (raw_sat_formulaExCodeTermAt_iff M _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode.
    rewrite hcode in hparent.
    exact (raw_rankZeroTruthCertificate_ex_false M hPA child
      (rawNumeralValue M 1) (e 1) (e 0) hparent).
  - rewrite raw_sat_dynamicTruthMixedQFReplayExclusivityFormula_iff.
    rewrite raw_sat_dynamicTruthSigmaImpFalseLeftEx8BranchFormula_iff.
    rewrite raw_sat_dynamicTruthPiQFEx8BranchFormula_iff.
    intros [htruthPi _] hsigma hpi.
    destruct hsigma as
      (leftIndex & left & rightIndex & right & s4 & s5 & s6 & s7 &
       hcode & hleft & _).
    destruct hpi as
      (p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & hparent).
    rewrite hcode in hparent.
    destruct (raw_rankZeroTruthCertificate_imp_view M hPA
      (rawFormulaImpCode M left right) (raw_zero M)
      (e 1) (e 0) left right eq_refl hparent) as
      (leftOutput & rightOutput & hleftZero & hrightZero & htable).
    destruct (raw_impTruth_zero_elim M hPA leftOutput rightOutput htable)
      as [hleftOutput hrightOutput].
    subst leftOutput. exact (htruthPi leftIndex left hleftZero hleft).
  - rewrite raw_sat_dynamicTruthMixedQFReplayExclusivityFormula_iff.
    rewrite raw_sat_dynamicTruthSigmaImpTrueRightEx8BranchFormula_iff.
    rewrite raw_sat_dynamicTruthPiQFEx8BranchFormula_iff.
    intros [_ hsigmaFalse] hsigma hpi.
    destruct hsigma as
      (leftIndex & left & rightIndex & right & s4 & s5 & s6 & s7 &
       hcode & hright & _).
    destruct hpi as
      (p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & hparent).
    rewrite hcode in hparent.
    destruct (raw_rankZeroTruthCertificate_imp_view M hPA
      (rawFormulaImpCode M left right) (raw_zero M)
      (e 1) (e 0) left right eq_refl hparent) as
      (leftOutput & rightOutput & hleftZero & hrightZero & htable).
    destruct (raw_impTruth_zero_elim M hPA leftOutput rightOutput htable)
      as [hleftOutput hrightOutput].
    subst rightOutput. exact (hsigmaFalse rightIndex right hright hrightZero).
  - rewrite raw_sat_dynamicTruthMixedQFReplayExclusivityFormula_iff.
    rewrite raw_sat_dynamicTruthSigmaAndEx8BranchFormula_iff.
    rewrite raw_sat_dynamicTruthPiQFEx8BranchFormula_iff.
    intros [_ hsigmaFalse] hsigma hpi.
    destruct hsigma as
      (leftIndex & left & rightIndex & right & s4 & s5 & s6 & s7 &
       hcode & hleft & hright).
    destruct hpi as
      (p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & hparent).
    rewrite hcode in hparent.
    destruct (raw_rankZeroTruthCertificate_and_view M hPA
      (rawFormulaAndCode M left right) (raw_zero M)
      (e 1) (e 0) left right eq_refl hparent) as
      (leftOutput & rightOutput & hleftZero & hrightZero & htable).
    destruct (raw_andTruth_zero_elim M hPA leftOutput rightOutput htable)
      as [hleftOutput | hrightOutput].
    + subst leftOutput. exact (hsigmaFalse leftIndex left hleft hleftZero).
    + subst rightOutput. exact (hsigmaFalse rightIndex right hright hrightZero).
  - rewrite raw_sat_dynamicTruthMixedQFReplayExclusivityFormula_iff.
    rewrite raw_sat_dynamicTruthSigmaOrEx8BranchFormula_iff.
    rewrite raw_sat_dynamicTruthPiQFEx8BranchFormula_iff.
    intros [_ hsigmaFalse] hsigma hpi.
    destruct hsigma as
      (leftIndex & left & rightIndex & right & s4 & s5 & s6 & s7 &
       hcode & [hleft | hright]).
    all: destruct hpi as
      (p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & hparent).
    all: rewrite hcode in hparent.
    all: destruct (raw_rankZeroTruthCertificate_or_view M hPA
      (rawFormulaOrCode M left right) (raw_zero M)
      (e 1) (e 0) left right eq_refl hparent) as
      (leftOutput & rightOutput & hleftZero & hrightZero & htable).
    all: destruct (raw_orTruth_zero_elim M hPA leftOutput rightOutput htable)
      as [hleftOutput hrightOutput].
    + subst leftOutput. exact (hsigmaFalse leftIndex left hleft hleftZero).
    + subst rightOutput. exact (hsigmaFalse rightIndex right hright hrightZero).
  - rewrite raw_sat_dynamicTruthPiQFEx8BranchFormula_iff.
    intros hsigma hpi.
    destruct hpi as
      (p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & hparent).
    unfold dynamicTruthSigmaEx8BranchFormula,
      dynamicTruthSigmaRowExFormula, fixedLevelEx8,
      fixedLevelAnd3 in hsigma.
    cbn [raw_formula_sat] in hsigma.
    destruct hsigma as (s0 & child & s2 & s3 & s4 & s5 & s6 & s7 & hcode & _).
    apply (proj1 (raw_sat_formulaExCodeTermAt_iff M _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode.
    rewrite hcode in hparent.
    exact (raw_rankZeroTruthCertificate_ex_false M hPA child
      (raw_zero M) (e 1) (e 0) hparent).
  - rewrite raw_sat_dynamicTruthPiQFEx8BranchFormula_iff.
    intros hsigma hpi.
    destruct hpi as
      (p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & hparent).
    unfold dynamicTruthSigmaUniversalEx8BranchFormula,
      dynamicTruthSigmaUniversalLeafFormula,
      dynamicTruthSigmaRowUniversalPrefixFormula,
      fixedLevelEx8 in hsigma.
    cbn [raw_formula_sat] in hsigma.
    destruct hsigma as (s0 & child & s2 & s3 & s4 & s5 & s6 & s7 & hcode & _).
    apply (proj1 (raw_sat_formulaAllCodeTermAt_iff M _ _ _)) in hcode.
    cbn [raw_term_eval scons] in hcode.
    rewrite hcode in hparent.
    exact (raw_rankZeroTruthCertificate_all_false M hPA child
      (raw_zero M) (e 1) (e 0) hparent).
Qed.

(** Sealing is used only to turn the already proved open validity theorem
    into an ordinary PA derivation; it introduces no semantic premise. *)
Theorem PA_proves_dynamicTruthMixedQFCellFormula : forall
    cell lowerPiApplication lowerSigmaApplication,
  Formula.BProv Formula.Ax_s []
    (dynamicTruthMixedQFCellFormula cell
      lowerPiApplication lowerSigmaApplication).
Proof.
  intros cell lowerPiApplication lowerSigmaApplication.
  apply PA_proves_open_formula_of_raw_valid.
  exact (dynamicTruthMixedQFCellFormula_raw_valid
    cell lowerPiApplication lowerSigmaApplication).
Qed.

(** ------------------------------------------------------------------
    Literal carrier branch and cell polynomials. *)

Definition rawDynamicTruthMixedQFSigmaBranchCode
    (M : RawPAModel) (cell : DynamicTruthMixedQFCell)
    (lowerPiApplication : M) : M :=
  match cell with
  | DTMQFSigmaQFPiImp
  | DTMQFSigmaQFPiAnd
  | DTMQFSigmaQFPiOr
  | DTMQFSigmaQFPiAll
  | DTMQFSigmaQFPiEx => rawDynamicTruthSigmaQFEx8BranchCode M
  | DTMQFSigmaImpFalseLeftPiQF =>
      rawDynamicTruthSigmaImpFalseLeftEx8BranchCode M
  | DTMQFSigmaImpTrueRightPiQF =>
      rawDynamicTruthSigmaImpTrueRightEx8BranchCode M
  | DTMQFSigmaAndPiQF => rawDynamicTruthSigmaAndEx8BranchCode M
  | DTMQFSigmaOrPiQF => rawDynamicTruthSigmaOrEx8BranchCode M
  | DTMQFSigmaExPiQF => rawDynamicTruthSigmaEx8BranchCode M
  | DTMQFSigmaAllPiQF =>
      rawDynamicTruthSigmaUniversalEx8BranchCode M lowerPiApplication
  end.

Definition rawDynamicTruthMixedQFPiBranchCode
    (M : RawPAModel) (cell : DynamicTruthMixedQFCell)
    (lowerSigmaApplication : M) : M :=
  match cell with
  | DTMQFSigmaQFPiImp => rawDynamicTruthPiImpEx8BranchCode M
  | DTMQFSigmaQFPiAnd => rawDynamicTruthPiAndEx8BranchCode M
  | DTMQFSigmaQFPiOr => rawDynamicTruthPiOrEx8BranchCode M
  | DTMQFSigmaQFPiAll => rawDynamicTruthPiAllEx8BranchCode M
  | DTMQFSigmaQFPiEx =>
      rawDynamicTruthPiExistentialEx8BranchCode M lowerSigmaApplication
  | DTMQFSigmaImpFalseLeftPiQF
  | DTMQFSigmaImpTrueRightPiQF
  | DTMQFSigmaAndPiQF
  | DTMQFSigmaOrPiQF
  | DTMQFSigmaExPiQF
  | DTMQFSigmaAllPiQF => rawDynamicTruthPiQFEx8BranchCode M
  end.

Definition rawDynamicTruthMixedQFReplayExclusivityCode
    (M : RawPAModel) : M :=
  rawFixedFormulaNumeralCode M
    dynamicTruthMixedQFReplayExclusivityFormula.

Definition rawDynamicTruthMixedQFCollisionCode
    (M : RawPAModel) (cell : DynamicTruthMixedQFCell)
    (lowerPiApplication lowerSigmaApplication : M) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthMixedQFSigmaBranchCode M cell lowerPiApplication)
    (rawFormulaImpCode M
      (rawDynamicTruthMixedQFPiBranchCode M cell lowerSigmaApplication)
      (rawFormulaBotCode M)).

Definition rawDynamicTruthMixedQFCellCode
    (M : RawPAModel) (cell : DynamicTruthMixedQFCell)
    (lowerPiApplication lowerSigmaApplication : M) : M :=
  match cell with
  | DTMQFSigmaQFPiImp
  | DTMQFSigmaQFPiAnd
  | DTMQFSigmaQFPiOr
  | DTMQFSigmaImpFalseLeftPiQF
  | DTMQFSigmaImpTrueRightPiQF
  | DTMQFSigmaAndPiQF
  | DTMQFSigmaOrPiQF =>
      rawFormulaImpCode M
        (rawDynamicTruthMixedQFReplayExclusivityCode M)
        (rawDynamicTruthMixedQFCollisionCode M cell
          lowerPiApplication lowerSigmaApplication)
  | DTMQFSigmaQFPiAll
  | DTMQFSigmaQFPiEx
  | DTMQFSigmaExPiQF
  | DTMQFSigmaAllPiQF =>
      rawDynamicTruthMixedQFCollisionCode M cell
        lowerPiApplication lowerSigmaApplication
  end.

(** Exact carrier-level irrelevance for the nine fixed-code cells.  The
    quantified Pi-Ex and Sigma-All leaves are intentionally absent: their
    lower application is genuine syntax data and cannot be discarded. *)
Lemma rawDynamicTruthMixedQFCellCode_fixed_lower_irrelevant : forall
    (M : RawPAModel) cell,
  In cell dynamicTruthMixedQFFixedCodeCells -> forall
    lowerPiApplication lowerSigmaApplication
    lowerPiApplication' lowerSigmaApplication',
  rawDynamicTruthMixedQFCellCode M cell
    lowerPiApplication lowerSigmaApplication =
  rawDynamicTruthMixedQFCellCode M cell
    lowerPiApplication' lowerSigmaApplication'.
Proof.
  intros M cell hFixed lowerPiApplication lowerSigmaApplication
    lowerPiApplication' lowerSigmaApplication'.
  destruct cell.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn in hFixed. intuition congruence.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn in hFixed. intuition congruence.
Qed.

Lemma rawDynamicTruthMixedQFReplayExclusivityCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthMixedQFReplayExclusivityCode M =
  rawQuotedFormulaCode M dynamicTruthMixedQFReplayExclusivityFormula.
Proof.
  intros M hPA.
  unfold rawDynamicTruthMixedQFReplayExclusivityCode.
  apply rawFixedFormulaNumeralCode_eq_quoted. exact hPA.
Qed.

(** The aligned-QF module exposes numeral equations for the two selected
    branch codes.  The following tiny adapters recover quotation equations,
    which are the form needed by the uniform mixed-cell map. *)
Lemma rawDynamicTruthMixedSigmaQFEx8BranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthSigmaQFEx8BranchCode M =
  rawQuotedFormulaCode M dynamicTruthSigmaQFEx8BranchFormula.
Proof.
  intros M hPA.
  rewrite rawDynamicTruthSigmaQFEx8BranchCode_eq_numeral by exact hPA.
  symmetry. apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Lemma rawDynamicTruthMixedPiQFEx8BranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthPiQFEx8BranchCode M =
  rawQuotedFormulaCode M dynamicTruthPiQFEx8BranchFormula.
Proof.
  intros M hPA.
  rewrite rawDynamicTruthPiQFEx8BranchCode_eq_numeral by exact hPA.
  symmetry. apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

Lemma rawDynamicTruthMixedQFSigmaBranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cell lowerPiApplication,
  rawDynamicTruthMixedQFSigmaBranchCode M cell
    (rawQuotedFormulaCode M lowerPiApplication) =
  rawQuotedFormulaCode M
    (dynamicTruthMixedQFSigmaBranchFormula cell lowerPiApplication).
Proof.
  intros M hPA cell lowerPiApplication.
  destruct cell.
  - exact (rawDynamicTruthMixedSigmaQFEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthMixedSigmaQFEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthMixedSigmaQFEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthMixedSigmaQFEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthMixedSigmaQFEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthSigmaImpFalseLeftEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthSigmaImpTrueRightEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthSigmaAndEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthSigmaOrEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthSigmaEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthSigmaUniversalEx8BranchCode_eq_quoted
      M hPA lowerPiApplication).
Qed.

Lemma rawDynamicTruthMixedQFPiBranchCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cell lowerSigmaApplication,
  rawDynamicTruthMixedQFPiBranchCode M cell
    (rawQuotedFormulaCode M lowerSigmaApplication) =
  rawQuotedFormulaCode M
    (dynamicTruthMixedQFPiBranchFormula cell lowerSigmaApplication).
Proof.
  intros M hPA cell lowerSigmaApplication.
  destruct cell.
  - exact (rawDynamicTruthPiImpEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthPiAndEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthPiOrEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthPiAllEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthPiExistentialEx8BranchCode_eq_quoted
      M hPA lowerSigmaApplication).
  - exact (rawDynamicTruthMixedPiQFEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthMixedPiQFEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthMixedPiQFEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthMixedPiQFEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthMixedPiQFEx8BranchCode_eq_quoted M hPA).
  - exact (rawDynamicTruthMixedPiQFEx8BranchCode_eq_quoted M hPA).
Qed.

Lemma rawDynamicTruthMixedQFCellCode_eq_quoted : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cell lowerPiApplication lowerSigmaApplication,
  rawDynamicTruthMixedQFCellCode M cell
    (rawQuotedFormulaCode M lowerPiApplication)
    (rawQuotedFormulaCode M lowerSigmaApplication) =
  rawQuotedFormulaCode M
    (dynamicTruthMixedQFCellFormula cell
      lowerPiApplication lowerSigmaApplication).
Proof.
  intros M hPA cell lowerPiApplication lowerSigmaApplication.
  destruct cell.
  all: unfold rawDynamicTruthMixedQFCellCode.
  all: unfold dynamicTruthMixedQFCellFormula.
  all: unfold rawDynamicTruthMixedQFCollisionCode.
  all: rewrite rawDynamicTruthMixedQFSigmaBranchCode_eq_quoted
    by exact hPA.
  all: rewrite rawDynamicTruthMixedQFPiBranchCode_eq_quoted
    by exact hPA.
  all: try rewrite rawDynamicTruthMixedQFReplayExclusivityCode_eq_quoted
    by exact hPA.
  all: reflexivity.
Qed.

Lemma rawDynamicTruthMixedQFCellCode_eq_numeral : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cell lowerPiApplication lowerSigmaApplication,
  rawDynamicTruthMixedQFCellCode M cell
    (rawQuotedFormulaCode M lowerPiApplication)
    (rawQuotedFormulaCode M lowerSigmaApplication) =
  rawNumeralValue M
    (formulaCode (dynamicTruthMixedQFCellFormula cell
      lowerPiApplication lowerSigmaApplication)).
Proof.
  intros M hPA cell lowerPiApplication lowerSigmaApplication.
  rewrite rawDynamicTruthMixedQFCellCode_eq_quoted by exact hPA.
  apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

(** Every standard specialization has an ordinary represented PA proof.
    For the two opaque binder leaves, arbitrary-carrier compilation is kept
    separate below; this theorem makes no illicit decoding assumption. *)
Theorem raw_codedPAProofOf_dynamicTruthMixedQFCell : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cell lowerPiApplication lowerSigmaApplication,
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthMixedQFCellCode M cell
        (rawQuotedFormulaCode M lowerPiApplication)
        (rawQuotedFormulaCode M lowerSigmaApplication)) certificate.
Proof.
  intros M hPA cell lowerPiApplication lowerSigmaApplication.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    (dynamicTruthMixedQFCellFormula cell
      lowerPiApplication lowerSigmaApplication)
    (PA_proves_dynamicTruthMixedQFCellFormula cell
      lowerPiApplication lowerSigmaApplication))
    as [certificate hcertificate].
  exists certificate.
  rewrite rawDynamicTruthMixedQFCellCode_eq_numeral by exact hPA.
  exact hcertificate.
Qed.

(** Standard quotation is unnecessary for the nine fixed-code cells.  Their
    carrier arguments are definitionally irrelevant, so the standard proof
    at two bottom formulae transports to arbitrary carrier inputs. *)
Theorem raw_codedPAProofOf_dynamicTruthMixedQFFixedCell : forall
    (M : RawPAModel), RawPASatisfies M -> forall cell,
  In cell dynamicTruthMixedQFFixedCodeCells -> forall
    lowerPiApplication lowerSigmaApplication,
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthMixedQFCellCode M cell
        lowerPiApplication lowerSigmaApplication) certificate.
Proof.
  intros M hPA cell hFixed lowerPiApplication lowerSigmaApplication.
  destruct (raw_codedPAProofOf_dynamicTruthMixedQFCell M hPA cell
    pBot pBot) as [certificate hcertificate].
  exists certificate.
  rewrite (rawDynamicTruthMixedQFCellCode_fixed_lower_irrelevant
    M cell hFixed lowerPiApplication lowerSigmaApplication
    (rawQuotedFormulaCode M pBot) (rawQuotedFormulaCode M pBot)).
  exact hcertificate.
Qed.

(** ------------------------------------------------------------------
    Exact common-context elimination.

    Seven cells additionally consume the replay root; quantified cells use
    the two-implication collision directly.  The optional replay argument is
    represented by a sum, so no dummy carrier element or broad global
    assumption is smuggled into the four unconditional cases. *)

(** Naming the replay-root judgement before placing it in an indexed family
    keeps positivity checking from repeatedly normalizing the large local
    proof package.  The alias is definitionally exact. *)
Definition RawDynamicTruthMixedQFReplayRootAt
    (M : RawPAModel) (context root : M) : Prop :=
  RawCodedPALocalProofOf M context
    (rawDynamicTruthMixedQFReplayExclusivityCode M) root.

Arguments RawDynamicTruthMixedQFReplayRootAt
  M context root : clear implicits.

(** A transparent cell-indexed family avoids an expensive positivity check
    over the large local-proof judgement.  Replay cells carry a dependent
    pair of a root and its exact local proof; quantified cells carry [unit]. *)
Definition RawDynamicTruthMixedQFCellPremiseRoots
    (M : RawPAModel) (context : M)
    (cell : DynamicTruthMixedQFCell) : Type :=
  match cell with
  | DTMQFSigmaQFPiImp
  | DTMQFSigmaQFPiAnd
  | DTMQFSigmaQFPiOr
  | DTMQFSigmaImpFalseLeftPiQF
  | DTMQFSigmaImpTrueRightPiQF
  | DTMQFSigmaAndPiQF
  | DTMQFSigmaOrPiQF =>
      { root : M & RawDynamicTruthMixedQFReplayRootAt M context root }
  | DTMQFSigmaQFPiAll
  | DTMQFSigmaQFPiEx
  | DTMQFSigmaExPiQF
  | DTMQFSigmaAllPiQF => unit
  end.

(** Smart constructors retain the finite-membership evidence at the public
    boundary, while the stored value itself is minimal. *)
Definition RDTMQFReplayPremiseRoot (M : RawPAModel) (context : M)
    (cell : DynamicTruthMixedQFCell) (root : M) :
  In cell dynamicTruthMixedQFReplayCells ->
  RawDynamicTruthMixedQFReplayRootAt M context root ->
  RawDynamicTruthMixedQFCellPremiseRoots M context cell.
Proof.
  intros hCell hRoot. destruct cell.
  - exact (existT _ root hRoot).
  - exact (existT _ root hRoot).
  - exact (existT _ root hRoot).
  - exact tt.
  - exact tt.
  - exact (existT _ root hRoot).
  - exact (existT _ root hRoot).
  - exact (existT _ root hRoot).
  - exact (existT _ root hRoot).
  - exact tt.
  - exact tt.
Defined.

Definition RDTMQFQuantifierNoPremise (M : RawPAModel) (context : M)
    (cell : DynamicTruthMixedQFCell) :
  In cell dynamicTruthMixedQFQuantifierCells ->
  RawDynamicTruthMixedQFCellPremiseRoots M context cell.
Proof.
  intro hCell. destruct cell.
  - elim (dynamicTruthMixedQFLogicalPartitions_disjoint_rev
      DTMQFSigmaQFPiImp hCell). cbn; intuition.
  - elim (dynamicTruthMixedQFLogicalPartitions_disjoint_rev
      DTMQFSigmaQFPiAnd hCell). cbn; intuition.
  - elim (dynamicTruthMixedQFLogicalPartitions_disjoint_rev
      DTMQFSigmaQFPiOr hCell). cbn; intuition.
  - exact tt.
  - exact tt.
  - elim (dynamicTruthMixedQFLogicalPartitions_disjoint_rev
      DTMQFSigmaImpFalseLeftPiQF hCell). cbn; intuition.
  - elim (dynamicTruthMixedQFLogicalPartitions_disjoint_rev
      DTMQFSigmaImpTrueRightPiQF hCell). cbn; intuition.
  - elim (dynamicTruthMixedQFLogicalPartitions_disjoint_rev
      DTMQFSigmaAndPiQF hCell). cbn; intuition.
  - elim (dynamicTruthMixedQFLogicalPartitions_disjoint_rev
      DTMQFSigmaOrPiQF hCell). cbn; intuition.
  - exact tt.
  - exact tt.
Defined.

Definition rawDynamicTruthMixedQFReplayCellCollisionRoot
    (M : RawPAModel) (context : M) (cell : DynamicTruthMixedQFCell)
    (lowerPiApplication lowerSigmaApplication cellRoot
      sigmaRoot piRoot : M)
    (premise : { root : M &
      RawDynamicTruthMixedQFReplayRootAt M context root }) : M :=
  match premise with
  | existT _ replayRoot _ =>
      rawDynamicTruthImpConditionalCellCollisionRoot M context
        (rawDynamicTruthMixedQFReplayExclusivityCode M)
        (rawDynamicTruthMixedQFSigmaBranchCode M cell lowerPiApplication)
        (rawDynamicTruthMixedQFPiBranchCode M cell lowerSigmaApplication)
        cellRoot replayRoot sigmaRoot piRoot
  end.

Definition rawDynamicTruthMixedQFQuantifierCellCollisionRoot
    (M : RawPAModel) (context : M) (cell : DynamicTruthMixedQFCell)
    (lowerPiApplication lowerSigmaApplication cellRoot
      sigmaRoot piRoot : M) : M :=
  rawDynamicTruthQFBranchCollisionRoot M context
    (rawDynamicTruthMixedQFSigmaBranchCode M cell lowerPiApplication)
    (rawDynamicTruthMixedQFPiBranchCode M cell lowerSigmaApplication)
    cellRoot sigmaRoot piRoot.

Definition rawDynamicTruthMixedQFCellCollisionRoot
    (M : RawPAModel) (context : M) (cell : DynamicTruthMixedQFCell)
    (lowerPiApplication lowerSigmaApplication cellRoot
      sigmaRoot piRoot : M)
    (premise : RawDynamicTruthMixedQFCellPremiseRoots M context cell) : M :=
  match cell as selected return
      RawDynamicTruthMixedQFCellPremiseRoots M context selected -> M with
  | DTMQFSigmaQFPiImp =>
      rawDynamicTruthMixedQFReplayCellCollisionRoot M context
        DTMQFSigmaQFPiImp lowerPiApplication lowerSigmaApplication
        cellRoot sigmaRoot piRoot
  | DTMQFSigmaQFPiAnd =>
      rawDynamicTruthMixedQFReplayCellCollisionRoot M context
        DTMQFSigmaQFPiAnd lowerPiApplication lowerSigmaApplication
        cellRoot sigmaRoot piRoot
  | DTMQFSigmaQFPiOr =>
      rawDynamicTruthMixedQFReplayCellCollisionRoot M context
        DTMQFSigmaQFPiOr lowerPiApplication lowerSigmaApplication
        cellRoot sigmaRoot piRoot
  | DTMQFSigmaQFPiAll => fun _ =>
      rawDynamicTruthMixedQFQuantifierCellCollisionRoot M context
        DTMQFSigmaQFPiAll lowerPiApplication lowerSigmaApplication
        cellRoot sigmaRoot piRoot
  | DTMQFSigmaQFPiEx => fun _ =>
      rawDynamicTruthMixedQFQuantifierCellCollisionRoot M context
        DTMQFSigmaQFPiEx lowerPiApplication lowerSigmaApplication
        cellRoot sigmaRoot piRoot
  | DTMQFSigmaImpFalseLeftPiQF =>
      rawDynamicTruthMixedQFReplayCellCollisionRoot M context
        DTMQFSigmaImpFalseLeftPiQF
        lowerPiApplication lowerSigmaApplication cellRoot sigmaRoot piRoot
  | DTMQFSigmaImpTrueRightPiQF =>
      rawDynamicTruthMixedQFReplayCellCollisionRoot M context
        DTMQFSigmaImpTrueRightPiQF
        lowerPiApplication lowerSigmaApplication cellRoot sigmaRoot piRoot
  | DTMQFSigmaAndPiQF =>
      rawDynamicTruthMixedQFReplayCellCollisionRoot M context
        DTMQFSigmaAndPiQF lowerPiApplication lowerSigmaApplication
        cellRoot sigmaRoot piRoot
  | DTMQFSigmaOrPiQF =>
      rawDynamicTruthMixedQFReplayCellCollisionRoot M context
        DTMQFSigmaOrPiQF lowerPiApplication lowerSigmaApplication
        cellRoot sigmaRoot piRoot
  | DTMQFSigmaExPiQF => fun _ =>
      rawDynamicTruthMixedQFQuantifierCellCollisionRoot M context
        DTMQFSigmaExPiQF lowerPiApplication lowerSigmaApplication
        cellRoot sigmaRoot piRoot
  | DTMQFSigmaAllPiQF => fun _ =>
      rawDynamicTruthMixedQFQuantifierCellCollisionRoot M context
        DTMQFSigmaAllPiQF lowerPiApplication lowerSigmaApplication
        cellRoot sigmaRoot piRoot
  end premise.

Arguments rawDynamicTruthMixedQFCellCollisionRoot
  M context cell lowerPiApplication lowerSigmaApplication
    cellRoot sigmaRoot piRoot premise : clear implicits.

Theorem raw_codedPALocalProofOf_dynamicTruthMixedQFCellCollision : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context cell lowerPiApplication lowerSigmaApplication
      cellRoot sigmaRoot piRoot
      (premise : RawDynamicTruthMixedQFCellPremiseRoots M context cell),
  RawCodedPALocalProofOf M context
    (rawDynamicTruthMixedQFCellCode M cell
      lowerPiApplication lowerSigmaApplication) cellRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthMixedQFSigmaBranchCode M cell lowerPiApplication)
    sigmaRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthMixedQFPiBranchCode M cell lowerSigmaApplication)
    piRoot ->
  RawCodedPALocalProofOf M context (rawFormulaBotCode M)
    (rawDynamicTruthMixedQFCellCollisionRoot M context cell
      lowerPiApplication lowerSigmaApplication
      cellRoot sigmaRoot piRoot premise).
Proof.
  intros M hPA context cell lowerPiApplication lowerSigmaApplication
    cellRoot sigmaRoot piRoot premise hcell hsigma hpi.
  destruct cell.
  1-3: (
    destruct premise as [replayRoot hreplay];
    unfold rawDynamicTruthMixedQFCellCode,
      rawDynamicTruthMixedQFCollisionCode in hcell;
    exact (raw_codedPALocalProofOf_dynamicTruthImpConditionalCellCollision
      M hPA context
      (rawDynamicTruthMixedQFReplayExclusivityCode M) _ _
      cellRoot replayRoot sigmaRoot piRoot
      hcell hreplay hsigma hpi)).
  3-6: (
    destruct premise as [replayRoot hreplay];
    unfold rawDynamicTruthMixedQFCellCode,
      rawDynamicTruthMixedQFCollisionCode in hcell;
    exact (raw_codedPALocalProofOf_dynamicTruthImpConditionalCellCollision
      M hPA context
      (rawDynamicTruthMixedQFReplayExclusivityCode M) _ _
      cellRoot replayRoot sigmaRoot piRoot
      hcell hreplay hsigma hpi)).
  all: destruct premise;
    unfold rawDynamicTruthMixedQFCellCode,
      rawDynamicTruthMixedQFCollisionCode in hcell;
    exact (raw_codedPALocalProofOf_dynamicTruthQFBranchCollision
      M hPA context _ _ cellRoot sigmaRoot piRoot hcell hsigma hpi).
Qed.

(** The only remaining nonstandard code-generation obligation is stated at
    its exact boundary: the two lower-dependent quantified cells.  All nine
    carrier-independent cells already specialize to fixed PA formulae, and
    all eleven standard quoted specializations are proved above. *)
Definition RawDynamicTruthMixedQFOpaqueQuantifierCellProofCompiler
    (M : RawPAModel) : Prop :=
  (forall lowerSigmaApplication : M,
    exists certificate : M,
      RawCodedPAProofOf M
        (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
          (rawFormulaBotCode M) lowerSigmaApplication) certificate) /\
  (forall lowerPiApplication : M,
    exists certificate : M,
      RawCodedPAProofOf M
        (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
          lowerPiApplication (rawFormulaBotCode M)) certificate).

(** This all-eleven interface makes the remaining boundary measurable.  The
    adapter below discharges nine constructors internally and asks the
    caller only for the two genuinely lower-dependent compiler clauses. *)
Definition RawDynamicTruthMixedQFCellProofCompilerTotal
    (M : RawPAModel) : Prop :=
  forall cell lowerPiApplication lowerSigmaApplication,
    exists certificate : M,
      RawCodedPAProofOf M
        (rawDynamicTruthMixedQFCellCode M cell
          lowerPiApplication lowerSigmaApplication) certificate.

Theorem raw_dynamicTruthMixedQFCellProofCompilerTotal_of_opaque : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthMixedQFOpaqueQuantifierCellProofCompiler M ->
  RawDynamicTruthMixedQFCellProofCompilerTotal M.
Proof.
  intros M hPA [hPiEx hSigmaAll] cell
    lowerPiApplication lowerSigmaApplication.
  destruct cell.
  - apply (raw_codedPAProofOf_dynamicTruthMixedQFFixedCell M hPA
      DTMQFSigmaQFPiImp); cbn; intuition.
  - apply (raw_codedPAProofOf_dynamicTruthMixedQFFixedCell M hPA
      DTMQFSigmaQFPiAnd); cbn; intuition.
  - apply (raw_codedPAProofOf_dynamicTruthMixedQFFixedCell M hPA
      DTMQFSigmaQFPiOr); cbn; intuition.
  - apply (raw_codedPAProofOf_dynamicTruthMixedQFFixedCell M hPA
      DTMQFSigmaQFPiAll); cbn; intuition.
  - change (exists certificate : M,
      RawCodedPAProofOf M
        (rawDynamicTruthMixedQFCellCode M DTMQFSigmaQFPiEx
          (rawFormulaBotCode M) lowerSigmaApplication) certificate).
    exact (hPiEx lowerSigmaApplication).
  - apply (raw_codedPAProofOf_dynamicTruthMixedQFFixedCell M hPA
      DTMQFSigmaImpFalseLeftPiQF); cbn; intuition.
  - apply (raw_codedPAProofOf_dynamicTruthMixedQFFixedCell M hPA
      DTMQFSigmaImpTrueRightPiQF); cbn; intuition.
  - apply (raw_codedPAProofOf_dynamicTruthMixedQFFixedCell M hPA
      DTMQFSigmaAndPiQF); cbn; intuition.
  - apply (raw_codedPAProofOf_dynamicTruthMixedQFFixedCell M hPA
      DTMQFSigmaOrPiQF); cbn; intuition.
  - apply (raw_codedPAProofOf_dynamicTruthMixedQFFixedCell M hPA
      DTMQFSigmaExPiQF); cbn; intuition.
  - change (exists certificate : M,
      RawCodedPAProofOf M
        (rawDynamicTruthMixedQFCellCode M DTMQFSigmaAllPiQF
          lowerPiApplication (rawFormulaBotCode M)) certificate).
    exact (hSigmaAll lowerPiApplication).
Qed.

End PABoundedRawCodedDynamicTruthMixedQFBranchExclusivity.
