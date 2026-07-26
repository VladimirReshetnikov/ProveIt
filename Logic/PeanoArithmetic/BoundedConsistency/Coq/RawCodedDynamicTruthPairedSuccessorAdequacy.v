(**
  Atomic adequacy of the paired dynamic-truth successor row.

  The two component graphs deliberately stop at honest operation
  interfaces: each rank-domain formula is obtained by represented
  substitution of a possibly nonstandard numeral code, and each lower
  polarity is applied by three represented substitutions.  This module
  discharges those interfaces on the invariant actually carried by the
  paired orbit, namely [RawCodedFormulaAtomicallyAdequate].

  One structural fact is needed in addition to substitution preservation.
  The transparent row assembler forms implications, conjunctions,
  disjunctions, and quantifiers around adequate carrier-valued children.
  Atomic adequacy was not previously exported with constructor closure
  lemmas.  We prove that closure below without decoding a carrier code: PA
  induction constructs the identity formula shift with amount zero, and the
  already verified shift-target theorem supplies atomic adequacy of the
  resulting constructor code.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedAdditionLaws RawCodedSyntaxConstructors
  RawCodedAssignment RawCodedAssignmentTotality
  RawCodedFormulaRankStep RawCodedFormulaRankTraversal
  RawCodedFormulaRankTotality
  RawCodedTermEvaluationTraversal RawCodedTermEvaluationRealization
  RawCodedFormulaOperations
  RawCodedFormulaOperationTreeRealization
  RawCodedNumeralTermCode RawCodedNumeralTermShift
  RawCodedTermShiftSyntaxRealization
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedPAAxiomContextSelfShift
  RawCodedFormulaShiftTreeRealization
  RawCodedFormulaShiftTotality
  RawCodedFormulaOperationTraceConcatenation
  RawCodedFormulaShiftAtomicAdequacy
  RawCodedProofAtomicAdequacyStandard
  RawCodedTermOpeningTotalityDischarge
  RawCodedFormulaSingleSubstitutionAtomicAdequacy
  RawCodedTermOpeningAfterShiftSyntaxStability
  RawCodedDynamicTruthTernaryApplicationTotality
  RawCodedCarrierIndexedPairedAdequateCodeOrbitGraph
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorRowGraph.

Module PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedAdditionLaws.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationTreeRealization.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedNumeralTermShift.
Import PABoundedRawCodedTermShiftSyntaxRealization.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedFormulaOperationTraceConcatenation.
Import PABoundedRawCodedFormulaShiftAtomicAdequacy.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedTermOpeningTotalityDischarge.
Import PABoundedRawCodedFormulaSingleSubstitutionAtomicAdequacy.
Import PABoundedRawCodedTermOpeningAfterShiftSyntaxStability.
Import PABoundedRawCodedDynamicTruthTernaryApplicationTotality.
Import PABoundedRawCodedCarrierIndexedPairedAdequateCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.

(** ------------------------------------------------------------------
    Identity term shifts with zero amount.

    The existing term-shift totality theorem may choose an abstract target.
    Constructor adequacy needs the stronger, exact target [input].  The
    following represented strong induction follows an arbitrary nonstandard
    syntax support table and chooses the identity row at every constructor.
*)

Lemma raw_codedTermShift_variable_zero_amount_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff index,
  RawCodedTermShift M cutoff (raw_zero M)
    (rawTermVarCode M index) (rawTermVarCode M index).
Proof.
  intros M hPA cutoff index.
  destruct (raw_le_or_gt M hPA cutoff index) as [hhigh | hlow].
  - assert (hrow : RawCodedTermShiftTraversalRow M cutoff (raw_zero M)
        (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
        (raw_zero M) (rawTermVarCode M index) (rawTermVarCode M index)).
    {
      left. exists index, index.
      split; [reflexivity |]. split; [reflexivity |].
      right. split; [exact hhigh |].
      symmetry. exact (raw_add_zero_right M hPA index).
    }
    destruct (raw_termShiftTraversalBundle_append M hPA
      cutoff (raw_zero M)
      (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
      (raw_zero M) (rawTermVarCode M index) (rawTermVarCode M index)
      (raw_termShiftTraversalBundle_empty M hPA cutoff (raw_zero M)) hrow)
      as (sourceCode & sourceStep & targetCode & targetStep &
          hbundle & _ & hroot).
    exists sourceCode, sourceStep, targetCode, targetStep,
      (raw_succ M (raw_zero M)), (raw_zero M).
    destruct hbundle as [hsource [htarget [hrows hnonnegative]]].
    exact (conj hsource
      (conj htarget
        (conj (raw_assignment_lt_self_succ M hPA (raw_zero M))
          (conj hroot (conj hrows hnonnegative))))).
  - exact (raw_codedTermShift_variable_identity M hPA
      cutoff (raw_zero M) index hlow).
Qed.

Definition RawCodedTermZeroShiftBelow (M : RawPAModel)
    (cutoff supportCode supportStep current : M) : Prop :=
  forall input : M,
    rawLt M input current ->
    rawTermCodeSupported M supportCode supportStep input ->
    RawCodedTermShift M cutoff (raw_zero M) input input.

Arguments RawCodedTermZeroShiftBelow
  M cutoff supportCode supportStep current : clear implicits.

Definition codedTermZeroShiftBelowTermAt
    (cutoff supportCode supportStep current : term) : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 current))
      (pImp
        (termCodeSupportedTermAt
          (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
        (codedTermShiftTermAt
          (liftTerm 1 cutoff) tZero (tVar 0) (tVar 0)))).

Lemma raw_sat_codedTermZeroShiftBelowTermAt_iff : forall
    (M : RawPAModel) e cutoff supportCode supportStep current,
  raw_formula_sat M e
    (codedTermZeroShiftBelowTermAt
      cutoff supportCode supportStep current) <->
  RawCodedTermZeroShiftBelow M
    (raw_term_eval M e cutoff)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold codedTermZeroShiftBelowTermAt,
    RawCodedTermZeroShiftBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_termCodeSupportedTermAt_iff.
  setoid_rewrite raw_sat_codedTermShiftTermAt_iff.
  repeat setoid_rewrite raw_shiftTotality_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_codedTermZeroShiftBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff supportCode supportStep,
  RawCodedTermZeroShiftBelow M cutoff supportCode supportStep
    (raw_zero M).
Proof.
  intros M hPA cutoff supportCode supportStep input hinput _.
  exfalso. exact (raw_not_lt_zero M hPA input hinput).
Qed.

Lemma raw_codedTermZeroShiftBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff limit supportCode supportStep current,
  RawTermSyntaxTraversal M limit supportCode supportStep ->
  rawLt M current limit ->
  RawCodedTermZeroShiftBelow M cutoff supportCode supportStep current ->
  RawCodedTermZeroShiftBelow M cutoff supportCode supportStep
    (raw_succ M current).
Proof.
  intros M hPA cutoff limit supportCode supportStep current
    [_ hsyntaxRows] hcurrentBound hprefix input hinput hsupported.
  destruct (raw_lt_succ_cases M hPA input current hinput)
    as [hbefore | ->].
  - exact (hprefix input hbefore hsupported).
  - destruct (hsyntaxRows current hcurrentBound hsupported)
      as (left & right & hshape).
    destruct hshape as
      [hvar | [hzero | [hsucc | [hadd | hmul]]]].
    + subst current.
      exact (raw_codedTermShift_variable_zero_amount_identity
        M hPA cutoff left).
    + subst current.
      exact (raw_codedTermShift_zero_identity
        M hPA cutoff (raw_zero M)).
    + destruct hsucc as [hcode [hchildSupported hchild]].
      subst current.
      apply (raw_codedTermShift_succ_identity M hPA
        cutoff (raw_zero M) left).
      exact (hprefix left hchild hchildSupported).
    + destruct hadd as
        [hcode [hleftSupported [hrightSupported [hleft hright]]]].
      subst current.
      apply (raw_codedTermShift_add_identity M hPA
        cutoff (raw_zero M) left right).
      * exact (hprefix left hleft hleftSupported).
      * exact (hprefix right hright hrightSupported).
    + destruct hmul as
        [hcode [hleftSupported [hrightSupported [hleft hright]]]].
      subst current.
      apply (raw_codedTermShift_mul_identity M hPA
        cutoff (raw_zero M) left right).
      * exact (hprefix left hleft hleftSupported).
      * exact (hprefix right hright hrightSupported).
Qed.

Definition RawCodedTermZeroShiftWithin (M : RawPAModel)
    (cutoff limit supportCode supportStep current : M) : Prop :=
  rawLe M current limit ->
  RawCodedTermZeroShiftBelow M
    cutoff supportCode supportStep current.

Arguments RawCodedTermZeroShiftWithin
  M cutoff limit supportCode supportStep current : clear implicits.

Definition codedTermZeroShiftWithinTermAt
    (cutoff limit supportCode supportStep current : term) : formula :=
  pImp
    (Formula.leTermAt current limit)
    (codedTermZeroShiftBelowTermAt
      cutoff supportCode supportStep current).

Lemma raw_sat_codedTermZeroShiftWithinTermAt_iff : forall
    (M : RawPAModel) e cutoff limit supportCode supportStep current,
  raw_formula_sat M e
    (codedTermZeroShiftWithinTermAt
      cutoff limit supportCode supportStep current) <->
  RawCodedTermZeroShiftWithin M
    (raw_term_eval M e cutoff) (raw_term_eval M e limit)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold codedTermZeroShiftWithinTermAt,
    RawCodedTermZeroShiftWithin.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank,
    raw_sat_codedTermZeroShiftBelowTermAt_iff.
  reflexivity.
Qed.

Theorem raw_codedTermZeroShiftWithin_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff limit supportCode supportStep,
  RawTermSyntaxTraversal M limit supportCode supportStep ->
  forall current,
    RawCodedTermZeroShiftWithin M
      cutoff limit supportCode supportStep current.
Proof.
  intros M hPA cutoff limit supportCode supportStep hsyntax.
  set (parameterEnv := scons M cutoff
    (scons M limit (scons M supportCode
      (scons M supportStep (fun _ : nat => raw_zero M))))).
  set (phi := codedTermZeroShiftWithinTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_codedTermZeroShiftWithinTermAt_iff M
        (scons M (raw_zero M) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons]. intros _.
      exact (raw_codedTermZeroShiftBelow_zero M hPA
        cutoff supportCode supportStep).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedTermZeroShiftWithinTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_codedTermZeroShiftWithinTermAt_iff M
        (scons M (raw_succ M current) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      intro hsuccBound.
      assert (hcurrentBound : rawLt M current limit).
      { exact (raw_rank_lt_of_succ_le M hPA current limit hsuccBound). }
      apply (raw_codedTermZeroShiftBelow_succ M hPA
        cutoff limit supportCode supportStep current
        hsyntax hcurrentBound).
      apply hcurrent.
      exact (raw_lt_to_le M current limit hcurrentBound).
  }
  intro current. unfold phi in hall.
  pose proof (proj1 (raw_sat_codedTermZeroShiftWithinTermAt_iff M
    (scons M current parameterEnv)
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0))
    (hall current)) as hcurrent.
  unfold parameterEnv in hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

Theorem raw_codedTermZeroShift_identity_of_syntax_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      input assignmentCode assignmentStep,
  RawTermSyntaxRealizable M input assignmentCode assignmentStep ->
  forall cutoff,
    RawCodedTermShift M cutoff (raw_zero M) input input.
Proof.
  intros M hPA input assignmentCode assignmentStep
    (supportCode & supportStep & hsyntax & _ & hrootSupported) cutoff.
  pose proof (raw_codedTermZeroShiftWithin_all M hPA
    cutoff (raw_succ M input) supportCode supportStep
    hsyntax (raw_succ M input)) as hall.
  specialize (hall (raw_rank_le_refl M hPA (raw_succ M input))).
  exact (hall input
    (raw_assignment_lt_self_succ M hPA input) hrootSupported).
Qed.

(** ------------------------------------------------------------------
    Identity formula shifts and constructor closure of atomic adequacy. *)

Lemma raw_codedFormulaEq_zeroShift_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff left right assignmentCode assignmentStep,
  RawTermSyntaxRealizable M left assignmentCode assignmentStep ->
  RawTermSyntaxRealizable M right assignmentCode assignmentStep ->
  RawCodedFormulaShift M cutoff (raw_zero M)
    (rawFormulaEqCode M left right) (rawFormulaEqCode M left right).
Proof.
  intros M hPA cutoff left right assignmentCode assignmentStep
    hleft hright.
  pose proof (raw_codedTermZeroShift_identity_of_syntax_realizable
    M hPA left assignmentCode assignmentStep hleft cutoff) as hleftShift.
  pose proof (raw_codedTermZeroShift_identity_of_syntax_realizable
    M hPA right assignmentCode assignmentStep hright cutoff) as hrightShift.
  pose proof (raw_codedFormulaShift_of_valid_tree M hPA (raw_zero M)
    (RFSTEq M cutoff left left right right)) as htree.
  cbn [rawFormulaShiftTreeDepth rawFormulaShiftTreeSource
    rawFormulaShiftTreeTarget RawFormulaShiftTreeValid] in htree.
  exact (htree (conj hleftShift hrightShift)).
Qed.

Lemma raw_codedFormulaBot_zeroShift_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff,
  RawCodedFormulaShift M cutoff (raw_zero M)
    (rawFormulaBotCode M) (rawFormulaBotCode M).
Proof.
  intros M hPA cutoff.
  pose proof (raw_codedFormulaShift_of_valid_tree M hPA (raw_zero M)
    (RFSTBot M cutoff)) as htree.
  cbn [rawFormulaShiftTreeDepth rawFormulaShiftTreeSource
    rawFormulaShiftTreeTarget RawFormulaShiftTreeValid] in htree.
  exact (htree I).
Qed.

Definition RawCodedFormulaZeroShiftBelow (M : RawPAModel)
    (current : M) : Prop :=
  forall input : M,
    rawLt M input current ->
    RawCodedFormulaAtomicallyAdequate M input ->
    forall cutoff : M,
      RawCodedFormulaShift M cutoff (raw_zero M) input input.

Arguments RawCodedFormulaZeroShiftBelow M current : clear implicits.

Definition codedFormulaZeroShiftBelowTermAt (current : term) : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 current))
      (pImp
        (codedFormulaAtomicallyAdequateTermAt (tVar 0))
        (pAll
          (codedFormulaShiftTermAt
            (tVar 0) tZero (tVar 1) (tVar 1))))).

Lemma raw_sat_codedFormulaZeroShiftBelowTermAt_iff : forall
    (M : RawPAModel) e current,
  raw_formula_sat M e (codedFormulaZeroShiftBelowTermAt current) <->
  RawCodedFormulaZeroShiftBelow M (raw_term_eval M e current).
Proof.
  intros. unfold codedFormulaZeroShiftBelowTermAt,
    RawCodedFormulaZeroShiftBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaShiftTermAt_iff.
  repeat setoid_rewrite raw_shiftTotality_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_codedFormulaZeroShiftBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaZeroShiftBelow M (raw_zero M).
Proof.
  intros M hPA input hinput _ cutoff.
  exfalso. exact (raw_not_lt_zero M hPA input hinput).
Qed.

Lemma raw_codedFormulaZeroShiftBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedFormulaZeroShiftBelow M current ->
  RawCodedFormulaZeroShiftBelow M (raw_succ M current).
Proof.
  intros M hPA current hprefix input hinput hadequate cutoff.
  destruct (raw_lt_succ_cases M hPA input current hinput)
    as [hbefore | ->].
  - exact (hprefix input hbefore hadequate cutoff).
  - destruct hadequate as
      (formulaCode & formulaStep & bound & rootIndex & hsyntax & hatomic).
    pose proof hsyntax as hsyntaxFull.
    destruct hsyntax as
      [hdefined [hrootBelow [hrootLookup hsyntaxRows]]].
    pose proof (hsyntaxRows rootIndex current hrootBelow hrootLookup)
      as hrootRow.
    destruct (raw_codedFormulaSyntaxTraversalRow_shape M
      formulaCode formulaStep rootIndex current hrootRow)
      as (shape & hcode & hshape).
    destruct shape as
      [sourceLeft sourceRight
      |
      | sourceLeft sourceRight
      | sourceLeft sourceRight
      | sourceLeft sourceRight
      | sourceChild
      | sourceChild].
    + cbn [rawCodedFormulaShapeCode] in hcode. subst current.
      destruct (hatomic rootIndex
        (rawFormulaEqCode M sourceLeft sourceRight)
        sourceLeft sourceRight (raw_zero M) (raw_zero M)
        hrootBelow hrootLookup eq_refl
        (raw_codedZeroAssignment_defined_all M hPA
          (rawFormulaEqCode M sourceLeft sourceRight)))
        as [hleftSyntax hrightSyntax].
      exact (raw_codedFormulaEq_zeroShift_identity M hPA
        cutoff sourceLeft sourceRight (raw_zero M) (raw_zero M)
        hleftSyntax hrightSyntax).
    + cbn [rawCodedFormulaShapeCode] in hcode. subst current.
      exact (raw_codedFormulaBot_zeroShift_identity M hPA cutoff).
    + cbn [rawCodedFormulaShapeCode] in hcode. subst current.
      destruct hshape as
        (leftIndex & rightIndex & hleftIndex & hleftLookup &
         hrightIndex & hrightLookup).
      assert (hleftBound : rawLt M leftIndex bound).
      { exact (raw_assignment_lt_trans M hPA leftIndex rootIndex bound
          hleftIndex hrootBelow). }
      assert (hrightBound : rawLt M rightIndex bound).
      { exact (raw_assignment_lt_trans M hPA rightIndex rootIndex bound
          hrightIndex hrootBelow). }
      pose proof (raw_codedFormulaAtomicallyAdequate_at_lookup M
        formulaCode formulaStep bound rootIndex
        (rawFormulaImpCode M sourceLeft sourceRight)
        hsyntaxFull hatomic leftIndex sourceLeft
        hleftBound hleftLookup) as hleftAdequate.
      pose proof (raw_codedFormulaAtomicallyAdequate_at_lookup M
        formulaCode formulaStep bound rootIndex
        (rawFormulaImpCode M sourceLeft sourceRight)
        hsyntaxFull hatomic rightIndex sourceRight
        hrightBound hrightLookup) as hrightAdequate.
      apply (raw_codedFormulaShift_binary_composition M hPA
        RFSBImp cutoff (raw_zero M)
        sourceLeft sourceLeft sourceRight sourceRight).
      * exact (hprefix sourceLeft
          (raw_formulaCodeList3_left_lt M hPA
            (rawNumeralValue M 2) sourceLeft sourceRight)
          hleftAdequate cutoff).
      * exact (hprefix sourceRight
          (raw_formulaCodeList3_right_lt M hPA
            (rawNumeralValue M 2) sourceLeft sourceRight)
          hrightAdequate cutoff).
    + cbn [rawCodedFormulaShapeCode] in hcode. subst current.
      destruct hshape as
        (leftIndex & rightIndex & hleftIndex & hleftLookup &
         hrightIndex & hrightLookup).
      assert (hleftBound : rawLt M leftIndex bound).
      { exact (raw_assignment_lt_trans M hPA leftIndex rootIndex bound
          hleftIndex hrootBelow). }
      assert (hrightBound : rawLt M rightIndex bound).
      { exact (raw_assignment_lt_trans M hPA rightIndex rootIndex bound
          hrightIndex hrootBelow). }
      pose proof (raw_codedFormulaAtomicallyAdequate_at_lookup M
        formulaCode formulaStep bound rootIndex
        (rawFormulaAndCode M sourceLeft sourceRight)
        hsyntaxFull hatomic leftIndex sourceLeft
        hleftBound hleftLookup) as hleftAdequate.
      pose proof (raw_codedFormulaAtomicallyAdequate_at_lookup M
        formulaCode formulaStep bound rootIndex
        (rawFormulaAndCode M sourceLeft sourceRight)
        hsyntaxFull hatomic rightIndex sourceRight
        hrightBound hrightLookup) as hrightAdequate.
      apply (raw_codedFormulaShift_binary_composition M hPA
        RFSBAnd cutoff (raw_zero M)
        sourceLeft sourceLeft sourceRight sourceRight).
      * exact (hprefix sourceLeft
          (raw_formulaCodeList3_left_lt M hPA
            (rawNumeralValue M 3) sourceLeft sourceRight)
          hleftAdequate cutoff).
      * exact (hprefix sourceRight
          (raw_formulaCodeList3_right_lt M hPA
            (rawNumeralValue M 3) sourceLeft sourceRight)
          hrightAdequate cutoff).
    + cbn [rawCodedFormulaShapeCode] in hcode. subst current.
      destruct hshape as
        (leftIndex & rightIndex & hleftIndex & hleftLookup &
         hrightIndex & hrightLookup).
      assert (hleftBound : rawLt M leftIndex bound).
      { exact (raw_assignment_lt_trans M hPA leftIndex rootIndex bound
          hleftIndex hrootBelow). }
      assert (hrightBound : rawLt M rightIndex bound).
      { exact (raw_assignment_lt_trans M hPA rightIndex rootIndex bound
          hrightIndex hrootBelow). }
      pose proof (raw_codedFormulaAtomicallyAdequate_at_lookup M
        formulaCode formulaStep bound rootIndex
        (rawFormulaOrCode M sourceLeft sourceRight)
        hsyntaxFull hatomic leftIndex sourceLeft
        hleftBound hleftLookup) as hleftAdequate.
      pose proof (raw_codedFormulaAtomicallyAdequate_at_lookup M
        formulaCode formulaStep bound rootIndex
        (rawFormulaOrCode M sourceLeft sourceRight)
        hsyntaxFull hatomic rightIndex sourceRight
        hrightBound hrightLookup) as hrightAdequate.
      apply (raw_codedFormulaShift_binary_composition M hPA
        RFSBOr cutoff (raw_zero M)
        sourceLeft sourceLeft sourceRight sourceRight).
      * exact (hprefix sourceLeft
          (raw_formulaCodeList3_left_lt M hPA
            (rawNumeralValue M 4) sourceLeft sourceRight)
          hleftAdequate cutoff).
      * exact (hprefix sourceRight
          (raw_formulaCodeList3_right_lt M hPA
            (rawNumeralValue M 4) sourceLeft sourceRight)
          hrightAdequate cutoff).
    + cbn [rawCodedFormulaShapeCode] in hcode. subst current.
      destruct hshape as [childIndex [hchildIndex hchildLookup]].
      assert (hchildBound : rawLt M childIndex bound).
      { exact (raw_assignment_lt_trans M hPA childIndex rootIndex bound
          hchildIndex hrootBelow). }
      pose proof (raw_codedFormulaAtomicallyAdequate_at_lookup M
        formulaCode formulaStep bound rootIndex
        (rawFormulaAllCode M sourceChild)
        hsyntaxFull hatomic childIndex sourceChild
        hchildBound hchildLookup) as hchildAdequate.
      apply (raw_codedFormulaShift_unary_composition M hPA
        RFSUAll cutoff (raw_zero M) sourceChild sourceChild).
      exact (hprefix sourceChild
        (raw_formulaCodeList2_child_lt M hPA
          (rawNumeralValue M 5) sourceChild)
        hchildAdequate (raw_succ M cutoff)).
    + cbn [rawCodedFormulaShapeCode] in hcode. subst current.
      destruct hshape as [childIndex [hchildIndex hchildLookup]].
      assert (hchildBound : rawLt M childIndex bound).
      { exact (raw_assignment_lt_trans M hPA childIndex rootIndex bound
          hchildIndex hrootBelow). }
      pose proof (raw_codedFormulaAtomicallyAdequate_at_lookup M
        formulaCode formulaStep bound rootIndex
        (rawFormulaExCode M sourceChild)
        hsyntaxFull hatomic childIndex sourceChild
        hchildBound hchildLookup) as hchildAdequate.
      apply (raw_codedFormulaShift_unary_composition M hPA
        RFSUEx cutoff (raw_zero M) sourceChild sourceChild).
      exact (hprefix sourceChild
        (raw_formulaCodeList2_child_lt M hPA
          (rawNumeralValue M 6) sourceChild)
        hchildAdequate (raw_succ M cutoff)).
Qed.

Theorem raw_codedFormulaZeroShiftBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedFormulaZeroShiftBelow M current.
Proof.
  intros M hPA.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := codedFormulaZeroShiftBelowTermAt (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_codedFormulaZeroShiftBelowTermAt_iff M
        (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_codedFormulaZeroShiftBelow_zero M hPA).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedFormulaZeroShiftBelowTermAt_iff M
          (scons M current parameterEnv) (tVar 0)) hcurrentSat)
        as hcurrent.
      apply (proj2 (raw_sat_codedFormulaZeroShiftBelowTermAt_iff M
        (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_codedFormulaZeroShiftBelow_succ M hPA
        current hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1 (raw_sat_codedFormulaZeroShiftBelowTermAt_iff M
    (scons M current parameterEnv) (tVar 0)) (hall current)) as hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

Theorem raw_codedFormula_zeroShift_identity : forall
    (M : RawPAModel), RawPASatisfies M -> forall input,
  RawCodedFormulaAtomicallyAdequate M input ->
  forall cutoff,
    RawCodedFormulaShift M cutoff (raw_zero M) input input.
Proof.
  intros M hPA input hadequate cutoff.
  pose proof (raw_codedFormulaZeroShiftBelow_all M hPA
    (raw_succ M input)) as hall.
  exact (hall input (raw_assignment_lt_self_succ M hPA input)
    hadequate cutoff).
Qed.

Lemma raw_formulaImpCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  RawCodedFormulaAtomicallyAdequate M left ->
  RawCodedFormulaAtomicallyAdequate M right ->
  RawCodedFormulaAtomicallyAdequate M
    (rawFormulaImpCode M left right).
Proof.
  intros M hPA left right hleft hright.
  apply (raw_codedFormulaShift_target_atomically_adequate M hPA
    (raw_zero M) (raw_zero M)
    (rawFormulaImpCode M left right) (rawFormulaImpCode M left right)).
  apply (raw_codedFormulaShift_binary_composition M hPA
    RFSBImp (raw_zero M) (raw_zero M) left left right right).
  - exact (raw_codedFormula_zeroShift_identity M hPA left hleft
      (raw_zero M)).
  - exact (raw_codedFormula_zeroShift_identity M hPA right hright
      (raw_zero M)).
Qed.

Lemma raw_formulaAndCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  RawCodedFormulaAtomicallyAdequate M left ->
  RawCodedFormulaAtomicallyAdequate M right ->
  RawCodedFormulaAtomicallyAdequate M
    (rawFormulaAndCode M left right).
Proof.
  intros M hPA left right hleft hright.
  apply (raw_codedFormulaShift_target_atomically_adequate M hPA
    (raw_zero M) (raw_zero M)
    (rawFormulaAndCode M left right) (rawFormulaAndCode M left right)).
  apply (raw_codedFormulaShift_binary_composition M hPA
    RFSBAnd (raw_zero M) (raw_zero M) left left right right).
  - exact (raw_codedFormula_zeroShift_identity M hPA left hleft
      (raw_zero M)).
  - exact (raw_codedFormula_zeroShift_identity M hPA right hright
      (raw_zero M)).
Qed.

Lemma raw_formulaOrCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  RawCodedFormulaAtomicallyAdequate M left ->
  RawCodedFormulaAtomicallyAdequate M right ->
  RawCodedFormulaAtomicallyAdequate M
    (rawFormulaOrCode M left right).
Proof.
  intros M hPA left right hleft hright.
  apply (raw_codedFormulaShift_target_atomically_adequate M hPA
    (raw_zero M) (raw_zero M)
    (rawFormulaOrCode M left right) (rawFormulaOrCode M left right)).
  apply (raw_codedFormulaShift_binary_composition M hPA
    RFSBOr (raw_zero M) (raw_zero M) left left right right).
  - exact (raw_codedFormula_zeroShift_identity M hPA left hleft
      (raw_zero M)).
  - exact (raw_codedFormula_zeroShift_identity M hPA right hright
      (raw_zero M)).
Qed.

Lemma raw_formulaAllCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall child,
  RawCodedFormulaAtomicallyAdequate M child ->
  RawCodedFormulaAtomicallyAdequate M (rawFormulaAllCode M child).
Proof.
  intros M hPA child hchild.
  apply (raw_codedFormulaShift_target_atomically_adequate M hPA
    (raw_zero M) (raw_zero M)
    (rawFormulaAllCode M child) (rawFormulaAllCode M child)).
  apply (raw_codedFormulaShift_unary_composition M hPA
    RFSUAll (raw_zero M) (raw_zero M) child child).
  exact (raw_codedFormula_zeroShift_identity M hPA child hchild
    (raw_succ M (raw_zero M))).
Qed.

Lemma raw_formulaExCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall child,
  RawCodedFormulaAtomicallyAdequate M child ->
  RawCodedFormulaAtomicallyAdequate M (rawFormulaExCode M child).
Proof.
  intros M hPA child hchild.
  apply (raw_codedFormulaShift_target_atomically_adequate M hPA
    (raw_zero M) (raw_zero M)
    (rawFormulaExCode M child) (rawFormulaExCode M child)).
  apply (raw_codedFormulaShift_unary_composition M hPA
    RFSUEx (raw_zero M) (raw_zero M) child child).
  exact (raw_codedFormula_zeroShift_identity M hPA child hchild
    (raw_succ M (raw_zero M))).
Qed.

(** ------------------------------------------------------------------
    The four represented component operations. *)

Lemma raw_numeralTermCode_syntax_realizable_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall bound numeralCode,
  RawNumeralTermCodeAt M bound numeralCode ->
  RawTermSyntaxRealizable M numeralCode (raw_zero M) (raw_zero M).
Proof.
  intros M hPA bound numeralCode hnumeral.
  apply (raw_codedTermShift_target_syntax_realizable M hPA
    (raw_zero M) (raw_zero M) numeralCode numeralCode
    (raw_zero M) (raw_zero M) (raw_succ M numeralCode)).
  - exact (raw_codedTermShift_numeral_identity M hPA
      bound numeralCode (raw_zero M) (raw_zero M) hnumeral).
  - exact (raw_assignment_lt_self_succ M hPA numeralCode).
  - exact (raw_codedZeroAssignment_defined_all M hPA
      (raw_succ M numeralCode)).
Qed.

Lemma raw_fixedFormulaNumeral_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall phi,
  RawCodedFormulaAtomicallyAdequate M
    (rawNumeralValue M (formulaCode phi)).
Proof.
  intros M hPA phi.
  rewrite <- (rawQuotedFormulaCode_standard M hPA phi).
  exact (raw_quotedFormula_atomically_adequate M hPA phi).
Qed.

Lemma raw_dynamicTruthSigmaDomain_exists_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerLevel upperNumeral,
  RawNumeralTermCodeAt M (raw_succ M lowerLevel) upperNumeral ->
  exists domain,
    RawCodedFormulaSingleSubstitution M upperNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthSigmaRowDomainTemplate)) domain /\
    RawCodedFormulaAtomicallyAdequate M domain.
Proof.
  intros M hPA lowerLevel upperNumeral hnumeral.
  exact (raw_codedFormulaSingleSubstitution_exists_atomically_adequate
    M hPA (raw_codedTermOpening_total M hPA)
    (raw_codedTermOpeningAfterShiftSyntaxStable_of_PA M hPA)
    (rawNumeralValue M (formulaCode dynamicTruthSigmaRowDomainTemplate))
    (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthSigmaRowDomainTemplate)
    upperNumeral (raw_zero M) (raw_zero M)
    (raw_numeralTermCode_syntax_realizable_zero M hPA
      (raw_succ M lowerLevel) upperNumeral hnumeral)).
Qed.

Lemma raw_dynamicTruthPiDomain_exists_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerLevel successorNumeral,
  RawNumeralTermCodeAt M (raw_succ M lowerLevel) successorNumeral ->
  exists domain,
    RawCodedFormulaSingleSubstitution M successorNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthPiRowDomainTemplate)) domain /\
    RawCodedFormulaAtomicallyAdequate M domain.
Proof.
  intros M hPA lowerLevel successorNumeral hnumeral.
  exact (raw_codedFormulaSingleSubstitution_exists_atomically_adequate
    M hPA (raw_codedTermOpening_total M hPA)
    (raw_codedTermOpeningAfterShiftSyntaxStable_of_PA M hPA)
    (rawNumeralValue M (formulaCode dynamicTruthPiRowDomainTemplate))
    (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthPiRowDomainTemplate)
    successorNumeral (raw_zero M) (raw_zero M)
    (raw_numeralTermCode_syntax_realizable_zero M hPA
      (raw_succ M lowerLevel) successorNumeral hnumeral)).
Qed.

Lemma raw_dynamicTruthSigmaLower_exists_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall previousPi,
  RawCodedFormulaAtomicallyAdequate M previousPi ->
  exists lowerApplication,
    RawDynamicTruthCoqLowerApplication M previousPi lowerApplication /\
    RawCodedFormulaAtomicallyAdequate M lowerApplication.
Proof.
  intros M hPA previousPi hprevious.
  destruct (raw_codedFormulaSingleSubstitution_three_exists_total M hPA
    previousPi hprevious
    (rawNumeralValue M
      (termCode dynamicTruthCoqLowerFirstReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      dynamicTruthCoqLowerFirstReplacement)
    (rawNumeralValue M
      (termCode dynamicTruthCoqLowerSecondReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      dynamicTruthCoqLowerSecondReplacement)
    (rawNumeralValue M
      (termCode dynamicTruthCoqLowerThirdReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      dynamicTruthCoqLowerThirdReplacement)) as
    (first & second & output & hfirst & _ & hsecond & _ & hthird & houtput).
  exists output. split.
  - exists first, second. repeat split; assumption.
  - exact houtput.
Qed.

Lemma raw_dynamicTruthPiLower_exists_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall previousSigma,
  RawCodedFormulaAtomicallyAdequate M previousSigma ->
  exists lowerApplication,
    RawDynamicTruthPiCoqLowerApplication M previousSigma lowerApplication /\
    RawCodedFormulaAtomicallyAdequate M lowerApplication.
Proof.
  intros M hPA previousSigma hprevious.
  destruct (raw_codedFormulaSingleSubstitution_three_exists_total M hPA
    previousSigma hprevious
    (rawNumeralValue M
      (termCode dynamicTruthPiCoqLowerFirstReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      dynamicTruthPiCoqLowerFirstReplacement)
    (rawNumeralValue M
      (termCode dynamicTruthPiCoqLowerSecondReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      dynamicTruthPiCoqLowerSecondReplacement)
    (rawNumeralValue M
      (termCode dynamicTruthPiCoqLowerThirdReplacement))
    (raw_zero M) (raw_zero M)
    (raw_dynamicTruthApplication_fixedReplacement_syntax M hPA
      dynamicTruthPiCoqLowerThirdReplacement)) as
    (first & second & output & hfirst & _ & hsecond & _ & hthird & houtput).
  exists output. split.
  - exists first, second. repeat split; assumption.
  - exact houtput.
Qed.

(** ------------------------------------------------------------------
    Atomic adequacy of the two transparent row constructors. *)

Lemma raw_formulaBotCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaAtomicallyAdequate M (rawFormulaBotCode M).
Proof.
  intros M hPA.
  change (RawCodedFormulaAtomicallyAdequate M
    (rawQuotedFormulaCode M pBot)).
  exact (raw_quotedFormula_atomically_adequate M hPA pBot).
Qed.

Lemma rawDynamicTruthSigmaNoBinderCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  RawCodedFormulaAtomicallyAdequate M lowerApplication ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthSigmaNoBinderCode M lowerApplication).
Proof.
  intros M hPA lowerApplication hlower.
  unfold rawDynamicTruthSigmaNoBinderCode, rawFormulaEx3Code.
  apply raw_formulaImpCode_atomically_adequate; [exact hPA | |].
  - repeat apply raw_formulaExCode_atomically_adequate; try exact hPA.
    apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
    + exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
        dynamicTruthSigmaRowBinderPrependFormula).
    + exact hlower.
  - exact (raw_formulaBotCode_atomically_adequate M hPA).
Qed.

Lemma rawDynamicTruthSigmaBranchesCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  RawCodedFormulaAtomicallyAdequate M lowerApplication ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthSigmaBranchesCode M lowerApplication).
Proof.
  intros M hPA lowerApplication hlower.
  unfold rawDynamicTruthSigmaBranchesCode,
    rawDynamicTruthSigmaUniversalCode.
  repeat apply raw_formulaOrCode_atomically_adequate; try exact hPA;
    try apply raw_fixedFormulaNumeral_atomically_adequate; try exact hPA.
  apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
  - exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthSigmaRowUniversalPrefixFormula).
  - exact (rawDynamicTruthSigmaNoBinderCode_atomically_adequate
      M hPA lowerApplication hlower).
Qed.

Theorem rawDynamicTruthSigmaSuccessorRowCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall domain lowerApplication,
  RawCodedFormulaAtomicallyAdequate M domain ->
  RawCodedFormulaAtomicallyAdequate M lowerApplication ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthSigmaSuccessorRowCode M domain lowerApplication).
Proof.
  intros M hPA domain lowerApplication hdomain hlower.
  unfold rawDynamicTruthSigmaSuccessorRowCode, rawFormulaEx8Code.
  repeat apply raw_formulaExCode_atomically_adequate; try exact hPA.
  apply raw_formulaAndCode_atomically_adequate; [exact hPA | exact hdomain |].
  exact (rawDynamicTruthSigmaBranchesCode_atomically_adequate
    M hPA lowerApplication hlower).
Qed.

Lemma rawDynamicTruthPiNoBinderCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  RawCodedFormulaAtomicallyAdequate M lowerApplication ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthPiNoBinderCode M lowerApplication).
Proof.
  intros M hPA lowerApplication hlower.
  unfold rawDynamicTruthPiNoBinderCode,
    rawDynamicTruthPiFormulaEx3Code.
  apply raw_formulaImpCode_atomically_adequate; [exact hPA | |].
  - repeat apply raw_formulaExCode_atomically_adequate; try exact hPA.
    apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
    + exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
        dynamicTruthPiRowBinderPrependFormula).
    + exact hlower.
  - exact (raw_formulaBotCode_atomically_adequate M hPA).
Qed.

Lemma rawDynamicTruthPiBranchesCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall lowerApplication,
  RawCodedFormulaAtomicallyAdequate M lowerApplication ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthPiBranchesCode M lowerApplication).
Proof.
  intros M hPA lowerApplication hlower.
  unfold rawDynamicTruthPiBranchesCode,
    rawDynamicTruthPiExistentialCode.
  repeat apply raw_formulaOrCode_atomically_adequate; try exact hPA;
    try apply raw_fixedFormulaNumeral_atomically_adequate; try exact hPA.
  apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
  - exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      dynamicTruthPiRowExistentialPrefixFormula).
  - exact (rawDynamicTruthPiNoBinderCode_atomically_adequate
      M hPA lowerApplication hlower).
Qed.

Theorem rawDynamicTruthPiSuccessorRowCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall domain lowerApplication,
  RawCodedFormulaAtomicallyAdequate M domain ->
  RawCodedFormulaAtomicallyAdequate M lowerApplication ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthPiSuccessorRowCode M domain lowerApplication).
Proof.
  intros M hPA domain lowerApplication hdomain hlower.
  unfold rawDynamicTruthPiSuccessorRowCode,
    rawDynamicTruthPiFormulaEx8Code.
  repeat apply raw_formulaExCode_atomically_adequate; try exact hPA.
  apply raw_formulaAndCode_atomically_adequate; [exact hPA | exact hdomain |].
  exact (rawDynamicTruthPiBranchesCode_atomically_adequate
    M hPA lowerApplication hlower).
Qed.

(** The paired successor interface now has no remaining conditional
    operation premise.  The same represented successor numeral may witness
    both polarities, while their domain substitutions and lower applications
    retain separate checked traces. *)
Theorem dynamicTruthPairedSuccessorRowGraph_raw_adequate_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCarrierIndexedPairedAdequateCodeOrbitSuccessorTotal M
    dynamicTruthPairedSuccessorRowGraph.
Proof.
  intros M hPA tail lowerLevel previousSigma previousPi
    hpreviousSigma hpreviousPi.
  destruct (raw_numeralTermCodeExists_all M hPA
    (raw_succ M lowerLevel)) as [successorNumeral hnumeral].
  destruct (raw_dynamicTruthSigmaDomain_exists_adequate M hPA
    lowerLevel successorNumeral hnumeral)
    as (sigmaDomain & hsigmaDomain & hsigmaDomainAdequate).
  destruct (raw_dynamicTruthPiDomain_exists_adequate M hPA
    lowerLevel successorNumeral hnumeral)
    as (piDomain & hpiDomain & hpiDomainAdequate).
  destruct (raw_dynamicTruthSigmaLower_exists_adequate M hPA
    previousPi hpreviousPi)
    as (sigmaLower & hsigmaLower & hsigmaLowerAdequate).
  destruct (raw_dynamicTruthPiLower_exists_adequate M hPA
    previousSigma hpreviousSigma)
    as (piLower & hpiLower & hpiLowerAdequate).
  exists (rawDynamicTruthSigmaSuccessorRowCode M sigmaDomain sigmaLower),
    (rawDynamicTruthPiSuccessorRowCode M piDomain piLower).
  split.
  - apply (proj2
      (raw_sat_dynamicTruthPairedSuccessorRowGraph_iff M tail lowerLevel
        previousSigma previousPi
        (rawDynamicTruthSigmaSuccessorRowCode M sigmaDomain sigmaLower)
        (rawDynamicTruthPiSuccessorRowCode M piDomain piLower))).
    split.
    + exists successorNumeral, sigmaDomain, sigmaLower.
      repeat split; try assumption; reflexivity.
    + exists successorNumeral, piDomain, piLower.
      repeat split; try assumption; reflexivity.
  - split.
    + exact (rawDynamicTruthSigmaSuccessorRowCode_atomically_adequate
        M hPA sigmaDomain sigmaLower
        hsigmaDomainAdequate hsigmaLowerAdequate).
    + exact (rawDynamicTruthPiSuccessorRowCode_atomically_adequate
        M hPA piDomain piLower
        hpiDomainAdequate hpiLowerAdequate).
Qed.

End PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
