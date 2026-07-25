(**
  Definable totality infrastructure for raw formula shifting.

  Formula-shift preservation alone does not produce an output code.  The
  input may be a genuinely nonstandard carrier element, so neither terms nor
  formulae may be decoded in Rocq.  This file starts from the represented
  syntax certificates and performs strong prefix inductions inside PA.

  The first half closes the atomic gap completely: every term with a
  [RawTermSyntaxRealizable] certificate has a raw shift output at every
  cutoff and amount.  The second half packages the analogous represented
  induction for atomically adequate formulae.  Its only remaining premise is
  explicit constructor composition for already realized binary and unary
  formula shifts; equality and bottom leaves are discharged here.
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFOrdinalCodeTotalInduction.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity
  RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedAssignmentTotality RawCodedTermEvaluationTraversal
  RawCodedTermEvaluationRealization RawCodedProofDescent
  RawCodedFormulaRankStep RawCodedFormulaRankTraversal
  RawCodedFormulaRankTotality RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedPAAxiomContextSelfShift RawCodedFormulaShiftTreeRealization.

Import ListNotations.

Module PABoundedRawCodedFormulaShiftTotality.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedFormulaShiftTreeRealization.

(** ------------------------------------------------------------------
    Structural term-shift constructors with genuinely changed targets. *)

(** Variable shifting is total because PA linearly orders the variable index
    and cutoff.  The output is either the original variable or the variable
    whose index is increased by [amount]. *)
Lemma raw_codedTermShift_variable_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount index,
  exists output,
    RawCodedTermShift M cutoff amount (rawTermVarCode M index) output.
Proof.
  intros M hPA cutoff amount index.
  destruct (raw_le_or_gt M hPA cutoff index) as [hhigh | hlow].
  - set (output := rawTermVarCode M (raw_add M index amount)).
    assert (hrow : RawCodedTermShiftTraversalRow M cutoff amount
        (raw_zero M) (raw_zero M) (raw_zero M) (raw_zero M)
        (raw_zero M) (rawTermVarCode M index) output).
    {
      left. exists index, (raw_add M index amount).
      split; [reflexivity |]. split; [reflexivity |].
      right. split; [exact hhigh | reflexivity].
    }
    destruct (raw_termShiftTraversalBundle_append M hPA
      cutoff amount (raw_zero M) (raw_zero M)
      (raw_zero M) (raw_zero M) (raw_zero M)
      (rawTermVarCode M index) output
      (raw_termShiftTraversalBundle_empty M hPA cutoff amount) hrow)
      as (sourceCode & sourceStep & targetCode & targetStep &
          hbundle & _ & hroot).
    exists output, sourceCode, sourceStep, targetCode, targetStep,
      (raw_succ M (raw_zero M)), (raw_zero M).
    destruct hbundle as [hsource [htarget [hrows hnonnegative]]].
    exact (conj hsource
      (conj htarget
        (conj (raw_assignment_lt_self_succ M hPA (raw_zero M))
          (conj hroot (conj hrows hnonnegative))))).
  - exists (rawTermVarCode M index).
    exact (raw_codedTermShift_variable_identity M hPA
      cutoff amount index hlow).
Qed.

(** These constructors concatenate the already certified child traces and
    append one parent row.  Thus they remain valid when the child traces and
    their bounds are nonstandard. *)
Lemma raw_codedTermShift_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount inputChild outputChild,
  RawCodedTermShift M cutoff amount inputChild outputChild ->
  RawCodedTermShift M cutoff amount
    (rawTermSuccCode M inputChild) (rawTermSuccCode M outputChild).
Proof.
  intros M hPA cutoff amount inputChild outputChild
    (sourceCode & sourceStep & targetCode & targetStep & bound &
     rootIndex & htrace).
  destruct htrace as
    [hsource [htarget [hrootBelow [hroot [hrows hnonnegative]]]]].
  assert (hbundle : RawTermShiftTraversalBundle M cutoff amount
      sourceCode sourceStep targetCode targetStep bound).
  { repeat split; assumption. }
  assert (hrow : RawCodedTermShiftTraversalRow M cutoff amount
      sourceCode sourceStep targetCode targetStep bound
      (rawTermSuccCode M inputChild) (rawTermSuccCode M outputChild)).
  {
    right. right. left.
    exists rootIndex, inputChild, outputChild.
    split; [exact hrootBelow |]. split; [exact hroot |].
    split; reflexivity.
  }
  destruct (raw_termShiftTraversalBundle_append M hPA
    cutoff amount sourceCode sourceStep targetCode targetStep bound
    (rawTermSuccCode M inputChild) (rawTermSuccCode M outputChild)
    hbundle hrow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        hnewBundle & _ & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    (raw_succ M bound), bound.
  destruct hnewBundle as
    [hnewSource [hnewTarget [hnewRows hnewNonnegative]]].
  exact (conj hnewSource
    (conj hnewTarget
      (conj (raw_assignment_lt_self_succ M hPA bound)
        (conj hnewRoot (conj hnewRows hnewNonnegative))))).
Qed.

Lemma raw_codedTermShift_add : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount inputLeft outputLeft inputRight outputRight,
  RawCodedTermShift M cutoff amount inputLeft outputLeft ->
  RawCodedTermShift M cutoff amount inputRight outputRight ->
  RawCodedTermShift M cutoff amount
    (rawTermAddCode M inputLeft inputRight)
    (rawTermAddCode M outputLeft outputRight).
Proof.
  intros M hPA cutoff amount inputLeft outputLeft inputRight outputRight
    (leftSourceCode & leftSourceStep & leftTargetCode & leftTargetStep &
     leftBound & leftRootIndex & hleft)
    (rightSourceCode & rightSourceStep & rightTargetCode & rightTargetStep &
     rightBound & rightRootIndex & hright).
  assert (hleftBelow : rawLt M leftRootIndex leftBound).
  { exact (proj1 (proj2 (proj2 hleft))). }
  destruct (raw_termShiftTraces_concatenate M hPA cutoff amount
    leftSourceCode leftSourceStep leftTargetCode leftTargetStep
    leftBound leftRootIndex inputLeft outputLeft
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightBound rightRootIndex inputRight outputRight hleft hright)
    as (sourceCode & sourceStep & targetCode & targetStep &
        hcombined & hleftRoot).
  destruct hcombined as
    [hsource [htarget [hrightBelow [hrightRoot [hrows hnonnegative]]]]].
  set (bound := raw_add M leftBound rightBound).
  assert (hbundle : RawTermShiftTraversalBundle M cutoff amount
      sourceCode sourceStep targetCode targetStep bound).
  { repeat split; assumption. }
  assert (hrow : RawCodedTermShiftTraversalRow M cutoff amount
      sourceCode sourceStep targetCode targetStep bound
      (rawTermAddCode M inputLeft inputRight)
      (rawTermAddCode M outputLeft outputRight)).
  {
    right. right. right. left.
    exists leftRootIndex, inputLeft, outputLeft,
      (raw_add M leftBound rightRootIndex), inputRight, outputRight.
    split.
    - exact (raw_lt_le_trans_pair M hPA leftRootIndex leftBound bound
        hleftBelow (raw_proof_left_le_sum M leftBound rightBound)).
    - split; [exact hleftRoot |]. split; [exact hrightBelow |].
      split; [exact hrightRoot |]. split; reflexivity.
  }
  destruct (raw_termShiftTraversalBundle_append M hPA
    cutoff amount sourceCode sourceStep targetCode targetStep bound
    (rawTermAddCode M inputLeft inputRight)
    (rawTermAddCode M outputLeft outputRight) hbundle hrow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        hnewBundle & _ & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    (raw_succ M bound), bound.
  destruct hnewBundle as
    [hnewSource [hnewTarget [hnewRows hnewNonnegative]]].
  exact (conj hnewSource
    (conj hnewTarget
      (conj (raw_assignment_lt_self_succ M hPA bound)
        (conj hnewRoot (conj hnewRows hnewNonnegative))))).
Qed.

Lemma raw_codedTermShift_mul : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount inputLeft outputLeft inputRight outputRight,
  RawCodedTermShift M cutoff amount inputLeft outputLeft ->
  RawCodedTermShift M cutoff amount inputRight outputRight ->
  RawCodedTermShift M cutoff amount
    (rawTermMulCode M inputLeft inputRight)
    (rawTermMulCode M outputLeft outputRight).
Proof.
  intros M hPA cutoff amount inputLeft outputLeft inputRight outputRight
    (leftSourceCode & leftSourceStep & leftTargetCode & leftTargetStep &
     leftBound & leftRootIndex & hleft)
    (rightSourceCode & rightSourceStep & rightTargetCode & rightTargetStep &
     rightBound & rightRootIndex & hright).
  assert (hleftBelow : rawLt M leftRootIndex leftBound).
  { exact (proj1 (proj2 (proj2 hleft))). }
  destruct (raw_termShiftTraces_concatenate M hPA cutoff amount
    leftSourceCode leftSourceStep leftTargetCode leftTargetStep
    leftBound leftRootIndex inputLeft outputLeft
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightBound rightRootIndex inputRight outputRight hleft hright)
    as (sourceCode & sourceStep & targetCode & targetStep &
        hcombined & hleftRoot).
  destruct hcombined as
    [hsource [htarget [hrightBelow [hrightRoot [hrows hnonnegative]]]]].
  set (bound := raw_add M leftBound rightBound).
  assert (hbundle : RawTermShiftTraversalBundle M cutoff amount
      sourceCode sourceStep targetCode targetStep bound).
  { repeat split; assumption. }
  assert (hrow : RawCodedTermShiftTraversalRow M cutoff amount
      sourceCode sourceStep targetCode targetStep bound
      (rawTermMulCode M inputLeft inputRight)
      (rawTermMulCode M outputLeft outputRight)).
  {
    right. right. right. right.
    exists leftRootIndex, inputLeft, outputLeft,
      (raw_add M leftBound rightRootIndex), inputRight, outputRight.
    split.
    - exact (raw_lt_le_trans_pair M hPA leftRootIndex leftBound bound
        hleftBelow (raw_proof_left_le_sum M leftBound rightBound)).
    - split; [exact hleftRoot |]. split; [exact hrightBelow |].
      split; [exact hrightRoot |]. split; reflexivity.
  }
  destruct (raw_termShiftTraversalBundle_append M hPA
    cutoff amount sourceCode sourceStep targetCode targetStep bound
    (rawTermMulCode M inputLeft inputRight)
    (rawTermMulCode M outputLeft outputRight) hbundle hrow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        hnewBundle & _ & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    (raw_succ M bound), bound.
  destruct hnewBundle as
    [hnewSource [hnewTarget [hnewRows hnewNonnegative]]].
  exact (conj hnewSource
    (conj hnewTarget
      (conj (raw_assignment_lt_self_succ M hPA bound)
        (conj hnewRoot (conj hnewRows hnewNonnegative))))).
Qed.

(** ------------------------------------------------------------------
    PA-definable strong induction for term-shift totality. *)

Definition RawCodedTermShiftTotalBelow (M : RawPAModel)
    (cutoff amount supportCode supportStep current : M) : Prop :=
  forall input : M,
    rawLt M input current ->
    rawTermCodeSupported M supportCode supportStep input ->
    exists output : M, RawCodedTermShift M cutoff amount input output.

Arguments RawCodedTermShiftTotalBelow M
  cutoff amount supportCode supportStep current : clear implicits.

Definition codedTermShiftTotalBelowTermAt
    (cutoff amount supportCode supportStep current : term) : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 current))
      (pImp
        (termCodeSupportedTermAt
          (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
        (pEx
          (codedTermShiftTermAt
            (liftTerm 2 cutoff) (liftTerm 2 amount)
            (tVar 1) (tVar 0))))).

Lemma raw_shiftTotality_eval_liftTerm_one : forall
    (M : RawPAModel) a (e : nat -> M) t,
  raw_term_eval M (scons M a e) (liftTerm 1 t) = raw_term_eval M e t.
Proof.
  intros M a e t. unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro index.
  replace (index + 1) with (S index) by lia. reflexivity.
Qed.

Lemma raw_shiftTotality_eval_liftTerm_two : forall
    (M : RawPAModel) a b (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M a b e t. unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro index.
  replace (index + 2) with (S (S index)) by lia. reflexivity.
Qed.

Lemma raw_sat_codedTermShiftTotalBelowTermAt_iff : forall
    (M : RawPAModel) e cutoff amount supportCode supportStep current,
  raw_formula_sat M e
    (codedTermShiftTotalBelowTermAt
      cutoff amount supportCode supportStep current) <->
  RawCodedTermShiftTotalBelow M
    (raw_term_eval M e cutoff) (raw_term_eval M e amount)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold codedTermShiftTotalBelowTermAt,
    RawCodedTermShiftTotalBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_termCodeSupportedTermAt_iff.
  setoid_rewrite raw_sat_codedTermShiftTermAt_iff.
  repeat setoid_rewrite raw_shiftTotality_eval_liftTerm_one.
  repeat setoid_rewrite raw_shiftTotality_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_codedTermShiftTotalBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount supportCode supportStep,
  RawCodedTermShiftTotalBelow M cutoff amount supportCode supportStep
    (raw_zero M).
Proof.
  intros M hPA cutoff amount supportCode supportStep input hinput _.
  exfalso. exact (raw_not_lt_zero M hPA input hinput).
Qed.

Lemma raw_codedTermShiftTotalBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount limit supportCode supportStep current,
  RawTermSyntaxTraversal M limit supportCode supportStep ->
  rawLt M current limit ->
  RawCodedTermShiftTotalBelow M cutoff amount
    supportCode supportStep current ->
  RawCodedTermShiftTotalBelow M cutoff amount
    supportCode supportStep (raw_succ M current).
Proof.
  intros M hPA cutoff amount limit supportCode supportStep current
    [_ hsyntaxRows] hcurrentBound hprefix input hinput hsupported.
  destruct (raw_lt_succ_cases M hPA input current hinput)
    as [hbefore | ->].
  - exact (hprefix input hbefore hsupported).
  - destruct (hsyntaxRows current hcurrentBound hsupported)
      as (left & right & hshape).
    destruct hshape as
      [hvar | [hzero | [hsucc | [hadd | hmul]]]].
    + subst current.
      exact (raw_codedTermShift_variable_exists M hPA
        cutoff amount left).
    + subst current.
      exists (rawTermZeroCode M).
      exact (raw_codedTermShift_zero_identity M hPA cutoff amount).
    + destruct hsucc as [hcode [hchildSupported hchild]].
      subst current.
      destruct (hprefix left hchild hchildSupported)
        as [outputChild houtputChild].
      exists (rawTermSuccCode M outputChild).
      exact (raw_codedTermShift_succ M hPA cutoff amount
        left outputChild houtputChild).
    + destruct hadd as
        [hcode [hleftSupported [hrightSupported [hleft hright]]]].
      subst current.
      destruct (hprefix left hleft hleftSupported)
        as [outputLeft houtputLeft].
      destruct (hprefix right hright hrightSupported)
        as [outputRight houtputRight].
      exists (rawTermAddCode M outputLeft outputRight).
      exact (raw_codedTermShift_add M hPA cutoff amount
        left outputLeft right outputRight houtputLeft houtputRight).
    + destruct hmul as
        [hcode [hleftSupported [hrightSupported [hleft hright]]]].
      subst current.
      destruct (hprefix left hleft hleftSupported)
        as [outputLeft houtputLeft].
      destruct (hprefix right hright hrightSupported)
        as [outputRight houtputRight].
      exists (rawTermMulCode M outputLeft outputRight).
      exact (raw_codedTermShift_mul M hPA cutoff amount
        left outputLeft right outputRight houtputLeft houtputRight).
Qed.

Definition RawCodedTermShiftTotalWithin (M : RawPAModel)
    (cutoff amount limit supportCode supportStep current : M) : Prop :=
  rawLe M current limit ->
  RawCodedTermShiftTotalBelow M cutoff amount
    supportCode supportStep current.

Arguments RawCodedTermShiftTotalWithin M
  cutoff amount limit supportCode supportStep current : clear implicits.

Definition codedTermShiftTotalWithinTermAt
    (cutoff amount limit supportCode supportStep current : term) : formula :=
  pImp
    (Formula.leTermAt current limit)
    (codedTermShiftTotalBelowTermAt
      cutoff amount supportCode supportStep current).

Lemma raw_sat_codedTermShiftTotalWithinTermAt_iff : forall
    (M : RawPAModel) e cutoff amount limit supportCode supportStep current,
  raw_formula_sat M e
    (codedTermShiftTotalWithinTermAt
      cutoff amount limit supportCode supportStep current) <->
  RawCodedTermShiftTotalWithin M
    (raw_term_eval M e cutoff) (raw_term_eval M e amount)
    (raw_term_eval M e limit)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold codedTermShiftTotalWithinTermAt,
    RawCodedTermShiftTotalWithin.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank,
    raw_sat_codedTermShiftTotalBelowTermAt_iff.
  reflexivity.
Qed.

Theorem raw_codedTermShiftTotalWithin_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount limit supportCode supportStep,
  RawTermSyntaxTraversal M limit supportCode supportStep ->
  forall current,
    RawCodedTermShiftTotalWithin M cutoff amount
      limit supportCode supportStep current.
Proof.
  intros M hPA cutoff amount limit supportCode supportStep hsyntax.
  set (parameterEnv := scons M cutoff
    (scons M amount (scons M limit
      (scons M supportCode (scons M supportStep
        (fun _ : nat => raw_zero M)))))).
  set (phi := codedTermShiftTotalWithinTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_codedTermShiftTotalWithinTermAt_iff M
        (scons M (raw_zero M) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons]. intros _.
      exact (raw_codedTermShiftTotalBelow_zero M hPA
        cutoff amount supportCode supportStep).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedTermShiftTotalWithinTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_codedTermShiftTotalWithinTermAt_iff M
        (scons M (raw_succ M current) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      intro hsuccBound.
      assert (hcurrentBound : rawLt M current limit).
      { exact (raw_rank_lt_of_succ_le M hPA current limit hsuccBound). }
      apply (raw_codedTermShiftTotalBelow_succ M hPA
        cutoff amount limit supportCode supportStep current
        hsyntax hcurrentBound).
      apply hcurrent.
      exact (raw_lt_to_le M current limit hcurrentBound).
  }
  intro current. unfold phi in hall.
  pose proof (proj1 (raw_sat_codedTermShiftTotalWithinTermAt_iff M
    (scons M current parameterEnv)
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))
    (hall current)) as hcurrent.
  unfold parameterEnv in hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

(** Public term theorem.  Assignment adequacy is part of the honest syntax
    domain but shifting itself only consumes the syntax-closure component. *)
Theorem raw_codedTermShift_exists_of_syntax_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      input assignmentCode assignmentStep,
  RawTermSyntaxRealizable M input assignmentCode assignmentStep ->
  forall cutoff amount,
    exists output, RawCodedTermShift M cutoff amount input output.
Proof.
  intros M hPA input assignmentCode assignmentStep
    (supportCode & supportStep & hsyntax & _ & hrootSupported)
    cutoff amount.
  pose proof (raw_codedTermShiftTotalWithin_all M hPA
    cutoff amount (raw_succ M input) supportCode supportStep
    hsyntax (raw_succ M input)) as hall.
  specialize (hall (raw_rank_le_refl M hPA (raw_succ M input))).
  exact (hall input
    (raw_assignment_lt_self_succ M hPA input) hrootSupported).
Qed.

(** ------------------------------------------------------------------
    Formula leaves and the exact remaining composition interface. *)

Lemma raw_codedFormulaShift_eq_exists_of_term_syntax : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount sourceLeft sourceRight assignmentCode assignmentStep,
  RawTermSyntaxRealizable M sourceLeft assignmentCode assignmentStep ->
  RawTermSyntaxRealizable M sourceRight assignmentCode assignmentStep ->
  exists target,
    RawCodedFormulaShift M cutoff amount
      (rawFormulaEqCode M sourceLeft sourceRight) target.
Proof.
  intros M hPA cutoff amount sourceLeft sourceRight
    assignmentCode assignmentStep hleftSyntax hrightSyntax.
  destruct (raw_codedTermShift_exists_of_syntax_realizable M hPA
    sourceLeft assignmentCode assignmentStep hleftSyntax cutoff amount)
    as [targetLeft hleftShift].
  destruct (raw_codedTermShift_exists_of_syntax_realizable M hPA
    sourceRight assignmentCode assignmentStep hrightSyntax cutoff amount)
    as [targetRight hrightShift].
  exists (rawFormulaEqCode M targetLeft targetRight).
  pose proof (raw_codedFormulaShift_of_valid_tree M hPA amount
    (RFSTEq M cutoff sourceLeft targetLeft sourceRight targetRight))
    as htree.
  cbn [rawFormulaShiftTreeDepth rawFormulaShiftTreeSource
    rawFormulaShiftTreeTarget RawFormulaShiftTreeValid] in htree.
  exact (htree (conj hleftShift hrightShift)).
Qed.

Lemma raw_codedFormulaShift_bot_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount,
  exists target,
    RawCodedFormulaShift M cutoff amount (rawFormulaBotCode M) target.
Proof.
  intros M hPA cutoff amount.
  exists (rawFormulaBotCode M).
  pose proof (raw_codedFormulaShift_of_valid_tree M hPA amount
    (RFSTBot M cutoff)) as htree.
  cbn [rawFormulaShiftTreeDepth rawFormulaShiftTreeSource
    rawFormulaShiftTreeTarget RawFormulaShiftTreeValid] in htree.
  exact (htree I).
Qed.

(** A formula-operation trace stores three synchronized beta columns.
    Combining independently realized children therefore requires a
    nonstandard-length copy/concatenation theorem, not merely constructor
    arithmetic.  These two clauses isolate exactly that reusable operation:
    binary children stay at the parent cutoff, while quantified children
    were shifted at its successor.  No existence or logical principle is
    hidden in this definition. *)
Definition RawCodedFormulaShiftCompositional (M : RawPAModel) : Prop :=
  (forall kind cutoff amount sourceLeft targetLeft sourceRight targetRight,
    RawCodedFormulaShift M cutoff amount sourceLeft targetLeft ->
    RawCodedFormulaShift M cutoff amount sourceRight targetRight ->
    RawCodedFormulaShift M cutoff amount
      (rawFormulaShiftBinaryCode M kind sourceLeft sourceRight)
      (rawFormulaShiftBinaryCode M kind targetLeft targetRight)) /\
  (forall kind cutoff amount sourceChild targetChild,
    RawCodedFormulaShift M (raw_succ M cutoff) amount
      sourceChild targetChild ->
    RawCodedFormulaShift M cutoff amount
      (rawFormulaShiftUnaryCode M kind sourceChild)
      (rawFormulaShiftUnaryCode M kind targetChild)).

Arguments RawCodedFormulaShiftCompositional M : clear implicits.

(** ------------------------------------------------------------------
    A represented strong induction over formula *codes*.

    Quantifying over [cutoff] inside the invariant is essential.  When the
    current row is a quantifier, the induction hypothesis is instantiated at
    [S cutoff] for its child. *)

Definition RawCodedFormulaShiftTotalBelow (M : RawPAModel)
    (current : M) : Prop :=
  forall input : M,
    rawLt M input current ->
    RawCodedFormulaAtomicallyAdequate M input ->
    forall cutoff amount : M,
      exists output : M,
        RawCodedFormulaShift M cutoff amount input output.

Arguments RawCodedFormulaShiftTotalBelow M current : clear implicits.

Definition codedFormulaShiftTotalBelowTermAt (current : term) : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 current))
      (pImp
        (codedFormulaAtomicallyAdequateTermAt (tVar 0))
        (pAll (pAll (pEx
          (codedFormulaShiftTermAt
            (tVar 2) (tVar 1) (tVar 3) (tVar 0))))))).

Lemma raw_sat_codedFormulaShiftTotalBelowTermAt_iff : forall
    (M : RawPAModel) e current,
  raw_formula_sat M e (codedFormulaShiftTotalBelowTermAt current) <->
  RawCodedFormulaShiftTotalBelow M (raw_term_eval M e current).
Proof.
  intros. unfold codedFormulaShiftTotalBelowTermAt,
    RawCodedFormulaShiftTotalBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaShiftTermAt_iff.
  repeat setoid_rewrite raw_shiftTotality_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_codedFormulaShiftTotalBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaShiftTotalBelow M (raw_zero M).
Proof.
  intros M hPA input hinput _ cutoff amount.
  exfalso. exact (raw_not_lt_zero M hPA input hinput).
Qed.

(** One successor stage uses an adequate syntax traversal only to expose the
    current constructor and to re-root adequacy at its earlier child rows.
    Numeric child-code descent then makes the strong prefix hypothesis
    applicable independently of the occurrence indices. *)
Lemma raw_codedFormulaShiftTotalBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaShiftCompositional M ->
  forall current,
  RawCodedFormulaShiftTotalBelow M current ->
  RawCodedFormulaShiftTotalBelow M (raw_succ M current).
Proof.
  intros M hPA [hbinary hunary] current hprefix
    input hinput hadequate cutoff amount.
  destruct (raw_lt_succ_cases M hPA input current hinput)
    as [hbefore | ->].
  - exact (hprefix input hbefore hadequate cutoff amount).
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
      exact (raw_codedFormulaShift_eq_exists_of_term_syntax M hPA
        cutoff amount sourceLeft sourceRight
        (raw_zero M) (raw_zero M) hleftSyntax hrightSyntax).
    + cbn [rawCodedFormulaShapeCode] in hcode. subst current.
      exact (raw_codedFormulaShift_bot_exists M hPA cutoff amount).
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
      destruct (hprefix sourceLeft
        (raw_formulaCodeList3_left_lt M hPA
          (rawNumeralValue M 2) sourceLeft sourceRight)
        hleftAdequate cutoff amount) as [targetLeft hleftShift].
      destruct (hprefix sourceRight
        (raw_formulaCodeList3_right_lt M hPA
          (rawNumeralValue M 2) sourceLeft sourceRight)
        hrightAdequate cutoff amount) as [targetRight hrightShift].
      exists (rawFormulaImpCode M targetLeft targetRight).
      exact (hbinary RFSBImp cutoff amount
        sourceLeft targetLeft sourceRight targetRight
        hleftShift hrightShift).
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
      destruct (hprefix sourceLeft
        (raw_formulaCodeList3_left_lt M hPA
          (rawNumeralValue M 3) sourceLeft sourceRight)
        hleftAdequate cutoff amount) as [targetLeft hleftShift].
      destruct (hprefix sourceRight
        (raw_formulaCodeList3_right_lt M hPA
          (rawNumeralValue M 3) sourceLeft sourceRight)
        hrightAdequate cutoff amount) as [targetRight hrightShift].
      exists (rawFormulaAndCode M targetLeft targetRight).
      exact (hbinary RFSBAnd cutoff amount
        sourceLeft targetLeft sourceRight targetRight
        hleftShift hrightShift).
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
      destruct (hprefix sourceLeft
        (raw_formulaCodeList3_left_lt M hPA
          (rawNumeralValue M 4) sourceLeft sourceRight)
        hleftAdequate cutoff amount) as [targetLeft hleftShift].
      destruct (hprefix sourceRight
        (raw_formulaCodeList3_right_lt M hPA
          (rawNumeralValue M 4) sourceLeft sourceRight)
        hrightAdequate cutoff amount) as [targetRight hrightShift].
      exists (rawFormulaOrCode M targetLeft targetRight).
      exact (hbinary RFSBOr cutoff amount
        sourceLeft targetLeft sourceRight targetRight
        hleftShift hrightShift).
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
      destruct (hprefix sourceChild
        (raw_formulaCodeList2_child_lt M hPA
          (rawNumeralValue M 5) sourceChild)
        hchildAdequate (raw_succ M cutoff) amount)
        as [targetChild hchildShift].
      exists (rawFormulaAllCode M targetChild).
      exact (hunary RFSUAll cutoff amount
        sourceChild targetChild hchildShift).
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
      destruct (hprefix sourceChild
        (raw_formulaCodeList2_child_lt M hPA
          (rawNumeralValue M 6) sourceChild)
        hchildAdequate (raw_succ M cutoff) amount)
        as [targetChild hchildShift].
      exists (rawFormulaExCode M targetChild).
      exact (hunary RFSUEx cutoff amount
        sourceChild targetChild hchildShift).
Qed.

(** The induction formula is precisely
    [codedFormulaShiftTotalBelowTermAt]; hence this theorem ranges over all
    carrier elements, including nonstandard formula-code bounds. *)
Theorem raw_codedFormulaShiftTotalBelow_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaShiftCompositional M ->
  forall current, RawCodedFormulaShiftTotalBelow M current.
Proof.
  intros M hPA hcompositional.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := codedFormulaShiftTotalBelowTermAt (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_codedFormulaShiftTotalBelowTermAt_iff M
        (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_codedFormulaShiftTotalBelow_zero M hPA).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedFormulaShiftTotalBelowTermAt_iff M
          (scons M current parameterEnv) (tVar 0)) hcurrentSat)
        as hcurrent.
      apply (proj2 (raw_sat_codedFormulaShiftTotalBelowTermAt_iff M
        (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_codedFormulaShiftTotalBelow_succ M hPA
        hcompositional current hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1 (raw_sat_codedFormulaShiftTotalBelowTermAt_iff M
    (scons M current parameterEnv) (tVar 0)) (hall current)) as hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

Theorem raw_codedFormulaShift_exists_of_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaShiftCompositional M ->
  forall source,
  RawCodedFormulaAtomicallyAdequate M source ->
  forall cutoff amount,
    exists target, RawCodedFormulaShift M cutoff amount source target.
Proof.
  intros M hPA hcompositional source hadequate cutoff amount.
  pose proof (raw_codedFormulaShiftTotalBelow_all M hPA
    hcompositional (raw_succ M source)) as hall.
  exact (hall source (raw_assignment_lt_self_succ M hPA source)
    hadequate cutoff amount).
Qed.

(** This is the exact unit shift required by context insertion.  It is
    conditional only on the two trace-splicing clauses displayed in
    [RawCodedFormulaShiftCompositional]. *)
Corollary raw_codedFormulaUnitShift_exists_of_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaShiftCompositional M ->
  forall source,
  RawCodedFormulaAtomicallyAdequate M source ->
  exists target,
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1) source target.
Proof.
  intros M hPA hcompositional source hadequate.
  exact (raw_codedFormulaShift_exists_of_atomically_adequate M hPA
    hcompositional source hadequate
    (raw_zero M) (rawNumeralValue M 1)).
Qed.

End PABoundedRawCodedFormulaShiftTotality.
