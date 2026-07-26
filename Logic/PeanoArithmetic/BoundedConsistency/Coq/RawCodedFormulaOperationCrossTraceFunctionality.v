(**
  Cross-trace functionality for represented formula operations.

  Term-operation atoms are functional by
  [RawCodedTermOperationCrossTraceFunctionality].  This module lifts that
  fact through arbitrary, possibly nonstandard, formula traversals.  As at
  term level, the proof is PA-definable induction on the first trace's root
  row index; the competing trace may use wholly unrelated beta tables.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity
  RawCodedAssignment RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation RawCodedFormulaOperations
  RawCodedProofAtomicAdequacyStandard
  RawCodedTermOperationCrossTraceFunctionality.

Module PABoundedRawCodedFormulaOperationCrossTraceFunctionality.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedTermOperationCrossTraceFunctionality.

(** Preserve the concrete left tables when rerooting. *)
Lemma raw_codedFormulaOperationTrace_reroot_exact : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      atom parameter rootDepth
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex input output,
  RawCodedFormulaOperationTrace M atom parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output ->
  forall childIndex childInput childOutput childDepth,
  rawLt M childIndex rootIndex ->
  RawCodedFormulaOperationTripleLookup M
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    childIndex childInput childOutput childDepth ->
  RawCodedFormulaOperationTrace M atom parameter childDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound childIndex childInput childOutput.
Proof.
  intros M hPA atom parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output htrace
    childIndex childInput childOutput childDepth hchild hlookup.
  destruct htrace as
    (hsource & htarget & hdepth & hroot & hrootLookup & hrows).
  split; [exact hsource |].
  split; [exact htarget |].
  split; [exact hdepth |].
  split.
  - exact (raw_assignment_lt_trans M hPA
      childIndex rootIndex bound hchild hroot).
  - split; [exact hlookup | exact hrows].
Qed.

Corollary raw_codedFormulaOperation_reroot : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      atom parameter rootDepth
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex input output,
  RawCodedFormulaOperationTrace M atom parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output ->
  forall childIndex childInput childOutput childDepth,
  rawLt M childIndex rootIndex ->
  RawCodedFormulaOperationTripleLookup M
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    childIndex childInput childOutput childDepth ->
  RawCodedFormulaOperation M atom parameter childDepth
    childInput childOutput.
Proof.
  intros M hPA atom parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output htrace
    childIndex childInput childOutput childDepth hchild hlookup.
  exists sourceCode, sourceStep, targetCode, targetStep,
    depthCode, depthStep, bound, childIndex.
  exact (raw_codedFormulaOperationTrace_reroot_exact M hPA
    atom parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output htrace
    childIndex childInput childOutput childDepth hchild hlookup).
Qed.

(** ------------------------------------------------------------------
    The generic PA-definable induction invariant. *)

Definition RawCodedFormulaOperationIndexFunctionalBelow
    (M : RawPAModel) (atom : M -> M -> M -> M -> Prop)
    (current : M) : Prop :=
  forall parameter rootDepth
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex input output otherOutput : M,
    rawLt M rootIndex current ->
    RawCodedFormulaOperationTrace M atom parameter rootDepth
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex input output ->
    RawCodedFormulaOperation M atom parameter rootDepth
      input otherOutput ->
    output = otherOutput.

Arguments RawCodedFormulaOperationIndexFunctionalBelow
  M atom current : clear implicits.

Definition formulaOperationAll13 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll (pAll
    (pAll (pAll (pAll (pAll (pAll (pAll body)))))))))))).

(** Binders 12 down to 0 are parameter, rootDepth, six table columns,
    bound, rootIndex, input, output, and the competing output. *)
Definition codedFormulaOperationIndexFunctionalBelowTermAt
    (atom : term -> term -> term -> term -> formula)
    (current : term) : formula :=
  formulaOperationAll13
    (pImp
      (Formula.ltTermAt (tVar 3) (liftTerm 13 current))
      (pImp
        (codedFormulaOperationTraceTermAt atom
          (tVar 12) (tVar 11)
          (tVar 10) (tVar 9) (tVar 8) (tVar 7)
          (tVar 6) (tVar 5) (tVar 4) (tVar 3)
          (tVar 2) (tVar 1))
        (pImp
          (codedFormulaOperationTermAt atom
            (tVar 12) (tVar 11) (tVar 2) (tVar 0))
          (pEq (tVar 1) (tVar 0))))).

Lemma raw_formulaOperation_eval_liftTerm_thirteen : forall
    (M : RawPAModel) a b c d f g h i j k l m n
    (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i
        (scons M j (scons M k (scons M l (scons M m
          (scons M n e)))))))))))))
    (liftTerm 13 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i j k l m n e t.
  unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro x.
  replace (x + 13) with
    (S (S (S (S (S (S (S (S (S (S (S (S (S x)))))))))))))
    by lia.
  reflexivity.
Qed.

Lemma raw_sat_codedFormulaOperationIndexFunctionalBelowTermAt_iff :
  forall (M : RawPAModel) (e : nat -> M)
    (atomFormula : term -> term -> term -> term -> formula)
    (atom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atomFormula parameter depth input output) <->
    atom (raw_term_eval M e' parameter) (raw_term_eval M e' depth)
      (raw_term_eval M e' input) (raw_term_eval M e' output)) ->
  forall current,
  raw_formula_sat M e
    (codedFormulaOperationIndexFunctionalBelowTermAt
      atomFormula current) <->
  RawCodedFormulaOperationIndexFunctionalBelow M atom
    (raw_term_eval M e current).
Proof.
  intros M e atomFormula atom hatom current.
  unfold codedFormulaOperationIndexFunctionalBelowTermAt,
    formulaOperationAll13,
    RawCodedFormulaOperationIndexFunctionalBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite (raw_sat_codedFormulaOperationTraceTermAt_iff
    M _ atomFormula atom hatom).
  setoid_rewrite (raw_sat_codedFormulaOperationTermAt_iff
    M _ atomFormula atom hatom).
  repeat setoid_rewrite raw_formulaOperation_eval_liftTerm_thirteen.
  cbn [raw_term_eval scons].
  split; intros h parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output otherOutput;
    exact (h parameter rootDepth
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex input output otherOutput).
Qed.

(** Extract source-code equations from any formula row.  On a mismatched
    pair, constructor separation closes the branch.  On matching pairs the
    tactic deliberately fails and restores the context for the real proof. *)
Ltac raw_formula_row_mismatch M hPA left right :=
  let leftInput := fresh "leftInput" in
  let rightInput := fresh "rightInput" in
  lazymatch type of left with
  | RawCodedFormulaEqOperationRow _ _ _ _ _ _ =>
      let il := fresh "inputLeft" in let ol := fresh "outputLeft" in
      let ir := fresh "inputRight" in let orr := fresh "outputRight" in
      let hout := fresh "houtput" in
      let hal := fresh "hleftAtom" in let har := fresh "hrightAtom" in
      destruct left as (il & ol & ir & orr & leftInput & hout & hal & har)
  | RawCodedFormulaBotOperationRow _ _ _ =>
      let hout := fresh "houtput" in destruct left as [leftInput hout]
  | RawCodedFormulaBinaryOperationRow _ _ _ _ _ _ _ _ _ _ _ _ =>
      let li := fresh "leftIndex" in let il := fresh "inputLeft" in
      let ol := fresh "outputLeft" in let ld := fresh "leftDepth" in
      let ri := fresh "rightIndex" in let ir := fresh "inputRight" in
      let orr := fresh "outputRight" in let rd := fresh "rightDepth" in
      let hli := fresh "hleftIndex" in let hll := fresh "hleftLookup" in
      let hld := fresh "hleftDepth" in let hri := fresh "hrightIndex" in
      let hrl := fresh "hrightLookup" in let hrd := fresh "hrightDepth" in
      let hout := fresh "houtput" in
      destruct left as
        (li & il & ol & ld & ri & ir & orr & rd &
         hli & hll & hld & hri & hrl & hrd & leftInput & hout)
  | RawCodedFormulaUnaryOperationRow _ _ _ _ _ _ _ _ _ _ _ _ =>
      let ci := fresh "childIndex" in let cin := fresh "inputChild" in
      let cout := fresh "outputChild" in let cd := fresh "childDepth" in
      let hci := fresh "hchildIndex" in let hcl := fresh "hchildLookup" in
      let hcd := fresh "hchildDepth" in let hout := fresh "houtput" in
      destruct left as
        (ci & cin & cout & cd & hci & hcl & hcd & leftInput & hout)
  end;
  lazymatch type of right with
  | RawCodedFormulaEqOperationRow _ _ _ _ _ _ =>
      let il := fresh "inputLeft" in let ol := fresh "outputLeft" in
      let ir := fresh "inputRight" in let orr := fresh "outputRight" in
      let hout := fresh "houtput" in
      let hal := fresh "hleftAtom" in let har := fresh "hrightAtom" in
      destruct right as (il & ol & ir & orr & rightInput & hout & hal & har)
  | RawCodedFormulaBotOperationRow _ _ _ =>
      let hout := fresh "houtput" in destruct right as [rightInput hout]
  | RawCodedFormulaBinaryOperationRow _ _ _ _ _ _ _ _ _ _ _ _ =>
      let li := fresh "leftIndex" in let il := fresh "inputLeft" in
      let ol := fresh "outputLeft" in let ld := fresh "leftDepth" in
      let ri := fresh "rightIndex" in let ir := fresh "inputRight" in
      let orr := fresh "outputRight" in let rd := fresh "rightDepth" in
      let hli := fresh "hleftIndex" in let hll := fresh "hleftLookup" in
      let hld := fresh "hleftDepth" in let hri := fresh "hrightIndex" in
      let hrl := fresh "hrightLookup" in let hrd := fresh "hrightDepth" in
      let hout := fresh "houtput" in
      destruct right as
        (li & il & ol & ld & ri & ir & orr & rd &
         hli & hll & hld & hri & hrl & hrd & rightInput & hout)
  | RawCodedFormulaUnaryOperationRow _ _ _ _ _ _ _ _ _ _ _ _ =>
      let ci := fresh "childIndex" in let cin := fresh "inputChild" in
      let cout := fresh "outputChild" in let cd := fresh "childDepth" in
      let hci := fresh "hchildIndex" in let hcl := fresh "hchildLookup" in
      let hcd := fresh "hchildDepth" in let hout := fresh "houtput" in
      destruct right as
        (ci & cin & cout & cd & hci & hcl & hcd & rightInput & hout)
  end;
  let hshape := fresh "hshape" in
  assert (hshape := eq_trans (eq_sym leftInput) rightInput);
  exfalso; raw_standard_formula_shape_contradiction M hPA hshape.

Ltac raw_formula_rows_mismatch M hPA :=
  match goal with
  | left : RawCodedFormulaEqOperationRow _ _ _ _ _ _,
    right : ?T |- _ => raw_formula_row_mismatch M hPA left right
  | left : RawCodedFormulaBotOperationRow _ _ _,
    right : ?T |- _ => raw_formula_row_mismatch M hPA left right
  | left : RawCodedFormulaBinaryOperationRow _ _ _ _ _ _ _ _ _ _ _ _,
    right : ?T |- _ => raw_formula_row_mismatch M hPA left right
  | left : RawCodedFormulaUnaryOperationRow _ _ _ _ _ _ _ _ _ _ _ _,
    right : ?T |- _ => raw_formula_row_mismatch M hPA left right
  end.

Definition RawBinaryCodeConstructorInjective (M : RawPAModel)
    (constructor : M -> M -> M) : Prop :=
  forall left right left' right',
    constructor left right = constructor left' right' ->
    left = left' /\ right = right'.

Definition RawUnaryCodeConstructorInjective (M : RawPAModel)
    (constructor : M -> M) : Prop :=
  forall child child', constructor child = constructor child' ->
    child = child'.

Lemma rawFormulaImpCode_injective_cross : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawBinaryCodeConstructorInjective M (rawFormulaImpCode M).
Proof.
  intros M hPA left right left' right' heq.
  unfold rawFormulaImpCode in heq.
  destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
    _ _ _ _ _ _ heq) as [_ [hleft hright]].
  split; assumption.
Qed.

Lemma rawFormulaAndCode_injective_cross : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawBinaryCodeConstructorInjective M (rawFormulaAndCode M).
Proof.
  intros M hPA left right left' right' heq.
  unfold rawFormulaAndCode in heq.
  destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
    _ _ _ _ _ _ heq) as [_ [hleft hright]].
  split; assumption.
Qed.

Lemma rawFormulaOrCode_injective_cross : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawBinaryCodeConstructorInjective M (rawFormulaOrCode M).
Proof.
  intros M hPA left right left' right' heq.
  unfold rawFormulaOrCode in heq.
  destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
    _ _ _ _ _ _ heq) as [_ [hleft hright]].
  split; assumption.
Qed.

Lemma rawFormulaAllCode_injective_cross : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawUnaryCodeConstructorInjective M (rawFormulaAllCode M).
Proof.
  intros M hPA child child' heq.
  unfold rawFormulaAllCode in heq.
  destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
    _ _ _ _ heq) as [_ hchild]. exact hchild.
Qed.

Lemma rawFormulaExCode_injective_cross : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawUnaryCodeConstructorInjective M (rawFormulaExCode M).
Proof.
  intros M hPA child child' heq.
  unfold rawFormulaExCode in heq.
  destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
    _ _ _ _ heq) as [_ hchild]. exact hchild.
Qed.

(** The recursive binary case, shared by implication, conjunction and
    disjunction. *)
Lemma raw_codedFormulaBinaryRows_cross_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall atom current,
  RawCodedFormulaOperationIndexFunctionalBelow M atom current ->
  forall parameter rootDepth constructor,
  RawBinaryCodeConstructorInjective M constructor ->
  forall
    sourceCode sourceStep targetCode targetStep depthCode depthStep bound
    input output
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightDepthCode rightDepthStep rightBound rightRootIndex otherOutput,
  RawCodedFormulaOperationTrace M atom parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound current input output ->
  RawCodedFormulaOperationTrace M atom parameter rootDepth
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightDepthCode rightDepthStep rightBound rightRootIndex
    input otherOutput ->
  RawCodedFormulaBinaryOperationRow M constructor
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    current input output rootDepth ->
  RawCodedFormulaBinaryOperationRow M constructor
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightDepthCode rightDepthStep
    rightRootIndex input otherOutput rootDepth ->
  output = otherOutput.
Proof.
  intros M hPA atom current hcurrent parameter rootDepth constructor
    hinjective
    sourceCode sourceStep targetCode targetStep depthCode depthStep bound
    input output
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightDepthCode rightDepthStep rightBound rightRootIndex otherOutput
    hleftTrace hrightTrace hleftRow hrightRow.
  destruct hleftRow as
    (leftLeftIndex & leftInputLeft & leftOutputLeft & leftLeftDepth &
     leftRightIndex & leftInputRight & leftOutputRight & leftRightDepth &
     hleftLeftIndex & hleftLeftLookup & hleftLeftDepth &
     hleftRightIndex & hleftRightLookup & hleftRightDepth &
     hleftInput & hleftOutput).
  destruct hrightRow as
    (rightLeftIndex & rightInputLeft & rightOutputLeft & rightLeftDepth &
     rightRightIndex & rightInputRight & rightOutputRight & rightRightDepth &
     hrightLeftIndex & hrightLeftLookup & hrightLeftDepth &
     hrightRightIndex & hrightRightLookup & hrightRightDepth &
     hrightInput & hrightOutput).
  destruct (hinjective _ _ _ _
    (eq_trans (eq_sym hleftInput) hrightInput))
    as [hinputLeft hinputRight].
  subst rightInputLeft. subst rightInputRight.
  subst leftLeftDepth. subst leftRightDepth.
  subst rightLeftDepth. subst rightRightDepth.
  assert (houtputLeft : leftOutputLeft = rightOutputLeft).
  {
    apply (hcurrent parameter rootDepth
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound leftLeftIndex leftInputLeft leftOutputLeft rightOutputLeft
      hleftLeftIndex).
    - exact (raw_codedFormulaOperationTrace_reroot_exact M hPA
        atom parameter rootDepth
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound current input output hleftTrace
        leftLeftIndex leftInputLeft leftOutputLeft rootDepth
        hleftLeftIndex hleftLeftLookup).
    - exact (raw_codedFormulaOperation_reroot M hPA
        atom parameter rootDepth
        rightSourceCode rightSourceStep rightTargetCode rightTargetStep
        rightDepthCode rightDepthStep rightBound rightRootIndex
        input otherOutput hrightTrace
        rightLeftIndex leftInputLeft rightOutputLeft rootDepth
        hrightLeftIndex hrightLeftLookup).
  }
  assert (houtputRight : leftOutputRight = rightOutputRight).
  {
    apply (hcurrent parameter rootDepth
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound leftRightIndex leftInputRight leftOutputRight rightOutputRight
      hleftRightIndex).
    - exact (raw_codedFormulaOperationTrace_reroot_exact M hPA
        atom parameter rootDepth
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound current input output hleftTrace
        leftRightIndex leftInputRight leftOutputRight rootDepth
        hleftRightIndex hleftRightLookup).
    - exact (raw_codedFormulaOperation_reroot M hPA
        atom parameter rootDepth
        rightSourceCode rightSourceStep rightTargetCode rightTargetStep
        rightDepthCode rightDepthStep rightBound rightRootIndex
        input otherOutput hrightTrace
        rightRightIndex leftInputRight rightOutputRight rootDepth
        hrightRightIndex hrightRightLookup).
  }
  rewrite hleftOutput, hrightOutput, houtputLeft, houtputRight.
  reflexivity.
Qed.

(** The analogous shared quantified case. *)
Lemma raw_codedFormulaUnaryRows_cross_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall atom current,
  RawCodedFormulaOperationIndexFunctionalBelow M atom current ->
  forall parameter rootDepth constructor,
  RawUnaryCodeConstructorInjective M constructor ->
  forall
    sourceCode sourceStep targetCode targetStep depthCode depthStep bound
    input output
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightDepthCode rightDepthStep rightBound rightRootIndex otherOutput,
  RawCodedFormulaOperationTrace M atom parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound current input output ->
  RawCodedFormulaOperationTrace M atom parameter rootDepth
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightDepthCode rightDepthStep rightBound rightRootIndex
    input otherOutput ->
  RawCodedFormulaUnaryOperationRow M constructor
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    current input output rootDepth ->
  RawCodedFormulaUnaryOperationRow M constructor
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightDepthCode rightDepthStep
    rightRootIndex input otherOutput rootDepth ->
  output = otherOutput.
Proof.
  intros M hPA atom current hcurrent parameter rootDepth constructor
    hinjective
    sourceCode sourceStep targetCode targetStep depthCode depthStep bound
    input output
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightDepthCode rightDepthStep rightBound rightRootIndex otherOutput
    hleftTrace hrightTrace hleftRow hrightRow.
  destruct hleftRow as
    (leftChildIndex & leftInputChild & leftOutputChild & leftChildDepth &
     hleftChildIndex & hleftChildLookup & hleftChildDepth &
     hleftInput & hleftOutput).
  destruct hrightRow as
    (rightChildIndex & rightInputChild & rightOutputChild & rightChildDepth &
     hrightChildIndex & hrightChildLookup & hrightChildDepth &
     hrightInput & hrightOutput).
  assert (hinputChild : leftInputChild = rightInputChild).
  {
    exact (hinjective _ _ (eq_trans (eq_sym hleftInput) hrightInput)).
  }
  subst rightInputChild.
  subst leftChildDepth. subst rightChildDepth.
  assert (houtputChild : leftOutputChild = rightOutputChild).
  {
    apply (hcurrent parameter (raw_succ M rootDepth)
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound leftChildIndex leftInputChild leftOutputChild rightOutputChild
      hleftChildIndex).
    - exact (raw_codedFormulaOperationTrace_reroot_exact M hPA
        atom parameter rootDepth
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound current input output hleftTrace
        leftChildIndex leftInputChild leftOutputChild
        (raw_succ M rootDepth) hleftChildIndex hleftChildLookup).
    - exact (raw_codedFormulaOperation_reroot M hPA
        atom parameter rootDepth
        rightSourceCode rightSourceStep rightTargetCode rightTargetStep
        rightDepthCode rightDepthStep rightBound rightRootIndex
        input otherOutput hrightTrace
        rightChildIndex leftInputChild rightOutputChild
        (raw_succ M rootDepth) hrightChildIndex hrightChildLookup).
  }
  rewrite hleftOutput, hrightOutput, houtputChild. reflexivity.
Qed.

Theorem raw_codedFormulaOperationIndexFunctionalBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall atom,
  RawCodedFormulaOperationAtomFunctional M atom ->
  forall current,
  RawCodedFormulaOperationIndexFunctionalBelow M atom current ->
  RawCodedFormulaOperationIndexFunctionalBelow M atom
    (raw_succ M current).
Proof.
  intros M hPA atom hatom current hcurrent
    parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output otherOutput
    hrootIndex hleftTrace hrightOperation.
  destruct (raw_lt_succ_cases M hPA rootIndex current hrootIndex)
    as [hbefore | hrootCurrent].
  - exact (hcurrent parameter rootDepth
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex input output otherOutput
      hbefore hleftTrace hrightOperation).
  - subst rootIndex.
    destruct hrightOperation as
      (rightSourceCode & rightSourceStep & rightTargetCode &
       rightTargetStep & rightDepthCode & rightDepthStep &
       rightBound & rightRootIndex & hrightTrace).
    pose proof hleftTrace as hleftFacts.
    pose proof hrightTrace as hrightFacts.
    destruct hleftFacts as
      (_ & _ & _ & hleftRoot & hleftLookup & hleftRows).
    destruct hrightFacts as
      (_ & _ & _ & hrightRoot & hrightLookup & hrightRows).
    pose proof (hleftRows current input output rootDepth
      hleftRoot hleftLookup) as hleftRow.
    pose proof (hrightRows rightRootIndex input otherOutput rootDepth
      hrightRoot hrightLookup) as hrightRow.
    unfold RawCodedFormulaOperationTraversalRow in hleftRow, hrightRow.
    destruct hleftRow as
      [ hleftEq
      | [ hleftBot
        | [ hleftImp
          | [ hleftAnd
            | [ hleftOr
              | [ hleftAll | hleftEx ] ] ] ] ] ];
    destruct hrightRow as
      [ hrightEq
      | [ hrightBot
        | [ hrightImp
          | [ hrightAnd
            | [ hrightOr
              | [ hrightAll | hrightEx ] ] ] ] ] ].
  all: try solve [raw_formula_rows_mismatch M hPA].
  + destruct hleftEq as
      (leftInputLeft & leftOutputLeft & leftInputRight & leftOutputRight &
       hleftInput & hleftOutput & hleftLeftAtom & hleftRightAtom).
    destruct hrightEq as
      (rightInputLeft & rightOutputLeft & rightInputRight & rightOutputRight &
       hrightInput & hrightOutput & hrightLeftAtom & hrightRightAtom).
    assert (hinputs : leftInputLeft = rightInputLeft /\
        leftInputRight = rightInputRight).
    {
      unfold rawFormulaEqCode in hleftInput, hrightInput.
      destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
        _ _ _ _ _ _ (eq_trans (eq_sym hleftInput) hrightInput))
        as [_ [hleft hright]]. split; assumption.
    }
    destruct hinputs as [-> ->].
    pose proof (hatom parameter rootDepth rightInputLeft
      leftOutputLeft rightOutputLeft hleftLeftAtom hrightLeftAtom)
      as hleftOutputTerm.
    pose proof (hatom parameter rootDepth rightInputRight
      leftOutputRight rightOutputRight hleftRightAtom hrightRightAtom)
      as hrightOutputTerm.
    rewrite hleftOutput, hrightOutput,
      hleftOutputTerm, hrightOutputTerm. reflexivity.
  + destruct hleftBot as [_ ->]. destruct hrightBot as [_ ->].
    reflexivity.
  + eapply (raw_codedFormulaBinaryRows_cross_functional
      M hPA atom current hcurrent parameter rootDepth
      (rawFormulaImpCode M)).
    * exact (rawFormulaImpCode_injective_cross M hPA).
    * exact hleftTrace.
    * exact hrightTrace.
    * exact hleftImp.
    * exact hrightImp.
  + eapply (raw_codedFormulaBinaryRows_cross_functional
      M hPA atom current hcurrent parameter rootDepth
      (rawFormulaAndCode M)).
    * exact (rawFormulaAndCode_injective_cross M hPA).
    * exact hleftTrace.
    * exact hrightTrace.
    * exact hleftAnd.
    * exact hrightAnd.
  + eapply (raw_codedFormulaBinaryRows_cross_functional
      M hPA atom current hcurrent parameter rootDepth
      (rawFormulaOrCode M)).
    * exact (rawFormulaOrCode_injective_cross M hPA).
    * exact hleftTrace.
    * exact hrightTrace.
    * exact hleftOr.
    * exact hrightOr.
  + eapply (raw_codedFormulaUnaryRows_cross_functional
      M hPA atom current hcurrent parameter rootDepth
      (rawFormulaAllCode M)).
    * exact (rawFormulaAllCode_injective_cross M hPA).
    * exact hleftTrace.
    * exact hrightTrace.
    * exact hleftAll.
    * exact hrightAll.
  + eapply (raw_codedFormulaUnaryRows_cross_functional
      M hPA atom current hcurrent parameter rootDepth
      (rawFormulaExCode M)).
    * exact (rawFormulaExCode_injective_cross M hPA).
    * exact hleftTrace.
    * exact hrightTrace.
    * exact hleftEx.
    * exact hrightEx.
Qed.

Theorem raw_codedFormulaOperationIndexFunctionalBelow_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall
    (atomFormula : term -> term -> term -> term -> formula)
    (atom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e'
      (atomFormula parameter depth input output) <->
    atom (raw_term_eval M e' parameter) (raw_term_eval M e' depth)
      (raw_term_eval M e' input) (raw_term_eval M e' output)) ->
  RawCodedFormulaOperationAtomFunctional M atom ->
  forall current,
    RawCodedFormulaOperationIndexFunctionalBelow M atom current.
Proof.
  intros M hPA atomFormula atom hatom hfunctional.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := codedFormulaOperationIndexFunctionalBelowTermAt
    atomFormula (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedFormulaOperationIndexFunctionalBelowTermAt_iff
          M (scons M (raw_zero M) parameterEnv)
          atomFormula atom hatom (tVar 0))).
      cbn [raw_term_eval scons].
      intros parameter rootDepth
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound rootIndex input output otherOutput hrootIndex.
      exfalso. exact (raw_not_lt_zero M hPA rootIndex hrootIndex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_codedFormulaOperationIndexFunctionalBelowTermAt_iff
          M (scons M current parameterEnv)
          atomFormula atom hatom (tVar 0)) hcurrent) as hraw.
      apply (proj2
        (raw_sat_codedFormulaOperationIndexFunctionalBelowTermAt_iff
          M (scons M (raw_succ M current) parameterEnv)
          atomFormula atom hatom (tVar 0))).
      cbn [raw_term_eval scons] in hraw |- *.
      exact (raw_codedFormulaOperationIndexFunctionalBelow_succ
        M hPA atom hfunctional current hraw).
  }
  intro current.
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedFormulaOperationIndexFunctionalBelowTermAt_iff
      M (scons M current parameterEnv)
      atomFormula atom hatom (tVar 0)) (hall current)) as hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

(** The public generic cross-certificate theorem. *)
Theorem raw_codedFormulaOperation_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall
    (atomFormula : term -> term -> term -> term -> formula)
    (atom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e'
      (atomFormula parameter depth input output) <->
    atom (raw_term_eval M e' parameter) (raw_term_eval M e' depth)
      (raw_term_eval M e' input) (raw_term_eval M e' output)) ->
  RawCodedFormulaOperationAtomFunctional M atom ->
  forall parameter rootDepth input output output',
    RawCodedFormulaOperation M atom parameter rootDepth input output ->
    RawCodedFormulaOperation M atom parameter rootDepth input output' ->
    output = output'.
Proof.
  intros M hPA atomFormula atom hatom hfunctional
    parameter rootDepth input output output'
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & hleftTrace) hright.
  exact (raw_codedFormulaOperationIndexFunctionalBelow_all
    M hPA atomFormula atom hatom hfunctional (raw_succ M rootIndex)
    parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output output'
    (raw_assignment_lt_self_succ M hPA rootIndex)
    hleftTrace hright).
Qed.

Corollary raw_codedFormulaShift_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount input output output',
  RawCodedFormulaShift M cutoff amount input output ->
  RawCodedFormulaShift M cutoff amount input output' ->
  output = output'.
Proof.
  intros M hPA cutoff amount input output output'.
  apply (raw_codedFormulaOperation_functional M hPA
    codedFormulaShiftAtomTermAt (RawCodedFormulaShiftAtom M)
    (raw_sat_codedFormulaShiftAtomTermAt_iff M)
    (raw_codedFormulaShiftAtom_functional M hPA)
    amount cutoff input output output').
Qed.

Corollary raw_codedFormulaSubstitution_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement depth input output output',
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement depth input output ->
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement depth input output' ->
  output = output'.
Proof.
  intros M hPA replacement depth input output output'.
  apply (raw_codedFormulaOperation_functional M hPA
    codedFormulaSubstitutionAtomTermAt
    (RawCodedFormulaSubstitutionAtom M)
    (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M)
    (raw_codedFormulaSubstitutionAtom_functional M hPA)
    replacement depth input output output').
Qed.

Corollary raw_codedFormulaSingleSubstitution_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement input output output',
  RawCodedFormulaSingleSubstitution M replacement input output ->
  RawCodedFormulaSingleSubstitution M replacement input output' ->
  output = output'.
Proof.
  intros M hPA replacement input output output'.
  exact (raw_codedFormulaSubstitution_functional M hPA
    replacement (raw_zero M) input output output').
Qed.

End PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
