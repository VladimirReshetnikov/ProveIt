(**
  Cross-trace functionality for represented term operations.

  The public shift and opening relations existentially hide their source and
  target beta tables.  Functionality inside one table is immediate from beta
  lookup functionality, but it does not compare two independently generated
  traces.  This module closes that gap for shifting and opening.

  The proof cannot recurse on a carrier element in Coq: a raw PA model may be
  nonstandard.  Instead it follows the pattern used for formula-rank
  functionality.  A genuine PA-definable induction ranges over the root-row
  index of the first trace.  Recursive children occur at strictly smaller
  indices, while the second trace may use unrelated tables and indices.
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
  RawCodedProofAtomicAdequacyStandard.

Module PABoundedRawCodedTermOperationCrossTraceFunctionality.

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

(** The two branches of [RawShiftedIndex] cannot disagree. *)
Lemma raw_shiftedIndex_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount input output output',
  RawShiftedIndex M cutoff amount input output ->
  RawShiftedIndex M cutoff amount input output' ->
  output = output'.
Proof.
  intros M hPA cutoff amount input output output' hleft hright.
  destruct hleft as [[hleftBelow ->] | [hleftAbove ->]];
    destruct hright as [[hrightBelow ->] | [hrightAbove ->]];
    try reflexivity.
  - exfalso. apply (raw_not_lt_self M hPA input).
    exact (raw_lt_le_trans_pair M hPA
      input cutoff input hleftBelow hrightAbove).
  - exfalso. apply (raw_not_lt_self M hPA input).
    exact (raw_lt_le_trans_pair M hPA
      input cutoff input hrightBelow hleftAbove).
Qed.

(** Variable rows are functional even when their enclosing operation tables
    are unrelated. *)
Lemma raw_codedTermShiftVariableRow_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount input output output',
  RawCodedTermShiftVariableRow M cutoff amount input output ->
  RawCodedTermShiftVariableRow M cutoff amount input output' ->
  output = output'.
Proof.
  intros M hPA cutoff amount input output output'
    (inputIndex & outputIndex & hinput & houtput & hshift)
    (inputIndex' & outputIndex' & hinput' & houtput' & hshift').
  assert (hinputIndex : inputIndex = inputIndex').
  {
    unfold rawTermVarCode in hinput, hinput'.
    destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
      _ _ _ _ (eq_trans (eq_sym hinput) hinput')) as [_ hindex].
    exact hindex.
  }
  subst inputIndex'.
  pose proof (raw_shiftedIndex_functional M hPA
    cutoff amount inputIndex outputIndex outputIndex' hshift hshift')
    as houtputIndex.
  subst outputIndex'. congruence.
Qed.

(** A child row can be rerooted without copying either beta table. *)
Lemma raw_codedTermShiftTrace_reroot : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount sourceCode sourceStep targetCode targetStep
      bound rootIndex input output,
  RawCodedTermShiftTrace M cutoff amount
    sourceCode sourceStep targetCode targetStep
    bound rootIndex input output ->
  forall childIndex childInput childOutput,
  rawLt M childIndex rootIndex ->
  RawCodedTermOperationPairLookup M
    sourceCode sourceStep targetCode targetStep
    childIndex childInput childOutput ->
  RawCodedTermShiftTrace M cutoff amount
    sourceCode sourceStep targetCode targetStep
    bound childIndex childInput childOutput.
Proof.
  intros M hPA cutoff amount sourceCode sourceStep targetCode targetStep
    bound rootIndex input output htrace
    childIndex childInput childOutput hchild hlookup.
  destruct htrace as
    (hsource & htarget & hroot & hrootLookup & hrows & hcutoff).
  split; [exact hsource |].
  split; [exact htarget |].
  split.
  - exact (raw_assignment_lt_trans M hPA
      childIndex rootIndex bound hchild hroot).
  - split; [exact hlookup |].
    split; [exact hrows | exact hcutoff].
Qed.

Corollary raw_codedTermShift_reroot : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount sourceCode sourceStep targetCode targetStep
      bound rootIndex input output,
  RawCodedTermShiftTrace M cutoff amount
    sourceCode sourceStep targetCode targetStep
    bound rootIndex input output ->
  forall childIndex childInput childOutput,
  rawLt M childIndex rootIndex ->
  RawCodedTermOperationPairLookup M
    sourceCode sourceStep targetCode targetStep
    childIndex childInput childOutput ->
  RawCodedTermShift M cutoff amount childInput childOutput.
Proof.
  intros M hPA cutoff amount sourceCode sourceStep targetCode targetStep
    bound rootIndex input output htrace
    childIndex childInput childOutput hchild hlookup.
  exists sourceCode, sourceStep, targetCode, targetStep, bound, childIndex.
  exact (raw_codedTermShiftTrace_reroot M hPA
    cutoff amount sourceCode sourceStep targetCode targetStep
    bound rootIndex input output htrace
    childIndex childInput childOutput hchild hlookup).
Qed.

(** ------------------------------------------------------------------
    PA-definable induction invariant for shift functionality. *)

Definition RawCodedTermShiftIndexFunctionalBelow
    (M : RawPAModel) (current : M) : Prop :=
  forall cutoff amount sourceCode sourceStep targetCode targetStep
      bound rootIndex input output otherOutput : M,
    rawLt M rootIndex current ->
    RawCodedTermShiftTrace M cutoff amount
      sourceCode sourceStep targetCode targetStep
      bound rootIndex input output ->
    RawCodedTermShift M cutoff amount input otherOutput ->
    output = otherOutput.

Arguments RawCodedTermShiftIndexFunctionalBelow M current
  : clear implicits.

Definition termOperationAll11 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll
    (pAll (pAll (pAll (pAll (pAll body)))))))))).

(** The eleven binders are, from outermost to innermost,

      cutoff, amount, sourceCode, sourceStep, targetCode, targetStep,
      bound, rootIndex, input, output, otherOutput.

    They therefore occupy variables 10 down to 0 in the body. *)
Definition codedTermShiftIndexFunctionalBelowTermAt
    (current : term) : formula :=
  termOperationAll11
    (pImp
      (Formula.ltTermAt (tVar 3) (liftTerm 11 current))
      (pImp
        (codedTermShiftTraceTermAt
          (tVar 10) (tVar 9) (tVar 8) (tVar 7) (tVar 6)
          (tVar 5) (tVar 4) (tVar 3) (tVar 2) (tVar 1))
        (pImp
          (codedTermShiftTermAt
            (tVar 10) (tVar 9) (tVar 2) (tVar 0))
          (pEq (tVar 1) (tVar 0))))).

Lemma raw_termOperation_eval_liftTerm_eleven : forall
    (M : RawPAModel) a b c d f g h i j k l
    (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i
        (scons M j (scons M k (scons M l e)))))))))))
    (liftTerm 11 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i j k l e t.
  unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro x.
  replace (x + 11) with
    (S (S (S (S (S (S (S (S (S (S (S x))))))))))) by lia.
  reflexivity.
Qed.

Lemma raw_sat_codedTermShiftIndexFunctionalBelowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) current,
  raw_formula_sat M e
    (codedTermShiftIndexFunctionalBelowTermAt current) <->
  RawCodedTermShiftIndexFunctionalBelow M
    (raw_term_eval M e current).
Proof.
  intros M e current.
  unfold codedTermShiftIndexFunctionalBelowTermAt,
    termOperationAll11, RawCodedTermShiftIndexFunctionalBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermShiftTraceTermAt_iff.
  setoid_rewrite raw_sat_codedTermShiftTermAt_iff.
  repeat setoid_rewrite raw_termOperation_eval_liftTerm_eleven.
  cbn [raw_term_eval scons].
  split; intros h cutoff amount sourceCode sourceStep targetCode targetStep
    bound rootIndex input output otherOutput;
    exact (h cutoff amount sourceCode sourceStep targetCode targetStep
      bound rootIndex input output otherOutput).
Qed.

(** Constructor mismatches are impossible because raw syntax constructors
    are separated in every PA model.  This tactic is used only after the two
    rows have exposed their source-code equations. *)
Ltac raw_shift_row_mismatch M hPA left right :=
  let leftInput := fresh "leftInput" in
  let rightInput := fresh "rightInput" in
  lazymatch type of left with
  | RawCodedTermShiftVariableRow _ _ _ _ _ =>
      let ii := fresh "inputIndex" in
      let oi := fresh "outputIndex" in
      let hout := fresh "houtput" in
      let hs := fresh "hshift" in
      destruct left as (ii & oi & leftInput & hout & hs)
  | RawCodedTermOpeningVariableRow _ _ _ _ _ =>
      let ii := fresh "inputIndex" in
      let hcases := fresh "hcases" in
      destruct left as (ii & leftInput & hcases)
  | RawCodedTermZeroOperationRow _ _ _ =>
      let hout := fresh "houtput" in
      destruct left as [leftInput hout]
  | RawCodedTermSuccOperationRow _ _ _ _ _ _ _ _ =>
      let ci := fresh "childIndex" in
      let cin := fresh "inputChild" in
      let cout := fresh "outputChild" in
      let hlt := fresh "hchildIndex" in
      let hlk := fresh "hchildLookup" in
      let hout := fresh "houtput" in
      destruct left as
        (ci & cin & cout & hlt & hlk & leftInput & hout)
  | RawCodedTermBinaryOperationRow _ _ _ _ _ _ _ _ _ =>
      let li := fresh "leftIndex" in
      let lin := fresh "inputLeft" in
      let lout := fresh "outputLeft" in
      let ri := fresh "rightIndex" in
      let rin := fresh "inputRight" in
      let rout := fresh "outputRight" in
      let hli := fresh "hleftIndex" in
      let hll := fresh "hleftLookup" in
      let hri := fresh "hrightIndex" in
      let hrl := fresh "hrightLookup" in
      let hout := fresh "houtput" in
      destruct left as
        (li & lin & lout & ri & rin & rout & hli & hll & hri & hrl &
         leftInput & hout)
  end;
  lazymatch type of right with
  | RawCodedTermShiftVariableRow _ _ _ _ _ =>
      let ii := fresh "inputIndex" in
      let oi := fresh "outputIndex" in
      let hout := fresh "houtput" in
      let hs := fresh "hshift" in
      destruct right as (ii & oi & rightInput & hout & hs)
  | RawCodedTermOpeningVariableRow _ _ _ _ _ =>
      let ii := fresh "inputIndex" in
      let hcases := fresh "hcases" in
      destruct right as (ii & rightInput & hcases)
  | RawCodedTermZeroOperationRow _ _ _ =>
      let hout := fresh "houtput" in
      destruct right as [rightInput hout]
  | RawCodedTermSuccOperationRow _ _ _ _ _ _ _ _ =>
      let ci := fresh "childIndex" in
      let cin := fresh "inputChild" in
      let cout := fresh "outputChild" in
      let hlt := fresh "hchildIndex" in
      let hlk := fresh "hchildLookup" in
      let hout := fresh "houtput" in
      destruct right as
        (ci & cin & cout & hlt & hlk & rightInput & hout)
  | RawCodedTermBinaryOperationRow _ _ _ _ _ _ _ _ _ =>
      let li := fresh "leftIndex" in
      let lin := fresh "inputLeft" in
      let lout := fresh "outputLeft" in
      let ri := fresh "rightIndex" in
      let rin := fresh "inputRight" in
      let rout := fresh "outputRight" in
      let hli := fresh "hleftIndex" in
      let hll := fresh "hleftLookup" in
      let hri := fresh "hrightIndex" in
      let hrl := fresh "hrightLookup" in
      let hout := fresh "houtput" in
      destruct right as
        (li & lin & lout & ri & rin & rout & hli & hll & hri & hrl &
         rightInput & hout)
  end;
  let hshape := fresh "hshape" in
  assert (hshape := eq_trans (eq_sym leftInput) rightInput);
  exfalso; raw_standard_term_shape_contradiction M hPA hshape.

Theorem raw_codedTermShiftIndexFunctionalBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedTermShiftIndexFunctionalBelow M current ->
  RawCodedTermShiftIndexFunctionalBelow M (raw_succ M current).
Proof.
  intros M hPA current hcurrent cutoff amount
    sourceCode sourceStep targetCode targetStep bound rootIndex
    input output otherOutput hrootIndex hleftTrace hrightOperation.
  destruct (raw_lt_succ_cases M hPA rootIndex current hrootIndex)
    as [hbefore | hrootCurrent].
  - exact (hcurrent cutoff amount sourceCode sourceStep
      targetCode targetStep bound rootIndex input output otherOutput
      hbefore hleftTrace hrightOperation).
  - subst rootIndex.
    destruct hrightOperation as
      (rightSourceCode & rightSourceStep & rightTargetCode &
       rightTargetStep & rightBound & rightRootIndex & hrightTrace).
    pose proof hleftTrace as hleftFacts.
    pose proof hrightTrace as hrightFacts.
    destruct hleftFacts as
      (_ & _ & hleftRoot & hleftLookup & hleftRows & _).
    destruct hrightFacts as
      (_ & _ & hrightRoot & hrightLookup & hrightRows & _).
    pose proof (hleftRows current input output hleftRoot hleftLookup)
      as hleftRow.
    pose proof (hrightRows rightRootIndex input otherOutput
      hrightRoot hrightLookup) as hrightRow.
    unfold RawCodedTermShiftTraversalRow,
      RawCodedTermOperationTraversalRow in hleftRow, hrightRow.
    destruct hleftRow as
      [ hleftVar
      | [ hleftZero
        | [ hleftSucc
          | [ hleftAdd | hleftMul ] ] ] ];
    destruct hrightRow as
      [ hrightVar
      | [ hrightZero
        | [ hrightSucc
          | [ hrightAdd | hrightMul ] ] ] ].
  + exact (raw_codedTermShiftVariableRow_functional M hPA
      cutoff amount input output otherOutput hleftVar hrightVar).
  + raw_shift_row_mismatch M hPA hleftVar hrightZero.
  + raw_shift_row_mismatch M hPA hleftVar hrightSucc.
  + raw_shift_row_mismatch M hPA hleftVar hrightAdd.
  + raw_shift_row_mismatch M hPA hleftVar hrightMul.
  + raw_shift_row_mismatch M hPA hleftZero hrightVar.
  + destruct hleftZero as [_ ->]. destruct hrightZero as [_ ->].
    reflexivity.
  + raw_shift_row_mismatch M hPA hleftZero hrightSucc.
  + raw_shift_row_mismatch M hPA hleftZero hrightAdd.
  + raw_shift_row_mismatch M hPA hleftZero hrightMul.
  + raw_shift_row_mismatch M hPA hleftSucc hrightVar.
  + raw_shift_row_mismatch M hPA hleftSucc hrightZero.
  + destruct hleftSucc as
      (leftChildIndex & leftInputChild & leftOutputChild &
       hleftChildIndex & hleftChildLookup & hleftInput & hleftOutput).
    destruct hrightSucc as
      (rightChildIndex & rightInputChild & rightOutputChild &
       hrightChildIndex & hrightChildLookup & hrightInput & hrightOutput).
    assert (hinputChild : leftInputChild = rightInputChild).
    {
      unfold rawTermSuccCode in hleftInput, hrightInput.
      destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
        _ _ _ _ (eq_trans (eq_sym hleftInput) hrightInput))
        as [_ hchild]. exact hchild.
    }
    subst rightInputChild.
    assert (houtputChild : leftOutputChild = rightOutputChild).
    {
      apply (hcurrent cutoff amount sourceCode sourceStep
        targetCode targetStep bound leftChildIndex
        leftInputChild leftOutputChild rightOutputChild hleftChildIndex).
      - exact (raw_codedTermShiftTrace_reroot M hPA
          cutoff amount sourceCode sourceStep targetCode targetStep
          bound current input output hleftTrace
          leftChildIndex leftInputChild leftOutputChild
          hleftChildIndex hleftChildLookup).
      - exact (raw_codedTermShift_reroot M hPA
          cutoff amount rightSourceCode rightSourceStep
          rightTargetCode rightTargetStep rightBound rightRootIndex
          input otherOutput hrightTrace
          rightChildIndex leftInputChild rightOutputChild
          hrightChildIndex hrightChildLookup).
    }
    rewrite hleftOutput, hrightOutput, houtputChild. reflexivity.
  + raw_shift_row_mismatch M hPA hleftSucc hrightAdd.
  + raw_shift_row_mismatch M hPA hleftSucc hrightMul.
  + raw_shift_row_mismatch M hPA hleftAdd hrightVar.
  + raw_shift_row_mismatch M hPA hleftAdd hrightZero.
  + raw_shift_row_mismatch M hPA hleftAdd hrightSucc.
  + destruct hleftAdd as
      (leftLeftIndex & leftInputLeft & leftOutputLeft &
       leftRightIndex & leftInputRight & leftOutputRight &
       hleftLeftIndex & hleftLeftLookup &
       hleftRightIndex & hleftRightLookup & hleftInput & hleftOutput).
    destruct hrightAdd as
      (rightLeftIndex & rightInputLeft & rightOutputLeft &
       rightRightIndex & rightInputRight & rightOutputRight &
       hrightLeftIndex & hrightLeftLookup &
       hrightRightIndex & hrightRightLookup & hrightInput & hrightOutput).
    assert (hinputs : leftInputLeft = rightInputLeft /\
        leftInputRight = rightInputRight).
    {
      unfold rawTermAddCode in hleftInput, hrightInput.
      destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
        _ _ _ _ _ _ (eq_trans (eq_sym hleftInput) hrightInput))
        as [_ [hleft hright]]. split; assumption.
    }
    destruct hinputs as [-> ->].
    assert (hleftOutputChild : leftOutputLeft = rightOutputLeft).
    {
      apply (hcurrent cutoff amount sourceCode sourceStep
        targetCode targetStep bound leftLeftIndex
        rightInputLeft leftOutputLeft rightOutputLeft hleftLeftIndex).
      - exact (raw_codedTermShiftTrace_reroot M hPA
          cutoff amount sourceCode sourceStep targetCode targetStep
          bound current input output hleftTrace
          leftLeftIndex rightInputLeft leftOutputLeft
          hleftLeftIndex hleftLeftLookup).
      - exact (raw_codedTermShift_reroot M hPA
          cutoff amount rightSourceCode rightSourceStep
          rightTargetCode rightTargetStep rightBound rightRootIndex
          input otherOutput hrightTrace
          rightLeftIndex rightInputLeft rightOutputLeft
          hrightLeftIndex hrightLeftLookup).
    }
    assert (hrightOutputChild : leftOutputRight = rightOutputRight).
    {
      apply (hcurrent cutoff amount sourceCode sourceStep
        targetCode targetStep bound leftRightIndex
        rightInputRight leftOutputRight rightOutputRight hleftRightIndex).
      - exact (raw_codedTermShiftTrace_reroot M hPA
          cutoff amount sourceCode sourceStep targetCode targetStep
          bound current input output hleftTrace
          leftRightIndex rightInputRight leftOutputRight
          hleftRightIndex hleftRightLookup).
      - exact (raw_codedTermShift_reroot M hPA
          cutoff amount rightSourceCode rightSourceStep
          rightTargetCode rightTargetStep rightBound rightRootIndex
          input otherOutput hrightTrace
          rightRightIndex rightInputRight rightOutputRight
          hrightRightIndex hrightRightLookup).
    }
    rewrite hleftOutput, hrightOutput,
      hleftOutputChild, hrightOutputChild. reflexivity.
  + raw_shift_row_mismatch M hPA hleftAdd hrightMul.
  + raw_shift_row_mismatch M hPA hleftMul hrightVar.
  + raw_shift_row_mismatch M hPA hleftMul hrightZero.
  + raw_shift_row_mismatch M hPA hleftMul hrightSucc.
  + raw_shift_row_mismatch M hPA hleftMul hrightAdd.
  + destruct hleftMul as
      (leftLeftIndex & leftInputLeft & leftOutputLeft &
       leftRightIndex & leftInputRight & leftOutputRight &
       hleftLeftIndex & hleftLeftLookup &
       hleftRightIndex & hleftRightLookup & hleftInput & hleftOutput).
    destruct hrightMul as
      (rightLeftIndex & rightInputLeft & rightOutputLeft &
       rightRightIndex & rightInputRight & rightOutputRight &
       hrightLeftIndex & hrightLeftLookup &
       hrightRightIndex & hrightRightLookup & hrightInput & hrightOutput).
    assert (hinputs : leftInputLeft = rightInputLeft /\
        leftInputRight = rightInputRight).
    {
      unfold rawTermMulCode in hleftInput, hrightInput.
      destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
        _ _ _ _ _ _ (eq_trans (eq_sym hleftInput) hrightInput))
        as [_ [hleft hright]]. split; assumption.
    }
    destruct hinputs as [-> ->].
    assert (hleftOutputChild : leftOutputLeft = rightOutputLeft).
    {
      apply (hcurrent cutoff amount sourceCode sourceStep
        targetCode targetStep bound leftLeftIndex
        rightInputLeft leftOutputLeft rightOutputLeft hleftLeftIndex).
      - exact (raw_codedTermShiftTrace_reroot M hPA
          cutoff amount sourceCode sourceStep targetCode targetStep
          bound current input output hleftTrace
          leftLeftIndex rightInputLeft leftOutputLeft
          hleftLeftIndex hleftLeftLookup).
      - exact (raw_codedTermShift_reroot M hPA
          cutoff amount rightSourceCode rightSourceStep
          rightTargetCode rightTargetStep rightBound rightRootIndex
          input otherOutput hrightTrace
          rightLeftIndex rightInputLeft rightOutputLeft
          hrightLeftIndex hrightLeftLookup).
    }
    assert (hrightOutputChild : leftOutputRight = rightOutputRight).
    {
      apply (hcurrent cutoff amount sourceCode sourceStep
        targetCode targetStep bound leftRightIndex
        rightInputRight leftOutputRight rightOutputRight hleftRightIndex).
      - exact (raw_codedTermShiftTrace_reroot M hPA
          cutoff amount sourceCode sourceStep targetCode targetStep
          bound current input output hleftTrace
          leftRightIndex rightInputRight leftOutputRight
          hleftRightIndex hleftRightLookup).
      - exact (raw_codedTermShift_reroot M hPA
          cutoff amount rightSourceCode rightSourceStep
          rightTargetCode rightTargetStep rightBound rightRootIndex
          input otherOutput hrightTrace
          rightRightIndex rightInputRight rightOutputRight
          hrightRightIndex hrightRightLookup).
    }
    rewrite hleftOutput, hrightOutput,
      hleftOutputChild, hrightOutputChild. reflexivity.
Qed.

Theorem raw_codedTermShiftIndexFunctionalBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedTermShiftIndexFunctionalBelow M current.
Proof.
  intros M hPA.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := codedTermShiftIndexFunctionalBelowTermAt (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedTermShiftIndexFunctionalBelowTermAt_iff M
          (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      intros cutoff amount sourceCode sourceStep targetCode targetStep
        bound rootIndex input output otherOutput hrootIndex.
      exfalso. exact (raw_not_lt_zero M hPA rootIndex hrootIndex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_codedTermShiftIndexFunctionalBelowTermAt_iff M
          (scons M current parameterEnv) (tVar 0)) hcurrent) as hraw.
      apply (proj2
        (raw_sat_codedTermShiftIndexFunctionalBelowTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hraw |- *.
      exact (raw_codedTermShiftIndexFunctionalBelow_succ
        M hPA current hraw).
  }
  intro current.
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedTermShiftIndexFunctionalBelowTermAt_iff M
      (scons M current parameterEnv) (tVar 0)) (hall current)) as hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

(** Main cross-certificate theorem for arbitrary, possibly nonstandard,
    term codes. *)
Theorem raw_codedTermShift_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount input output output',
  RawCodedTermShift M cutoff amount input output ->
  RawCodedTermShift M cutoff amount input output' ->
  output = output'.
Proof.
  intros M hPA cutoff amount input output output'
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & hleftTrace) hright.
  exact (raw_codedTermShiftIndexFunctionalBelow_all M hPA
    (raw_succ M rootIndex)
    cutoff amount sourceCode sourceStep targetCode targetStep
    bound rootIndex input output output'
    (raw_assignment_lt_self_succ M hPA rootIndex)
    hleftTrace hright).
Qed.

(** ------------------------------------------------------------------
    Opening has the same recursive rows, but a three-way variable case. *)

Lemma raw_codedTermOpeningVariableRow_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement input output output',
  RawCodedTermOpeningVariableRow M
    cutoff liftedReplacement input output ->
  RawCodedTermOpeningVariableRow M
    cutoff liftedReplacement input output' ->
  output = output'.
Proof.
  intros M hPA cutoff liftedReplacement input output output'
    (inputIndex & hinput & hleft)
    (inputIndex' & hinput' & hright).
  assert (hinputIndex : inputIndex = inputIndex').
  {
    unfold rawTermVarCode in hinput, hinput'.
    destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
      _ _ _ _ (eq_trans (eq_sym hinput) hinput')) as [_ hindex].
    exact hindex.
  }
  subst inputIndex'.
  destruct hleft as
    [ [hleftBelow hleftOutput]
    | [ [hleftAt hleftOutput]
      | (leftPredecessor & hleftSucc & hleftAbove & hleftOutput) ] ];
  destruct hright as
    [ [hrightBelow hrightOutput]
    | [ [hrightAt hrightOutput]
      | (rightPredecessor & hrightSucc & hrightAbove & hrightOutput) ] ].
  - congruence.
  - subst cutoff. exfalso.
    exact (raw_not_lt_self M hPA inputIndex hleftBelow).
  - exfalso. apply (raw_not_lt_self M hPA inputIndex).
    exact (raw_assignment_lt_trans M hPA
      inputIndex cutoff inputIndex hleftBelow hrightAbove).
  - subst cutoff. exfalso.
    exact (raw_not_lt_self M hPA inputIndex hrightBelow).
  - congruence.
  - subst cutoff. exfalso.
    exact (raw_not_lt_self M hPA inputIndex hrightAbove).
  - exfalso. apply (raw_not_lt_self M hPA inputIndex).
    exact (raw_assignment_lt_trans M hPA
      inputIndex cutoff inputIndex hrightBelow hleftAbove).
  - subst cutoff. exfalso.
    exact (raw_not_lt_self M hPA inputIndex hleftAbove).
  - assert (hpredecessor : leftPredecessor = rightPredecessor).
    {
      apply (raw_succ_injective_syntax M hPA).
      exact (eq_trans (eq_sym hleftSucc) hrightSucc).
    }
    subst rightPredecessor. congruence.
Qed.

Lemma raw_codedTermOpeningTrace_reroot : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
      bound rootIndex input output,
  RawCodedTermOpeningTrace M cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep
    bound rootIndex input output ->
  forall childIndex childInput childOutput,
  rawLt M childIndex rootIndex ->
  RawCodedTermOperationPairLookup M
    sourceCode sourceStep targetCode targetStep
    childIndex childInput childOutput ->
  RawCodedTermOpeningTrace M cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep
    bound childIndex childInput childOutput.
Proof.
  intros M hPA cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep
    bound rootIndex input output htrace
    childIndex childInput childOutput hchild hlookup.
  destruct htrace as
    (hsource & htarget & hroot & hrootLookup & hrows).
  split; [exact hsource |].
  split; [exact htarget |].
  split.
  - exact (raw_assignment_lt_trans M hPA
      childIndex rootIndex bound hchild hroot).
  - split; [exact hlookup | exact hrows].
Qed.

Corollary raw_codedTermOpening_reroot : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
      bound rootIndex input output,
  RawCodedTermOpeningTrace M cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep
    bound rootIndex input output ->
  forall childIndex childInput childOutput,
  rawLt M childIndex rootIndex ->
  RawCodedTermOperationPairLookup M
    sourceCode sourceStep targetCode targetStep
    childIndex childInput childOutput ->
  RawCodedTermOpening M cutoff liftedReplacement childInput childOutput.
Proof.
  intros M hPA cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep
    bound rootIndex input output htrace
    childIndex childInput childOutput hchild hlookup.
  exists sourceCode, sourceStep, targetCode, targetStep, bound, childIndex.
  exact (raw_codedTermOpeningTrace_reroot M hPA
    cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
    bound rootIndex input output htrace
    childIndex childInput childOutput hchild hlookup).
Qed.

Definition RawCodedTermOpeningIndexFunctionalBelow
    (M : RawPAModel) (current : M) : Prop :=
  forall cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep
      bound rootIndex input output otherOutput : M,
    rawLt M rootIndex current ->
    RawCodedTermOpeningTrace M cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep
      bound rootIndex input output ->
    RawCodedTermOpening M cutoff liftedReplacement input otherOutput ->
    output = otherOutput.

Arguments RawCodedTermOpeningIndexFunctionalBelow M current
  : clear implicits.

Definition codedTermOpeningIndexFunctionalBelowTermAt
    (current : term) : formula :=
  termOperationAll11
    (pImp
      (Formula.ltTermAt (tVar 3) (liftTerm 11 current))
      (pImp
        (codedTermOpeningTraceTermAt
          (tVar 10) (tVar 9) (tVar 8) (tVar 7) (tVar 6)
          (tVar 5) (tVar 4) (tVar 3) (tVar 2) (tVar 1))
        (pImp
          (codedTermOpeningTermAt
            (tVar 10) (tVar 9) (tVar 2) (tVar 0))
          (pEq (tVar 1) (tVar 0))))).

Lemma raw_sat_codedTermOpeningIndexFunctionalBelowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) current,
  raw_formula_sat M e
    (codedTermOpeningIndexFunctionalBelowTermAt current) <->
  RawCodedTermOpeningIndexFunctionalBelow M
    (raw_term_eval M e current).
Proof.
  intros M e current.
  unfold codedTermOpeningIndexFunctionalBelowTermAt,
    termOperationAll11, RawCodedTermOpeningIndexFunctionalBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOpeningTraceTermAt_iff.
  setoid_rewrite raw_sat_codedTermOpeningTermAt_iff.
  repeat setoid_rewrite raw_termOperation_eval_liftTerm_eleven.
  cbn [raw_term_eval scons].
  split; intros h cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep
    bound rootIndex input output otherOutput;
    exact (h cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep
      bound rootIndex input output otherOutput).
Qed.

Theorem raw_codedTermOpeningIndexFunctionalBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedTermOpeningIndexFunctionalBelow M current ->
  RawCodedTermOpeningIndexFunctionalBelow M (raw_succ M current).
Proof.
  intros M hPA current hcurrent cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep bound rootIndex
    input output otherOutput hrootIndex hleftTrace hrightOperation.
  destruct (raw_lt_succ_cases M hPA rootIndex current hrootIndex)
    as [hbefore | hrootCurrent].
  - exact (hcurrent cutoff liftedReplacement sourceCode sourceStep
      targetCode targetStep bound rootIndex input output otherOutput
      hbefore hleftTrace hrightOperation).
  - subst rootIndex.
    destruct hrightOperation as
      (rightSourceCode & rightSourceStep & rightTargetCode &
       rightTargetStep & rightBound & rightRootIndex & hrightTrace).
    pose proof hleftTrace as hleftFacts.
    pose proof hrightTrace as hrightFacts.
    destruct hleftFacts as
      (_ & _ & hleftRoot & hleftLookup & hleftRows).
    destruct hrightFacts as
      (_ & _ & hrightRoot & hrightLookup & hrightRows).
    pose proof (hleftRows current input output hleftRoot hleftLookup)
      as hleftRow.
    pose proof (hrightRows rightRootIndex input otherOutput
      hrightRoot hrightLookup) as hrightRow.
    unfold RawCodedTermOpeningTraversalRow,
      RawCodedTermOperationTraversalRow in hleftRow, hrightRow.
    destruct hleftRow as
      [ hleftVar
      | [ hleftZero
        | [ hleftSucc
          | [ hleftAdd | hleftMul ] ] ] ];
    destruct hrightRow as
      [ hrightVar
      | [ hrightZero
        | [ hrightSucc
          | [ hrightAdd | hrightMul ] ] ] ].
  + exact (raw_codedTermOpeningVariableRow_functional M hPA
      cutoff liftedReplacement input output otherOutput hleftVar hrightVar).
  + raw_shift_row_mismatch M hPA hleftVar hrightZero.
  + raw_shift_row_mismatch M hPA hleftVar hrightSucc.
  + raw_shift_row_mismatch M hPA hleftVar hrightAdd.
  + raw_shift_row_mismatch M hPA hleftVar hrightMul.
  + raw_shift_row_mismatch M hPA hleftZero hrightVar.
  + destruct hleftZero as [_ ->]. destruct hrightZero as [_ ->].
    reflexivity.
  + raw_shift_row_mismatch M hPA hleftZero hrightSucc.
  + raw_shift_row_mismatch M hPA hleftZero hrightAdd.
  + raw_shift_row_mismatch M hPA hleftZero hrightMul.
  + raw_shift_row_mismatch M hPA hleftSucc hrightVar.
  + raw_shift_row_mismatch M hPA hleftSucc hrightZero.
  + destruct hleftSucc as
      (leftChildIndex & leftInputChild & leftOutputChild &
       hleftChildIndex & hleftChildLookup & hleftInput & hleftOutput).
    destruct hrightSucc as
      (rightChildIndex & rightInputChild & rightOutputChild &
       hrightChildIndex & hrightChildLookup & hrightInput & hrightOutput).
    assert (hinputChild : leftInputChild = rightInputChild).
    {
      unfold rawTermSuccCode in hleftInput, hrightInput.
      destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
        _ _ _ _ (eq_trans (eq_sym hleftInput) hrightInput))
        as [_ hchild]. exact hchild.
    }
    subst rightInputChild.
    assert (houtputChild : leftOutputChild = rightOutputChild).
    {
      apply (hcurrent cutoff liftedReplacement sourceCode sourceStep
        targetCode targetStep bound leftChildIndex
        leftInputChild leftOutputChild rightOutputChild hleftChildIndex).
      - exact (raw_codedTermOpeningTrace_reroot M hPA
          cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
          bound current input output hleftTrace
          leftChildIndex leftInputChild leftOutputChild
          hleftChildIndex hleftChildLookup).
      - exact (raw_codedTermOpening_reroot M hPA
          cutoff liftedReplacement rightSourceCode rightSourceStep
          rightTargetCode rightTargetStep rightBound rightRootIndex
          input otherOutput hrightTrace
          rightChildIndex leftInputChild rightOutputChild
          hrightChildIndex hrightChildLookup).
    }
    rewrite hleftOutput, hrightOutput, houtputChild. reflexivity.
  + raw_shift_row_mismatch M hPA hleftSucc hrightAdd.
  + raw_shift_row_mismatch M hPA hleftSucc hrightMul.
  + raw_shift_row_mismatch M hPA hleftAdd hrightVar.
  + raw_shift_row_mismatch M hPA hleftAdd hrightZero.
  + raw_shift_row_mismatch M hPA hleftAdd hrightSucc.
  + destruct hleftAdd as
      (leftLeftIndex & leftInputLeft & leftOutputLeft &
       leftRightIndex & leftInputRight & leftOutputRight &
       hleftLeftIndex & hleftLeftLookup &
       hleftRightIndex & hleftRightLookup & hleftInput & hleftOutput).
    destruct hrightAdd as
      (rightLeftIndex & rightInputLeft & rightOutputLeft &
       rightRightIndex & rightInputRight & rightOutputRight &
       hrightLeftIndex & hrightLeftLookup &
       hrightRightIndex & hrightRightLookup & hrightInput & hrightOutput).
    assert (hinputs : leftInputLeft = rightInputLeft /\
        leftInputRight = rightInputRight).
    {
      unfold rawTermAddCode in hleftInput, hrightInput.
      destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
        _ _ _ _ _ _ (eq_trans (eq_sym hleftInput) hrightInput))
        as [_ [hleft hright]]. split; assumption.
    }
    destruct hinputs as [-> ->].
    assert (hleftOutputChild : leftOutputLeft = rightOutputLeft).
    {
      apply (hcurrent cutoff liftedReplacement sourceCode sourceStep
        targetCode targetStep bound leftLeftIndex
        rightInputLeft leftOutputLeft rightOutputLeft hleftLeftIndex).
      - exact (raw_codedTermOpeningTrace_reroot M hPA
          cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
          bound current input output hleftTrace
          leftLeftIndex rightInputLeft leftOutputLeft
          hleftLeftIndex hleftLeftLookup).
      - exact (raw_codedTermOpening_reroot M hPA
          cutoff liftedReplacement rightSourceCode rightSourceStep
          rightTargetCode rightTargetStep rightBound rightRootIndex
          input otherOutput hrightTrace
          rightLeftIndex rightInputLeft rightOutputLeft
          hrightLeftIndex hrightLeftLookup).
    }
    assert (hrightOutputChild : leftOutputRight = rightOutputRight).
    {
      apply (hcurrent cutoff liftedReplacement sourceCode sourceStep
        targetCode targetStep bound leftRightIndex
        rightInputRight leftOutputRight rightOutputRight hleftRightIndex).
      - exact (raw_codedTermOpeningTrace_reroot M hPA
          cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
          bound current input output hleftTrace
          leftRightIndex rightInputRight leftOutputRight
          hleftRightIndex hleftRightLookup).
      - exact (raw_codedTermOpening_reroot M hPA
          cutoff liftedReplacement rightSourceCode rightSourceStep
          rightTargetCode rightTargetStep rightBound rightRootIndex
          input otherOutput hrightTrace
          rightRightIndex rightInputRight rightOutputRight
          hrightRightIndex hrightRightLookup).
    }
    rewrite hleftOutput, hrightOutput,
      hleftOutputChild, hrightOutputChild. reflexivity.
  + raw_shift_row_mismatch M hPA hleftAdd hrightMul.
  + raw_shift_row_mismatch M hPA hleftMul hrightVar.
  + raw_shift_row_mismatch M hPA hleftMul hrightZero.
  + raw_shift_row_mismatch M hPA hleftMul hrightSucc.
  + raw_shift_row_mismatch M hPA hleftMul hrightAdd.
  + destruct hleftMul as
      (leftLeftIndex & leftInputLeft & leftOutputLeft &
       leftRightIndex & leftInputRight & leftOutputRight &
       hleftLeftIndex & hleftLeftLookup &
       hleftRightIndex & hleftRightLookup & hleftInput & hleftOutput).
    destruct hrightMul as
      (rightLeftIndex & rightInputLeft & rightOutputLeft &
       rightRightIndex & rightInputRight & rightOutputRight &
       hrightLeftIndex & hrightLeftLookup &
       hrightRightIndex & hrightRightLookup & hrightInput & hrightOutput).
    assert (hinputs : leftInputLeft = rightInputLeft /\
        leftInputRight = rightInputRight).
    {
      unfold rawTermMulCode in hleftInput, hrightInput.
      destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
        _ _ _ _ _ _ (eq_trans (eq_sym hleftInput) hrightInput))
        as [_ [hleft hright]]. split; assumption.
    }
    destruct hinputs as [-> ->].
    assert (hleftOutputChild : leftOutputLeft = rightOutputLeft).
    {
      apply (hcurrent cutoff liftedReplacement sourceCode sourceStep
        targetCode targetStep bound leftLeftIndex
        rightInputLeft leftOutputLeft rightOutputLeft hleftLeftIndex).
      - exact (raw_codedTermOpeningTrace_reroot M hPA
          cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
          bound current input output hleftTrace
          leftLeftIndex rightInputLeft leftOutputLeft
          hleftLeftIndex hleftLeftLookup).
      - exact (raw_codedTermOpening_reroot M hPA
          cutoff liftedReplacement rightSourceCode rightSourceStep
          rightTargetCode rightTargetStep rightBound rightRootIndex
          input otherOutput hrightTrace
          rightLeftIndex rightInputLeft rightOutputLeft
          hrightLeftIndex hrightLeftLookup).
    }
    assert (hrightOutputChild : leftOutputRight = rightOutputRight).
    {
      apply (hcurrent cutoff liftedReplacement sourceCode sourceStep
        targetCode targetStep bound leftRightIndex
        rightInputRight leftOutputRight rightOutputRight hleftRightIndex).
      - exact (raw_codedTermOpeningTrace_reroot M hPA
          cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
          bound current input output hleftTrace
          leftRightIndex rightInputRight leftOutputRight
          hleftRightIndex hleftRightLookup).
      - exact (raw_codedTermOpening_reroot M hPA
          cutoff liftedReplacement rightSourceCode rightSourceStep
          rightTargetCode rightTargetStep rightBound rightRootIndex
          input otherOutput hrightTrace
          rightRightIndex rightInputRight rightOutputRight
          hrightRightIndex hrightRightLookup).
    }
    rewrite hleftOutput, hrightOutput,
      hleftOutputChild, hrightOutputChild. reflexivity.
Qed.

Theorem raw_codedTermOpeningIndexFunctionalBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedTermOpeningIndexFunctionalBelow M current.
Proof.
  intros M hPA.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := codedTermOpeningIndexFunctionalBelowTermAt (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedTermOpeningIndexFunctionalBelowTermAt_iff M
          (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      intros cutoff liftedReplacement
        sourceCode sourceStep targetCode targetStep
        bound rootIndex input output otherOutput hrootIndex.
      exfalso. exact (raw_not_lt_zero M hPA rootIndex hrootIndex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_codedTermOpeningIndexFunctionalBelowTermAt_iff M
          (scons M current parameterEnv) (tVar 0)) hcurrent) as hraw.
      apply (proj2
        (raw_sat_codedTermOpeningIndexFunctionalBelowTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hraw |- *.
      exact (raw_codedTermOpeningIndexFunctionalBelow_succ
        M hPA current hraw).
  }
  intro current.
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedTermOpeningIndexFunctionalBelowTermAt_iff M
      (scons M current parameterEnv) (tVar 0)) (hall current)) as hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

Theorem raw_codedTermOpening_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement input output output',
  RawCodedTermOpening M cutoff liftedReplacement input output ->
  RawCodedTermOpening M cutoff liftedReplacement input output' ->
  output = output'.
Proof.
  intros M hPA cutoff liftedReplacement input output output'
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & hleftTrace) hright.
  exact (raw_codedTermOpeningIndexFunctionalBelow_all M hPA
    (raw_succ M rootIndex)
    cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
    bound rootIndex input output output'
    (raw_assignment_lt_self_succ M hPA rootIndex)
    hleftTrace hright).
Qed.

(** Functionality of the two atom relations used by formula traversals. *)
Definition RawCodedFormulaOperationAtomFunctional
    (M : RawPAModel) (atom : M -> M -> M -> M -> Prop) : Prop :=
  forall parameter depth input output output',
    atom parameter depth input output ->
    atom parameter depth input output' ->
    output = output'.

Arguments RawCodedFormulaOperationAtomFunctional M atom
  : clear implicits.

Corollary raw_codedFormulaShiftAtom_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaOperationAtomFunctional M
    (RawCodedFormulaShiftAtom M).
Proof.
  intros M hPA amount depth input output output'.
  apply raw_codedTermShift_functional. exact hPA.
Qed.

Corollary raw_codedFormulaSubstitutionAtom_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaOperationAtomFunctional M
    (RawCodedFormulaSubstitutionAtom M).
Proof.
  intros M hPA replacement depth input output output'
    (liftedReplacement & hleftShift & hleftOpening)
    (liftedReplacement' & hrightShift & hrightOpening).
  pose proof (raw_codedTermShift_functional M hPA
    (raw_zero M) depth replacement
    liftedReplacement liftedReplacement' hleftShift hrightShift)
    as hlifted.
  subst liftedReplacement'.
  exact (raw_codedTermOpening_functional M hPA
    depth liftedReplacement input output output'
    hleftOpening hrightOpening).
Qed.

End PABoundedRawCodedTermOperationCrossTraceFunctionality.
