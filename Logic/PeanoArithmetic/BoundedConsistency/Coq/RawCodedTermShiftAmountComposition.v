(**
  Composition of represented term shifts at a common cutoff.

  Shift traces may have nonstandard bounds and roots, so the structural
  proof is a PA-definable induction on the root index of the first trace.
  The second trace may use completely unrelated assignment tables.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity RawCodedAdditionLaws
  RawCodedAssignment RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation RawCodedFormulaOperations
  RawCodedProofDescent
  RawCodedFormulaShiftTotality RawCodedPAAxiomContextSelfShift
  RawCodedProofAtomicAdequacyStandard
  RawCodedTermOperationCrossTraceFunctionality
  RawCodedTermShiftProtection RawCodedTermOpeningShiftInterchange.

Module PABoundedRawCodedTermShiftAmountComposition.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAdditionLaws.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedTermOperationCrossTraceFunctionality.
Import PABoundedRawCodedTermShiftProtection.
Import PABoundedRawCodedTermOpeningShiftInterchange.

(** The index-level calculation is valid for nonstandard carrier-valued
    amounts. *)
Lemma raw_shiftedIndex_amount_composition : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff firstAmount secondAmount input middle output,
  RawShiftedIndex M cutoff firstAmount input middle ->
  RawShiftedIndex M cutoff secondAmount middle output ->
  RawShiftedIndex M cutoff (raw_add M firstAmount secondAmount)
    input output.
Proof.
  intros M hPA cutoff firstAmount secondAmount input middle output
    hfirst hsecond.
  destruct hfirst as [[hfirstLow ->] | [hfirstHigh ->]].
  - destruct hsecond as [[hsecondLow ->] | [hsecondHigh ->]].
    + left. split; [exact hfirstLow | reflexivity].
    + exfalso. apply (raw_not_lt_self M hPA input).
      exact (raw_lt_le_trans_pair M hPA
        input cutoff input hfirstLow hsecondHigh).
  - destruct hsecond as [[hsecondLow ->] | [hsecondHigh ->]].
    + assert (hcutoffMiddle : rawLe M cutoff
          (raw_add M input firstAmount)).
      {
        eapply raw_le_trans; [exact hPA | exact hfirstHigh |].
        exact (raw_proof_left_le_sum M input firstAmount).
      }
      exfalso. apply (raw_not_lt_self M hPA
        (raw_add M input firstAmount)).
      exact (raw_lt_le_trans_pair M hPA
        (raw_add M input firstAmount) cutoff
        (raw_add M input firstAmount) hsecondLow hcutoffMiddle).
    + right. split; [exact hfirstHigh |].
      rewrite raw_add_assoc by exact hPA. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Represented induction invariant. *)

Definition RawCodedTermShiftAmountCompositionIndexBelow
    (M : RawPAModel) (current : M) : Prop :=
  forall cutoff firstAmount secondAmount
      sourceCode sourceStep targetCode targetStep
      bound rootIndex input middle output : M,
    rawLt M rootIndex current ->
    RawCodedTermShiftTrace M cutoff firstAmount
      sourceCode sourceStep targetCode targetStep
      bound rootIndex input middle ->
    RawCodedTermShift M cutoff secondAmount middle output ->
    RawCodedTermShift M cutoff (raw_add M firstAmount secondAmount)
      input output.

Arguments RawCodedTermShiftAmountCompositionIndexBelow M current
  : clear implicits.

Definition termShiftAmountCompositionAll12 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll
    (pAll (pAll (pAll (pAll (pAll (pAll body))))))))))).

(** Variables 11 down to 0 are cutoff, first amount, second amount,
    source/target table columns, bound, root, input, middle, output. *)
Definition codedTermShiftAmountCompositionIndexBelowTermAt
    (current : term) : formula :=
  termShiftAmountCompositionAll12
    (pImp
      (Formula.ltTermAt (tVar 3) (liftTerm 12 current))
      (pImp
        (codedTermShiftTraceTermAt
          (tVar 11) (tVar 10)
          (tVar 8) (tVar 7) (tVar 6) (tVar 5)
          (tVar 4) (tVar 3) (tVar 2) (tVar 1))
        (pImp
          (codedTermShiftTermAt
            (tVar 11) (tVar 9) (tVar 1) (tVar 0))
          (codedTermShiftTermAt
            (tVar 11) (tAdd (tVar 10) (tVar 9))
            (tVar 2) (tVar 0))))).

Lemma raw_termShiftAmountComposition_eval_liftTerm_twelve : forall
    (M : RawPAModel) a b c d f g h i j k l n
    (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i
        (scons M j (scons M k (scons M l (scons M n e))))))))))))
    (liftTerm 12 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i j k l n e t.
  unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro x.
  replace (x + 12) with
    (S (S (S (S (S (S (S (S (S (S (S (S x)))))))))))) by lia.
  reflexivity.
Qed.

Lemma raw_sat_codedTermShiftAmountCompositionIndexBelowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) current,
  raw_formula_sat M e
    (codedTermShiftAmountCompositionIndexBelowTermAt current) <->
  RawCodedTermShiftAmountCompositionIndexBelow M
    (raw_term_eval M e current).
Proof.
  intros M e current.
  unfold codedTermShiftAmountCompositionIndexBelowTermAt,
    termShiftAmountCompositionAll12,
    RawCodedTermShiftAmountCompositionIndexBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermShiftTraceTermAt_iff.
  repeat setoid_rewrite raw_sat_codedTermShiftTermAt_iff.
  repeat setoid_rewrite
    raw_termShiftAmountComposition_eval_liftTerm_twelve.
  cbn [raw_term_eval scons].
  split; intros h cutoff firstAmount secondAmount
    sourceCode sourceStep targetCode targetStep
    bound rootIndex input middle output;
    exact (h cutoff firstAmount secondAmount
      sourceCode sourceStep targetCode targetStep
      bound rootIndex input middle output).
Qed.

Theorem raw_codedTermShiftAmountCompositionIndexBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedTermShiftAmountCompositionIndexBelow M current ->
  RawCodedTermShiftAmountCompositionIndexBelow M (raw_succ M current).
Proof.
  intros M hPA current hcurrent cutoff firstAmount secondAmount
    sourceCode sourceStep targetCode targetStep
    bound rootIndex input middle output
    hrootIndex hfirstTrace hsecond.
  destruct (raw_lt_succ_cases M hPA rootIndex current hrootIndex)
    as [hbefore | hrootCurrent].
  - exact (hcurrent cutoff firstAmount secondAmount
      sourceCode sourceStep targetCode targetStep
      bound rootIndex input middle output
      hbefore hfirstTrace hsecond).
  - subst rootIndex.
    pose proof hfirstTrace as hfirstFacts.
    destruct hfirstFacts as
      (_ & _ & hfirstRoot & hfirstLookup & hfirstRows & _).
    pose proof (hfirstRows current input middle
      hfirstRoot hfirstLookup) as hfirstRow.
    unfold RawCodedTermShiftTraversalRow,
      RawCodedTermOperationTraversalRow in hfirstRow.
    destruct hfirstRow as
      [hfirstVar | [hfirstZero | [hfirstSucc | [hfirstAdd | hfirstMul]]]].
  + destruct hfirstVar as
      (inputIndex & middleIndex & hinput & hmiddle & hfirstIndex).
    subst input. subst middle.
    destruct (raw_codedTermShift_variable_inversion M hPA
      cutoff secondAmount middleIndex output hsecond)
      as (outputIndex & houtput & hsecondIndex).
    subst output.
    apply (raw_codedTermShift_variable_of_shiftedIndex M hPA).
    exact (raw_shiftedIndex_amount_composition M hPA
      cutoff firstAmount secondAmount inputIndex middleIndex outputIndex
      hfirstIndex hsecondIndex).
  + destruct hfirstZero as [hinput hmiddle].
    subst input. subst middle.
    pose proof (raw_codedTermShift_zero_inversion M hPA
      cutoff secondAmount output hsecond) as houtput.
    subst output.
    exact (raw_codedTermShift_zero_identity M hPA
      cutoff (raw_add M firstAmount secondAmount)).
  + destruct hfirstSucc as
      (childIndex & inputChild & middleChild &
       hchildIndex & hchildLookup & hinput & hmiddle).
    subst input. subst middle.
    destruct (raw_codedTermShift_succ_inversion M hPA
      cutoff secondAmount middleChild output hsecond)
      as (outputChild & houtput & hsecondChild).
    subst output.
    apply (raw_codedTermShift_succ M hPA).
    exact (hcurrent cutoff firstAmount secondAmount
      sourceCode sourceStep targetCode targetStep
      bound childIndex inputChild middleChild outputChild
      hchildIndex
      (raw_codedTermShiftTrace_reroot M hPA
        cutoff firstAmount sourceCode sourceStep targetCode targetStep
        bound current
        (rawTermSuccCode M inputChild) (rawTermSuccCode M middleChild)
        hfirstTrace childIndex inputChild middleChild
        hchildIndex hchildLookup)
      hsecondChild).
  + destruct hfirstAdd as
      (leftIndex & inputLeft & middleLeft &
       rightIndex & inputRight & middleRight &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup &
       hinput & hmiddle).
    subst input. subst middle.
    destruct (raw_codedTermShift_add_inversion M hPA
      cutoff secondAmount middleLeft middleRight output hsecond)
      as (outputLeft & outputRight & houtput & hsecondLeft & hsecondRight).
    subst output.
    apply (raw_codedTermShift_add M hPA).
    * exact (hcurrent cutoff firstAmount secondAmount
        sourceCode sourceStep targetCode targetStep
        bound leftIndex inputLeft middleLeft outputLeft
        hleftIndex
        (raw_codedTermShiftTrace_reroot M hPA
          cutoff firstAmount sourceCode sourceStep targetCode targetStep
          bound current
          (rawTermAddCode M inputLeft inputRight)
          (rawTermAddCode M middleLeft middleRight)
          hfirstTrace leftIndex inputLeft middleLeft
          hleftIndex hleftLookup)
        hsecondLeft).
    * exact (hcurrent cutoff firstAmount secondAmount
        sourceCode sourceStep targetCode targetStep
        bound rightIndex inputRight middleRight outputRight
        hrightIndex
        (raw_codedTermShiftTrace_reroot M hPA
          cutoff firstAmount sourceCode sourceStep targetCode targetStep
          bound current
          (rawTermAddCode M inputLeft inputRight)
          (rawTermAddCode M middleLeft middleRight)
          hfirstTrace rightIndex inputRight middleRight
          hrightIndex hrightLookup)
        hsecondRight).
  + destruct hfirstMul as
      (leftIndex & inputLeft & middleLeft &
       rightIndex & inputRight & middleRight &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup &
       hinput & hmiddle).
    subst input. subst middle.
    destruct (raw_codedTermShift_mul_inversion M hPA
      cutoff secondAmount middleLeft middleRight output hsecond)
      as (outputLeft & outputRight & houtput & hsecondLeft & hsecondRight).
    subst output.
    apply (raw_codedTermShift_mul M hPA).
    * exact (hcurrent cutoff firstAmount secondAmount
        sourceCode sourceStep targetCode targetStep
        bound leftIndex inputLeft middleLeft outputLeft
        hleftIndex
        (raw_codedTermShiftTrace_reroot M hPA
          cutoff firstAmount sourceCode sourceStep targetCode targetStep
          bound current
          (rawTermMulCode M inputLeft inputRight)
          (rawTermMulCode M middleLeft middleRight)
          hfirstTrace leftIndex inputLeft middleLeft
          hleftIndex hleftLookup)
        hsecondLeft).
    * exact (hcurrent cutoff firstAmount secondAmount
        sourceCode sourceStep targetCode targetStep
        bound rightIndex inputRight middleRight outputRight
        hrightIndex
        (raw_codedTermShiftTrace_reroot M hPA
          cutoff firstAmount sourceCode sourceStep targetCode targetStep
          bound current
          (rawTermMulCode M inputLeft inputRight)
          (rawTermMulCode M middleLeft middleRight)
          hfirstTrace rightIndex inputRight middleRight
          hrightIndex hrightLookup)
        hsecondRight).
Qed.

Theorem raw_codedTermShiftAmountCompositionIndexBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedTermShiftAmountCompositionIndexBelow M current.
Proof.
  intros M hPA.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi :=
    codedTermShiftAmountCompositionIndexBelowTermAt (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedTermShiftAmountCompositionIndexBelowTermAt_iff M
          (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      intros cutoff firstAmount secondAmount
        sourceCode sourceStep targetCode targetStep
        bound rootIndex input middle output hrootIndex.
      exfalso. exact (raw_not_lt_zero M hPA rootIndex hrootIndex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_codedTermShiftAmountCompositionIndexBelowTermAt_iff M
          (scons M current parameterEnv) (tVar 0)) hcurrent) as hraw.
      apply (proj2
        (raw_sat_codedTermShiftAmountCompositionIndexBelowTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hraw |- *.
      exact (raw_codedTermShiftAmountCompositionIndexBelow_succ
        M hPA current hraw).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedTermShiftAmountCompositionIndexBelowTermAt_iff M
      (scons M current parameterEnv) (tVar 0)) (hall current)) as hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

Theorem raw_codedTermShift_amount_composition : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff firstAmount secondAmount input middle output,
  RawCodedTermShift M cutoff firstAmount input middle ->
  RawCodedTermShift M cutoff secondAmount middle output ->
  RawCodedTermShift M cutoff (raw_add M firstAmount secondAmount)
    input output.
Proof.
  intros M hPA cutoff firstAmount secondAmount input middle output
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & hfirstTrace) hsecond.
  exact (raw_codedTermShiftAmountCompositionIndexBelow_all M hPA
    (raw_succ M rootIndex)
    cutoff firstAmount secondAmount
    sourceCode sourceStep targetCode targetStep
    bound rootIndex input middle output
    (raw_assignment_lt_self_succ M hPA rootIndex)
    hfirstTrace hsecond).
Qed.

End PABoundedRawCodedTermShiftAmountComposition.
