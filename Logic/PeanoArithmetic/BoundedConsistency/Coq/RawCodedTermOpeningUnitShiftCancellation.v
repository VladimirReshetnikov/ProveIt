(** Opening at zero cancels a represented unit shift from cutoff zero. *)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness RawCodedAdditionLaws RawCodedAssignment
  RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedProofDescent
  RawCodedTermOpeningTotality RawCodedProofAtomicAdequacyStandard
  RawCodedTermOperationCrossTraceFunctionality RawCodedTermShiftProtection
  RawCodedTermOpeningShiftInterchange RawCodedTermOpeningProtection.

Module PABoundedRawCodedTermOpeningUnitShiftCancellation.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAdditionLaws.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedTermOpeningTotality.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedTermOperationCrossTraceFunctionality.
Import PABoundedRawCodedTermShiftProtection.
Import PABoundedRawCodedTermOpeningShiftInterchange.
Import PABoundedRawCodedTermOpeningProtection.

Definition RawCodedTermOpeningUnitShiftCancellationIndexBelow
    (M : RawPAModel) (current : M) : Prop :=
  forall replacement sourceCode sourceStep targetCode targetStep
      bound rootIndex input shifted : M,
    rawLt M rootIndex current ->
    RawCodedTermShiftTrace M
      (raw_zero M) (rawNumeralValue M 1)
      sourceCode sourceStep targetCode targetStep
      bound rootIndex input shifted ->
    RawCodedTermOpening M (raw_zero M) replacement shifted input.

Arguments RawCodedTermOpeningUnitShiftCancellationIndexBelow M current
  : clear implicits.

Definition termOpeningUnitShiftCancellationAll9
    (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll
    (pAll (pAll (pAll (pAll body)))))))).

Definition codedTermOpeningUnitShiftCancellationIndexBelowTermAt
    (current : term) : formula :=
  termOpeningUnitShiftCancellationAll9
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 9 current))
      (pImp
        (codedTermShiftTraceTermAt tZero (tSucc tZero)
          (tVar 7) (tVar 6) (tVar 5) (tVar 4)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))
        (codedTermOpeningTermAt
          tZero (tVar 8) (tVar 0) (tVar 1)))).

Lemma raw_termOpeningUnitShift_eval_liftTerm_nine : forall
    (M : RawPAModel) a b c d f g h i j (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i
        (scons M j e)))))))))
    (liftTerm 9 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i j e t.
  unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro x.
  replace (x + 9) with
    (S (S (S (S (S (S (S (S (S x))))))))) by lia.
  reflexivity.
Qed.

Lemma raw_sat_codedTermOpeningUnitShiftCancellationIndexBelowTermAt_iff :
  forall (M : RawPAModel) (e : nat -> M) current,
  raw_formula_sat M e
    (codedTermOpeningUnitShiftCancellationIndexBelowTermAt current) <->
  RawCodedTermOpeningUnitShiftCancellationIndexBelow M
    (raw_term_eval M e current).
Proof.
  intros M e current.
  unfold codedTermOpeningUnitShiftCancellationIndexBelowTermAt,
    termOpeningUnitShiftCancellationAll9,
    RawCodedTermOpeningUnitShiftCancellationIndexBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermShiftTraceTermAt_iff.
  setoid_rewrite raw_sat_codedTermOpeningTermAt_iff.
  repeat setoid_rewrite raw_termOpeningUnitShift_eval_liftTerm_nine.
  cbn [raw_term_eval scons].
  split; intros h replacement sourceCode sourceStep targetCode targetStep
    bound rootIndex input shifted;
    exact (h replacement sourceCode sourceStep targetCode targetStep
      bound rootIndex input shifted).
Qed.

Theorem raw_codedTermOpeningUnitShiftCancellationIndexBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedTermOpeningUnitShiftCancellationIndexBelow M current ->
  RawCodedTermOpeningUnitShiftCancellationIndexBelow M
    (raw_succ M current).
Proof.
  intros M hPA current hcurrent replacement
    sourceCode sourceStep targetCode targetStep bound rootIndex
    input shifted hrootIndex htrace.
  destruct (raw_lt_succ_cases M hPA rootIndex current hrootIndex)
    as [hbefore | hrootCurrent].
  - exact (hcurrent replacement
      sourceCode sourceStep targetCode targetStep bound rootIndex
      input shifted hbefore htrace).
  - subst rootIndex.
    pose proof htrace as hfacts.
    destruct hfacts as (_ & _ & hroot & hlookup & hrows & _).
    pose proof (hrows current input shifted hroot hlookup) as hrow.
    unfold RawCodedTermShiftTraversalRow,
      RawCodedTermOperationTraversalRow in hrow.
    destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  + destruct hvar as
      (inputIndex & shiftedIndex & hinput & hshifted & hindex).
    subst input. subst shifted.
    pose proof (raw_shiftedIndex_zero_output M hPA
      (rawNumeralValue M 1) inputIndex shiftedIndex hindex)
      as hshiftedIndex.
    rewrite raw_termShiftProtection_add_one in hshiftedIndex by exact hPA.
    subst shiftedIndex.
    apply raw_codedTermOpening_variable_of_cases; [exact hPA |].
    right; right. exists inputIndex.
    split; [reflexivity |]. split.
    * apply raw_lt_succ_of_le; [exact hPA |].
      exact (raw_proof_zero_le M hPA inputIndex).
    * reflexivity.
  + destruct hzero as [hinput hshifted].
    subst input. subst shifted.
    exact (raw_codedTermOpening_zero M hPA
      (raw_zero M) replacement).
  + destruct hsucc as
      (childIndex & inputChild & shiftedChild &
       hchildIndex & hchildLookup & hinput & hshifted).
    subst input. subst shifted.
    apply (raw_codedTermOpening_succ M hPA).
    exact (hcurrent replacement
      sourceCode sourceStep targetCode targetStep bound childIndex
      inputChild shiftedChild hchildIndex
      (raw_codedTermShiftTrace_reroot M hPA
        (raw_zero M) (rawNumeralValue M 1)
        sourceCode sourceStep targetCode targetStep bound current
        (rawTermSuccCode M inputChild) (rawTermSuccCode M shiftedChild)
        htrace childIndex inputChild shiftedChild
        hchildIndex hchildLookup)).
  + destruct hadd as
      (leftIndex & inputLeft & shiftedLeft &
       rightIndex & inputRight & shiftedRight &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup &
       hinput & hshifted).
    subst input. subst shifted.
    apply (raw_codedTermOpening_add M hPA).
    * exact (hcurrent replacement
        sourceCode sourceStep targetCode targetStep bound leftIndex
        inputLeft shiftedLeft hleftIndex
        (raw_codedTermShiftTrace_reroot M hPA
          (raw_zero M) (rawNumeralValue M 1)
          sourceCode sourceStep targetCode targetStep bound current
          (rawTermAddCode M inputLeft inputRight)
          (rawTermAddCode M shiftedLeft shiftedRight)
          htrace leftIndex inputLeft shiftedLeft
          hleftIndex hleftLookup)).
    * exact (hcurrent replacement
        sourceCode sourceStep targetCode targetStep bound rightIndex
        inputRight shiftedRight hrightIndex
        (raw_codedTermShiftTrace_reroot M hPA
          (raw_zero M) (rawNumeralValue M 1)
          sourceCode sourceStep targetCode targetStep bound current
          (rawTermAddCode M inputLeft inputRight)
          (rawTermAddCode M shiftedLeft shiftedRight)
          htrace rightIndex inputRight shiftedRight
          hrightIndex hrightLookup)).
  + destruct hmul as
      (leftIndex & inputLeft & shiftedLeft &
       rightIndex & inputRight & shiftedRight &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup &
       hinput & hshifted).
    subst input. subst shifted.
    apply (raw_codedTermOpening_mul M hPA).
    * exact (hcurrent replacement
        sourceCode sourceStep targetCode targetStep bound leftIndex
        inputLeft shiftedLeft hleftIndex
        (raw_codedTermShiftTrace_reroot M hPA
          (raw_zero M) (rawNumeralValue M 1)
          sourceCode sourceStep targetCode targetStep bound current
          (rawTermMulCode M inputLeft inputRight)
          (rawTermMulCode M shiftedLeft shiftedRight)
          htrace leftIndex inputLeft shiftedLeft
          hleftIndex hleftLookup)).
    * exact (hcurrent replacement
        sourceCode sourceStep targetCode targetStep bound rightIndex
        inputRight shiftedRight hrightIndex
        (raw_codedTermShiftTrace_reroot M hPA
          (raw_zero M) (rawNumeralValue M 1)
          sourceCode sourceStep targetCode targetStep bound current
          (rawTermMulCode M inputLeft inputRight)
          (rawTermMulCode M shiftedLeft shiftedRight)
          htrace rightIndex inputRight shiftedRight
          hrightIndex hrightLookup)).
Qed.

Theorem raw_codedTermOpeningUnitShiftCancellationIndexBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedTermOpeningUnitShiftCancellationIndexBelow M current.
Proof.
  intros M hPA.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi :=
    codedTermOpeningUnitShiftCancellationIndexBelowTermAt (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedTermOpeningUnitShiftCancellationIndexBelowTermAt_iff M
          (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      intros replacement sourceCode sourceStep targetCode targetStep
        bound rootIndex input shifted hrootIndex.
      exfalso. exact (raw_not_lt_zero M hPA rootIndex hrootIndex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_codedTermOpeningUnitShiftCancellationIndexBelowTermAt_iff M
          (scons M current parameterEnv) (tVar 0)) hcurrent) as hraw.
      apply (proj2
        (raw_sat_codedTermOpeningUnitShiftCancellationIndexBelowTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hraw |- *.
      exact (raw_codedTermOpeningUnitShiftCancellationIndexBelow_succ
        M hPA current hraw).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedTermOpeningUnitShiftCancellationIndexBelowTermAt_iff M
      (scons M current parameterEnv) (tVar 0)) (hall current)) as hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

Theorem raw_codedTermOpening_zero_after_unit_shift : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement input shifted,
  RawCodedTermShift M
    (raw_zero M) (rawNumeralValue M 1) input shifted ->
  RawCodedTermOpening M (raw_zero M) replacement shifted input.
Proof.
  intros M hPA replacement input shifted
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace).
  exact (raw_codedTermOpeningUnitShiftCancellationIndexBelow_all M hPA
    (raw_succ M rootIndex) replacement
    sourceCode sourceStep targetCode targetStep bound rootIndex
    input shifted (raw_assignment_lt_self_succ M hPA rootIndex) htrace).
Qed.

End PABoundedRawCodedTermOpeningUnitShiftCancellation.
