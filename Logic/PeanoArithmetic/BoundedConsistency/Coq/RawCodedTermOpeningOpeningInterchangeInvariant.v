(** PA-definable structural induction for opening/opening interchange. *)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity RawCodedAdditionLaws
  RawCodedAssignment RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedFormulaRankStep
  RawCodedTermOpeningTotality RawCodedProofAtomicAdequacyStandard
  RawCodedTermOperationCrossTraceFunctionality
  RawCodedTermOpeningShiftInterchange
  RawCodedTermOpeningOpeningInterchange.

Module PABoundedRawCodedTermOpeningOpeningInterchangeInvariant.

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
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedTermOpeningTotality.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedTermOperationCrossTraceFunctionality.
Import PABoundedRawCodedTermOpeningShiftInterchange.
Import PABoundedRawCodedTermOpeningOpeningInterchange.

Definition RawCodedTermOpeningOpeningInterchangeIndexBelow
    (M : RawPAModel) (current : M) : Prop :=
  forall depth openingDepth outerAtDepth outerAtSucc
      replacement transformedReplacement
      sourceCode sourceStep targetCode targetStep bound rootIndex
      input transformedInput output transformedOutput : M,
    rawLt M rootIndex current ->
    rawLe M openingDepth depth ->
    RawCodedTermOpening M depth outerAtDepth
      replacement transformedReplacement ->
    RawCodedTermOpening M openingDepth transformedReplacement
      outerAtSucc outerAtDepth ->
    RawCodedTermOpeningTrace M (raw_succ M depth) outerAtSucc
      sourceCode sourceStep targetCode targetStep
      bound rootIndex input transformedInput ->
    RawCodedTermOpening M openingDepth replacement input output ->
    RawCodedTermOpening M openingDepth transformedReplacement
      transformedInput transformedOutput ->
    RawCodedTermOpening M depth outerAtDepth output transformedOutput.

Arguments RawCodedTermOpeningOpeningInterchangeIndexBelow M current
  : clear implicits.

Definition termOpeningOpeningAll16 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll (pAll (pAll
    (pAll (pAll (pAll (pAll (pAll (pAll (pAll (pAll body))))))))))))))).

(** Variables 15 down to 0 follow the semantic invariant's binder order. *)
Definition codedTermOpeningOpeningInterchangeIndexBelowTermAt
    (current : term) : formula :=
  termOpeningOpeningAll16
    (pImp
      (Formula.ltTermAt (tVar 4) (liftTerm 16 current))
      (pImp
        (Formula.leTermAt (tVar 14) (tVar 15))
        (pImp
          (codedTermOpeningTermAt
            (tVar 15) (tVar 13) (tVar 11) (tVar 10))
          (pImp
            (codedTermOpeningTermAt
              (tVar 14) (tVar 10) (tVar 12) (tVar 13))
            (pImp
              (codedTermOpeningTraceTermAt
                (tSucc (tVar 15)) (tVar 12)
                (tVar 9) (tVar 8) (tVar 7) (tVar 6)
                (tVar 5) (tVar 4) (tVar 3) (tVar 2))
              (pImp
                (codedTermOpeningTermAt
                  (tVar 14) (tVar 11) (tVar 3) (tVar 1))
                (pImp
                  (codedTermOpeningTermAt
                    (tVar 14) (tVar 10) (tVar 2) (tVar 0))
                  (codedTermOpeningTermAt
                    (tVar 15) (tVar 13) (tVar 1) (tVar 0))))))))).

Lemma raw_termOpeningOpening_eval_liftTerm_sixteen : forall
    (M : RawPAModel)
    a b c d f g h i j k l n o p q r (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i
        (scons M j (scons M k (scons M l (scons M n
          (scons M o (scons M p (scons M q (scons M r e))))))))))))))))
    (liftTerm 16 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i j k l n o p q r e t.
  unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro x.
  replace (x + 16) with
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x))))))))))))))))
    by lia.
  reflexivity.
Qed.

Lemma raw_sat_codedTermOpeningOpeningInterchangeIndexBelowTermAt_iff :
  forall (M : RawPAModel) (e : nat -> M) current,
  raw_formula_sat M e
    (codedTermOpeningOpeningInterchangeIndexBelowTermAt current) <->
  RawCodedTermOpeningOpeningInterchangeIndexBelow M
    (raw_term_eval M e current).
Proof.
  intros M e current.
  unfold codedTermOpeningOpeningInterchangeIndexBelowTermAt,
    termOpeningOpeningAll16,
    RawCodedTermOpeningOpeningInterchangeIndexBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_leTermAt_iff_rank.
  repeat setoid_rewrite raw_sat_codedTermOpeningTermAt_iff.
  setoid_rewrite raw_sat_codedTermOpeningTraceTermAt_iff.
  repeat setoid_rewrite raw_termOpeningOpening_eval_liftTerm_sixteen.
  cbn [raw_term_eval scons].
  split; intros h depth openingDepth outerAtDepth outerAtSucc
    replacement transformedReplacement
    sourceCode sourceStep targetCode targetStep bound rootIndex
    input transformedInput output transformedOutput;
    exact (h depth openingDepth outerAtDepth outerAtSucc
      replacement transformedReplacement
      sourceCode sourceStep targetCode targetStep bound rootIndex
      input transformedInput output transformedOutput).
Qed.

Theorem raw_codedTermOpeningOpeningInterchangeIndexBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedTermOpeningOpeningInterchangeIndexBelow M current ->
  RawCodedTermOpeningOpeningInterchangeIndexBelow M (raw_succ M current).
Proof.
  intros M hPA current hcurrent depth openingDepth
    outerAtDepth outerAtSucc replacement transformedReplacement
    sourceCode sourceStep targetCode targetStep bound rootIndex
    input transformedInput output transformedOutput hrootIndex hdepth
    hreplacement hcancellation htopTrace hleft hright.
  destruct (raw_lt_succ_cases M hPA rootIndex current hrootIndex)
    as [hbefore | hrootCurrent].
  - exact (hcurrent depth openingDepth outerAtDepth outerAtSucc
      replacement transformedReplacement
      sourceCode sourceStep targetCode targetStep bound rootIndex
      input transformedInput output transformedOutput
      hbefore hdepth hreplacement hcancellation htopTrace hleft hright).
  - subst rootIndex.
    pose proof htopTrace as htopFacts.
    destruct htopFacts as
      (_ & _ & htopRoot & htopLookup & htopRows).
    pose proof (htopRows current input transformedInput
      htopRoot htopLookup) as htopRow.
    unfold RawCodedTermOpeningTraversalRow,
      RawCodedTermOperationTraversalRow in htopRow.
    destruct htopRow as
      [htopVar | [htopZero | [htopSucc | [htopAdd | htopMul]]]].
  + destruct htopVar as (inputIndex & hinput & hcases).
    subst input.
    exact (raw_codedTermOpening_opening_variable_interchange M hPA
      depth openingDepth outerAtDepth outerAtSucc
      replacement transformedReplacement inputIndex
      transformedInput output transformedOutput hdepth
      hreplacement hcancellation
      (ex_intro _ sourceCode (ex_intro _ sourceStep
        (ex_intro _ targetCode (ex_intro _ targetStep
          (ex_intro _ bound (ex_intro _ current htopTrace))))))
      hleft hright).
  + destruct htopZero as [hinput htransformedInput].
    subst input. subst transformedInput.
    pose proof (raw_codedTermOpening_zero_inversion M hPA
      openingDepth replacement output hleft) as houtput.
    pose proof (raw_codedTermOpening_zero_inversion M hPA
      openingDepth transformedReplacement transformedOutput hright)
      as htransformedOutput.
    subst output. subst transformedOutput.
    exact (raw_codedTermOpening_zero M hPA depth outerAtDepth).
  + destruct htopSucc as
      (childIndex & inputChild & transformedChild &
       hchildIndex & hchildLookup & hinput & htransformedInput).
    subst input. subst transformedInput.
    destruct (raw_codedTermOpening_succ_inversion M hPA
      openingDepth replacement inputChild output hleft)
      as (outputChild & houtput & hleftChild).
    subst output.
    destruct (raw_codedTermOpening_succ_inversion M hPA
      openingDepth transformedReplacement transformedChild
      transformedOutput hright)
      as (transformedOutputChild & htransformedOutput & hrightChild).
    subst transformedOutput.
    apply (raw_codedTermOpening_succ M hPA).
    exact (hcurrent depth openingDepth outerAtDepth outerAtSucc
      replacement transformedReplacement
      sourceCode sourceStep targetCode targetStep bound childIndex
      inputChild transformedChild outputChild transformedOutputChild
      hchildIndex hdepth hreplacement hcancellation
      (raw_codedTermOpeningTrace_reroot M hPA
        (raw_succ M depth) outerAtSucc
        sourceCode sourceStep targetCode targetStep bound current
        (rawTermSuccCode M inputChild)
        (rawTermSuccCode M transformedChild) htopTrace
        childIndex inputChild transformedChild hchildIndex hchildLookup)
      hleftChild hrightChild).
  + destruct htopAdd as
      (leftIndex & inputLeft & transformedLeft &
       rightIndex & inputRight & transformedRight &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup &
       hinput & htransformedInput).
    subst input. subst transformedInput.
    destruct (raw_codedTermOpening_add_inversion M hPA
      openingDepth replacement inputLeft inputRight output hleft)
      as (outputLeft & outputRight & houtput & hleftLeft & hleftRight).
    subst output.
    destruct (raw_codedTermOpening_add_inversion M hPA
      openingDepth transformedReplacement transformedLeft transformedRight
      transformedOutput hright)
      as (transformedOutputLeft & transformedOutputRight &
          htransformedOutput & hrightLeft & hrightRight).
    subst transformedOutput.
    apply (raw_codedTermOpening_add M hPA).
    * exact (hcurrent depth openingDepth outerAtDepth outerAtSucc
        replacement transformedReplacement
        sourceCode sourceStep targetCode targetStep bound leftIndex
        inputLeft transformedLeft outputLeft transformedOutputLeft
        hleftIndex hdepth hreplacement hcancellation
        (raw_codedTermOpeningTrace_reroot M hPA
          (raw_succ M depth) outerAtSucc
          sourceCode sourceStep targetCode targetStep bound current
          (rawTermAddCode M inputLeft inputRight)
          (rawTermAddCode M transformedLeft transformedRight) htopTrace
          leftIndex inputLeft transformedLeft hleftIndex hleftLookup)
        hleftLeft hrightLeft).
    * exact (hcurrent depth openingDepth outerAtDepth outerAtSucc
        replacement transformedReplacement
        sourceCode sourceStep targetCode targetStep bound rightIndex
        inputRight transformedRight outputRight transformedOutputRight
        hrightIndex hdepth hreplacement hcancellation
        (raw_codedTermOpeningTrace_reroot M hPA
          (raw_succ M depth) outerAtSucc
          sourceCode sourceStep targetCode targetStep bound current
          (rawTermAddCode M inputLeft inputRight)
          (rawTermAddCode M transformedLeft transformedRight) htopTrace
          rightIndex inputRight transformedRight hrightIndex hrightLookup)
        hleftRight hrightRight).
  + destruct htopMul as
      (leftIndex & inputLeft & transformedLeft &
       rightIndex & inputRight & transformedRight &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup &
       hinput & htransformedInput).
    subst input. subst transformedInput.
    destruct (raw_codedTermOpening_mul_inversion M hPA
      openingDepth replacement inputLeft inputRight output hleft)
      as (outputLeft & outputRight & houtput & hleftLeft & hleftRight).
    subst output.
    destruct (raw_codedTermOpening_mul_inversion M hPA
      openingDepth transformedReplacement transformedLeft transformedRight
      transformedOutput hright)
      as (transformedOutputLeft & transformedOutputRight &
          htransformedOutput & hrightLeft & hrightRight).
    subst transformedOutput.
    apply (raw_codedTermOpening_mul M hPA).
    * exact (hcurrent depth openingDepth outerAtDepth outerAtSucc
        replacement transformedReplacement
        sourceCode sourceStep targetCode targetStep bound leftIndex
        inputLeft transformedLeft outputLeft transformedOutputLeft
        hleftIndex hdepth hreplacement hcancellation
        (raw_codedTermOpeningTrace_reroot M hPA
          (raw_succ M depth) outerAtSucc
          sourceCode sourceStep targetCode targetStep bound current
          (rawTermMulCode M inputLeft inputRight)
          (rawTermMulCode M transformedLeft transformedRight) htopTrace
          leftIndex inputLeft transformedLeft hleftIndex hleftLookup)
        hleftLeft hrightLeft).
    * exact (hcurrent depth openingDepth outerAtDepth outerAtSucc
        replacement transformedReplacement
        sourceCode sourceStep targetCode targetStep bound rightIndex
        inputRight transformedRight outputRight transformedOutputRight
        hrightIndex hdepth hreplacement hcancellation
        (raw_codedTermOpeningTrace_reroot M hPA
          (raw_succ M depth) outerAtSucc
          sourceCode sourceStep targetCode targetStep bound current
          (rawTermMulCode M inputLeft inputRight)
          (rawTermMulCode M transformedLeft transformedRight) htopTrace
          rightIndex inputRight transformedRight hrightIndex hrightLookup)
        hleftRight hrightRight).
Qed.

End PABoundedRawCodedTermOpeningOpeningInterchangeInvariant.
