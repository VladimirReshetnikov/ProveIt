(**
  Transport of represented term opening through a uniform protective shift.

  If the replacement, source, and target of an opening are all shifted from
  cutoff zero by [protection], the opening cutoff increases by the same
  amount.  The proof follows the root of the source-shift trace by genuine
  PA-definable induction and therefore covers nonstandard codes and bounds.
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
  RawCodedProofDescent RawCodedFormulaShiftTotality
  RawCodedTermOpeningTotality RawCodedTermOperationTreeRealization
  RawCodedProofAtomicAdequacyStandard
  RawCodedTermOperationCrossTraceFunctionality
  RawCodedTermShiftProtection RawCodedTermOpeningShiftInterchange.

Module PABoundedRawCodedTermOpeningProtection.

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
Import PABoundedRawCodedTermOpeningTotality.
Import PABoundedRawCodedTermOperationTreeRealization.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedTermOperationCrossTraceFunctionality.
Import PABoundedRawCodedTermShiftProtection.
Import PABoundedRawCodedTermOpeningShiftInterchange.

Lemma raw_shiftedIndex_zero_output : forall
    (M : RawPAModel), RawPASatisfies M -> forall amount input output,
  RawShiftedIndex M (raw_zero M) amount input output ->
  output = raw_add M input amount.
Proof.
  intros M hPA amount input output hshift.
  destruct hshift as [[himpossible _] | [_ houtput]].
  - exfalso. exact (raw_not_lt_zero M hPA input himpossible).
  - exact houtput.
Qed.

(** Build the exact variable opening once its three-way index case has been
    established. *)
Lemma raw_codedTermOpening_variable_of_cases : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement inputIndex output,
  ((rawLt M inputIndex cutoff /\
      output = rawTermVarCode M inputIndex) \/
   (inputIndex = cutoff /\ output = liftedReplacement) \/
   (exists predecessor,
      inputIndex = raw_succ M predecessor /\
      rawLt M cutoff inputIndex /\
      output = rawTermVarCode M predecessor)) ->
  RawCodedTermOpening M cutoff liftedReplacement
    (rawTermVarCode M inputIndex) output.
Proof.
  intros M hPA cutoff liftedReplacement inputIndex output hcases.
  apply (raw_codedTermOpening_of_valid_tree M hPA cutoff
    liftedReplacement (RTOTVar M inputIndex output)).
  cbn [RawTermOperationTreeValid].
  exists inputIndex. split; [reflexivity | exact hcases].
Qed.

(** ------------------------------------------------------------------
    Represented induction invariant. *)

Definition RawCodedTermOpeningProtectionIndexBelow
    (M : RawPAModel) (current : M) : Prop :=
  forall openingDepth protection replacement liftedReplacement
      sourceCode sourceStep targetCode targetStep bound rootIndex
      input liftedInput output liftedOutput : M,
    rawLt M rootIndex current ->
    RawCodedTermShift M (raw_zero M) protection
      replacement liftedReplacement ->
    RawCodedTermShiftTrace M (raw_zero M) protection
      sourceCode sourceStep targetCode targetStep
      bound rootIndex input liftedInput ->
    RawCodedTermOpening M openingDepth replacement input output ->
    RawCodedTermShift M (raw_zero M) protection output liftedOutput ->
    RawCodedTermOpening M (raw_add M openingDepth protection)
      liftedReplacement liftedInput liftedOutput.

Arguments RawCodedTermOpeningProtectionIndexBelow M current
  : clear implicits.

Definition termOpeningProtectionAll14 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll (pAll
    (pAll (pAll (pAll (pAll (pAll (pAll (pAll body))))))))))))).

(** Variables 13 down to 0 follow the order in the semantic invariant. *)
Definition codedTermOpeningProtectionIndexBelowTermAt
    (current : term) : formula :=
  termOpeningProtectionAll14
    (pImp
      (Formula.ltTermAt (tVar 4) (liftTerm 14 current))
      (pImp
        (codedTermShiftTermAt tZero (tVar 12) (tVar 11) (tVar 10))
        (pImp
          (codedTermShiftTraceTermAt tZero (tVar 12)
            (tVar 9) (tVar 8) (tVar 7) (tVar 6)
            (tVar 5) (tVar 4) (tVar 3) (tVar 2))
          (pImp
            (codedTermOpeningTermAt
              (tVar 13) (tVar 11) (tVar 3) (tVar 1))
            (pImp
              (codedTermShiftTermAt tZero (tVar 12)
                (tVar 1) (tVar 0))
              (codedTermOpeningTermAt
                (tAdd (tVar 13) (tVar 12))
                (tVar 10) (tVar 2) (tVar 0))))))).

Lemma raw_termOpeningProtection_eval_liftTerm_fourteen : forall
    (M : RawPAModel)
    a b c d f g h i j k l n o p (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i
        (scons M j (scons M k (scons M l (scons M n
          (scons M o (scons M p e))))))))))))))
    (liftTerm 14 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i j k l n o p e t.
  unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro x.
  replace (x + 14) with
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S x))))))))))))))
    by lia.
  reflexivity.
Qed.

Lemma raw_sat_codedTermOpeningProtectionIndexBelowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) current,
  raw_formula_sat M e
    (codedTermOpeningProtectionIndexBelowTermAt current) <->
  RawCodedTermOpeningProtectionIndexBelow M
    (raw_term_eval M e current).
Proof.
  intros M e current.
  unfold codedTermOpeningProtectionIndexBelowTermAt,
    termOpeningProtectionAll14,
    RawCodedTermOpeningProtectionIndexBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  repeat setoid_rewrite raw_sat_codedTermShiftTermAt_iff.
  setoid_rewrite raw_sat_codedTermShiftTraceTermAt_iff.
  repeat setoid_rewrite raw_sat_codedTermOpeningTermAt_iff.
  repeat setoid_rewrite raw_termOpeningProtection_eval_liftTerm_fourteen.
  cbn [raw_term_eval scons].
  split; intros h openingDepth protection replacement liftedReplacement
    sourceCode sourceStep targetCode targetStep bound rootIndex
    input liftedInput output liftedOutput;
    exact (h openingDepth protection replacement liftedReplacement
      sourceCode sourceStep targetCode targetStep bound rootIndex
      input liftedInput output liftedOutput).
Qed.

Theorem raw_codedTermOpeningProtectionIndexBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedTermOpeningProtectionIndexBelow M current ->
  RawCodedTermOpeningProtectionIndexBelow M (raw_succ M current).
Proof.
  intros M hPA current hcurrent openingDepth protection
    replacement liftedReplacement
    sourceCode sourceStep targetCode targetStep bound rootIndex
    input liftedInput output liftedOutput
    hrootIndex hreplacement htopTrace hopening houtputShift.
  destruct (raw_lt_succ_cases M hPA rootIndex current hrootIndex)
    as [hbefore | hrootCurrent].
  - exact (hcurrent openingDepth protection replacement liftedReplacement
      sourceCode sourceStep targetCode targetStep bound rootIndex
      input liftedInput output liftedOutput hbefore
      hreplacement htopTrace hopening houtputShift).
  - subst rootIndex.
    pose proof htopTrace as htopFacts.
    destruct htopFacts as
      (_ & _ & htopRoot & htopLookup & htopRows & _).
    pose proof (htopRows current input liftedInput
      htopRoot htopLookup) as htopRow.
    unfold RawCodedTermShiftTraversalRow,
      RawCodedTermOperationTraversalRow in htopRow.
    destruct htopRow as
      [htopVar | [htopZero | [htopSucc | [htopAdd | htopMul]]]].
  + destruct htopVar as
      (inputIndex & liftedIndex & hinput & hliftedInput & htopIndex).
    subst input. subst liftedInput.
    pose proof (raw_shiftedIndex_zero_output M hPA
      protection inputIndex liftedIndex htopIndex) as hliftedIndex.
    subst liftedIndex.
    destruct (raw_codedTermOpening_variable_inversion M hPA
      openingDepth replacement inputIndex output hopening)
      as [hlow | [hequal | hhigh]].
    * destruct hlow as [hindexLow houtput]. subst output.
      destruct (raw_codedTermShift_variable_inversion M hPA
        (raw_zero M) protection inputIndex liftedOutput houtputShift)
        as (liftedOutputIndex & hliftedOutput & houtputIndex).
      subst liftedOutput.
      pose proof (raw_shiftedIndex_zero_output M hPA
        protection inputIndex liftedOutputIndex houtputIndex)
        as hliftedOutputIndex.
      subst liftedOutputIndex.
      apply raw_codedTermOpening_variable_of_cases; [exact hPA |].
      left. split.
      -- exact (raw_termShiftProtection_add_right_lt M hPA
           inputIndex openingDepth protection hindexLow).
      -- reflexivity.
    * destruct hequal as [hindexEqual houtput].
      subst inputIndex. subst output.
      pose proof (raw_codedTermShift_functional M hPA
        (raw_zero M) protection replacement
        liftedReplacement liftedOutput hreplacement houtputShift)
        as hliftedOutput.
      subst liftedOutput.
      apply raw_codedTermOpening_variable_of_cases; [exact hPA |].
      right; left. split; reflexivity.
    * destruct hhigh as
        (predecessor & hinputIndex & hindexHigh & houtput).
      subst inputIndex. subst output.
      destruct (raw_codedTermShift_variable_inversion M hPA
        (raw_zero M) protection predecessor liftedOutput houtputShift)
        as (liftedPredecessor & hliftedOutput & hpredecessorShift).
      subst liftedOutput.
      pose proof (raw_shiftedIndex_zero_output M hPA
        protection predecessor liftedPredecessor hpredecessorShift)
        as hliftedPredecessor.
      subst liftedPredecessor.
      apply raw_codedTermOpening_variable_of_cases; [exact hPA |].
      right; right. exists (raw_add M predecessor protection).
      split.
      -- rewrite raw_succ_add_pair by exact hPA. reflexivity.
      -- split.
         ++ exact (raw_termShiftProtection_add_right_lt M hPA
              openingDepth (raw_succ M predecessor) protection
              hindexHigh).
         ++ reflexivity.
  + destruct htopZero as [hinput hliftedInput].
    subst input. subst liftedInput.
    pose proof (raw_codedTermOpening_zero_inversion M hPA
      openingDepth replacement output hopening) as houtput.
    subst output.
    pose proof (raw_codedTermShift_zero_inversion M hPA
      (raw_zero M) protection liftedOutput houtputShift)
      as hliftedOutput.
    subst liftedOutput.
    exact (raw_codedTermOpening_zero M hPA
      (raw_add M openingDepth protection) liftedReplacement).
  + destruct htopSucc as
      (childIndex & inputChild & liftedChild &
       hchildIndex & hchildLookup & hinput & hliftedInput).
    subst input. subst liftedInput.
    destruct (raw_codedTermOpening_succ_inversion M hPA
      openingDepth replacement inputChild output hopening)
      as (outputChild & houtput & hopeningChild).
    subst output.
    destruct (raw_codedTermShift_succ_inversion M hPA
      (raw_zero M) protection outputChild liftedOutput houtputShift)
      as (liftedOutputChild & hliftedOutput & houtputChildShift).
    subst liftedOutput.
    apply (raw_codedTermOpening_succ M hPA).
    exact (hcurrent openingDepth protection replacement liftedReplacement
      sourceCode sourceStep targetCode targetStep bound childIndex
      inputChild liftedChild outputChild liftedOutputChild hchildIndex
      hreplacement
      (raw_codedTermShiftTrace_reroot M hPA
        (raw_zero M) protection
        sourceCode sourceStep targetCode targetStep bound current
        (rawTermSuccCode M inputChild) (rawTermSuccCode M liftedChild)
        htopTrace childIndex inputChild liftedChild
        hchildIndex hchildLookup)
      hopeningChild houtputChildShift).
  + destruct htopAdd as
      (leftIndex & inputLeft & liftedLeft &
       rightIndex & inputRight & liftedRight &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup &
       hinput & hliftedInput).
    subst input. subst liftedInput.
    destruct (raw_codedTermOpening_add_inversion M hPA
      openingDepth replacement inputLeft inputRight output hopening)
      as (outputLeft & outputRight & houtput & hopeningLeft & hopeningRight).
    subst output.
    destruct (raw_codedTermShift_add_inversion M hPA
      (raw_zero M) protection outputLeft outputRight
      liftedOutput houtputShift)
      as (liftedOutputLeft & liftedOutputRight & hliftedOutput &
          houtputLeftShift & houtputRightShift).
    subst liftedOutput.
    apply (raw_codedTermOpening_add M hPA).
    * exact (hcurrent openingDepth protection replacement liftedReplacement
        sourceCode sourceStep targetCode targetStep bound leftIndex
        inputLeft liftedLeft outputLeft liftedOutputLeft hleftIndex
        hreplacement
        (raw_codedTermShiftTrace_reroot M hPA
          (raw_zero M) protection
          sourceCode sourceStep targetCode targetStep bound current
          (rawTermAddCode M inputLeft inputRight)
          (rawTermAddCode M liftedLeft liftedRight)
          htopTrace leftIndex inputLeft liftedLeft
          hleftIndex hleftLookup)
        hopeningLeft houtputLeftShift).
    * exact (hcurrent openingDepth protection replacement liftedReplacement
        sourceCode sourceStep targetCode targetStep bound rightIndex
        inputRight liftedRight outputRight liftedOutputRight hrightIndex
        hreplacement
        (raw_codedTermShiftTrace_reroot M hPA
          (raw_zero M) protection
          sourceCode sourceStep targetCode targetStep bound current
          (rawTermAddCode M inputLeft inputRight)
          (rawTermAddCode M liftedLeft liftedRight)
          htopTrace rightIndex inputRight liftedRight
          hrightIndex hrightLookup)
        hopeningRight houtputRightShift).
  + destruct htopMul as
      (leftIndex & inputLeft & liftedLeft &
       rightIndex & inputRight & liftedRight &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup &
       hinput & hliftedInput).
    subst input. subst liftedInput.
    destruct (raw_codedTermOpening_mul_inversion M hPA
      openingDepth replacement inputLeft inputRight output hopening)
      as (outputLeft & outputRight & houtput & hopeningLeft & hopeningRight).
    subst output.
    destruct (raw_codedTermShift_mul_inversion M hPA
      (raw_zero M) protection outputLeft outputRight
      liftedOutput houtputShift)
      as (liftedOutputLeft & liftedOutputRight & hliftedOutput &
          houtputLeftShift & houtputRightShift).
    subst liftedOutput.
    apply (raw_codedTermOpening_mul M hPA).
    * exact (hcurrent openingDepth protection replacement liftedReplacement
        sourceCode sourceStep targetCode targetStep bound leftIndex
        inputLeft liftedLeft outputLeft liftedOutputLeft hleftIndex
        hreplacement
        (raw_codedTermShiftTrace_reroot M hPA
          (raw_zero M) protection
          sourceCode sourceStep targetCode targetStep bound current
          (rawTermMulCode M inputLeft inputRight)
          (rawTermMulCode M liftedLeft liftedRight)
          htopTrace leftIndex inputLeft liftedLeft
          hleftIndex hleftLookup)
        hopeningLeft houtputLeftShift).
    * exact (hcurrent openingDepth protection replacement liftedReplacement
        sourceCode sourceStep targetCode targetStep bound rightIndex
        inputRight liftedRight outputRight liftedOutputRight hrightIndex
        hreplacement
        (raw_codedTermShiftTrace_reroot M hPA
          (raw_zero M) protection
          sourceCode sourceStep targetCode targetStep bound current
          (rawTermMulCode M inputLeft inputRight)
          (rawTermMulCode M liftedLeft liftedRight)
          htopTrace rightIndex inputRight liftedRight
          hrightIndex hrightLookup)
        hopeningRight houtputRightShift).
Qed.

Theorem raw_codedTermOpeningProtectionIndexBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedTermOpeningProtectionIndexBelow M current.
Proof.
  intros M hPA.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := codedTermOpeningProtectionIndexBelowTermAt (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedTermOpeningProtectionIndexBelowTermAt_iff M
          (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      intros openingDepth protection replacement liftedReplacement
        sourceCode sourceStep targetCode targetStep bound rootIndex
        input liftedInput output liftedOutput hrootIndex.
      exfalso. exact (raw_not_lt_zero M hPA rootIndex hrootIndex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_codedTermOpeningProtectionIndexBelowTermAt_iff M
          (scons M current parameterEnv) (tVar 0)) hcurrent) as hraw.
      apply (proj2
        (raw_sat_codedTermOpeningProtectionIndexBelowTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hraw |- *.
      exact (raw_codedTermOpeningProtectionIndexBelow_succ
        M hPA current hraw).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedTermOpeningProtectionIndexBelowTermAt_iff M
      (scons M current parameterEnv) (tVar 0)) (hall current)) as hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

Theorem raw_codedTermOpening_protection : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      openingDepth protection replacement liftedReplacement
      input liftedInput output liftedOutput,
  RawCodedTermShift M (raw_zero M) protection
    replacement liftedReplacement ->
  RawCodedTermShift M (raw_zero M) protection input liftedInput ->
  RawCodedTermOpening M openingDepth replacement input output ->
  RawCodedTermShift M (raw_zero M) protection output liftedOutput ->
  RawCodedTermOpening M (raw_add M openingDepth protection)
    liftedReplacement liftedInput liftedOutput.
Proof.
  intros M hPA openingDepth protection replacement liftedReplacement
    input liftedInput output liftedOutput hreplacement
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htopTrace) hopening houtput.
  exact (raw_codedTermOpeningProtectionIndexBelow_all M hPA
    (raw_succ M rootIndex)
    openingDepth protection replacement liftedReplacement
    sourceCode sourceStep targetCode targetStep bound rootIndex
    input liftedInput output liftedOutput
    (raw_assignment_lt_self_succ M hPA rootIndex)
    hreplacement htopTrace hopening houtput).
Qed.

End PABoundedRawCodedTermOpeningProtection.
