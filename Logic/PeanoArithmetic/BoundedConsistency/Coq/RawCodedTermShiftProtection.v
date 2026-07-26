(**
  Protective shifts commute with arbitrary represented term shifts.

  Formula operations increment their atom depth below each binder.  At an
  equality leaf this requires the square

<<
        input  -- shift cutoff amount -->  transformed
          |                                  |
      shift 0 protection                 shift 0 protection
          |                                  |
          v                                  v
     liftedInput -- shift (cutoff+protection) amount --> liftedTransformed.
>>

  All four term codes and all beta tables may be nonstandard elements of an
  arbitrary PA model.  Consequently the proof cannot decode a term in Coq.
  We obtain the bottom edge by represented totality and prove its endpoint
  correct by PA-definable induction over the root index of the top trace.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity RawCodedAdditionLaws
  RawCodedAssignment RawCodedAssignmentTotality RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation RawCodedFormulaOperations
  RawCodedTermEvaluationRealization
  RawCodedFormulaShiftTotality RawCodedTermShiftSyntaxRealization
  RawCodedProofAtomicAdequacyStandard
  RawCodedTermOperationCrossTraceFunctionality.

Module PABoundedRawCodedTermShiftProtection.

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
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedTermShiftSyntaxRealization.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedTermOperationCrossTraceFunctionality.

(** Successor transports strict and weak order in every raw PA model. *)
Lemma raw_termShiftProtection_succ_lt_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  rawLt M left right ->
  rawLt M (raw_succ M left) (raw_succ M right).
Proof.
  intros M hPA left right [gap hgap].
  exists gap.
  rewrite raw_succ_add_pair by exact hPA.
  now rewrite hgap.
Qed.

Lemma raw_termShiftProtection_succ_le_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  rawLe M left right ->
  rawLe M (raw_succ M left) (raw_succ M right).
Proof.
  intros M hPA left right [gap hgap].
  exists gap.
  rewrite raw_succ_add_pair by exact hPA.
  now rewrite hgap.
Qed.

(** Addition on the right transports order.  We spell this out from the
    existential definitions of [rawLt]/[rawLe], so the result is valid for
    nonstandard amounts as well. *)
Lemma raw_termShiftProtection_add_right_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right addend,
  rawLt M left right ->
  rawLt M (raw_add M left addend) (raw_add M right addend).
Proof.
  intros M hPA left right addend [gap hgap].
  exists gap.
  rewrite <- hgap.
  rewrite (raw_add_succ M hPA (raw_add M left addend) gap).
  rewrite (raw_add_succ M hPA left gap).
  rewrite (raw_succ_add_pair M hPA (raw_add M left gap) addend).
  f_equal.
  rewrite !raw_add_assoc by exact hPA.
  rewrite (raw_add_comm M hPA gap addend).
  reflexivity.
Qed.

Lemma raw_termShiftProtection_add_right_le : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right addend,
  rawLe M left right ->
  rawLe M (raw_add M left addend) (raw_add M right addend).
Proof.
  intros M hPA left right addend [gap hgap].
  exists gap.
  rewrite <- hgap.
  rewrite !raw_add_assoc by exact hPA.
  rewrite (raw_add_comm M hPA gap addend).
  reflexivity.
Qed.

(** The variable-level commuting square. *)
Lemma raw_shiftedIndex_protection : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount protection input transformed liftedInput
      liftedTransformed,
  RawShiftedIndex M cutoff amount input transformed ->
  RawShiftedIndex M (raw_zero M) protection input liftedInput ->
  RawShiftedIndex M (raw_zero M) protection
    transformed liftedTransformed ->
  RawShiftedIndex M (raw_add M cutoff protection) amount
    liftedInput liftedTransformed.
Proof.
  intros M hPA cutoff amount protection input transformed
    liftedInput liftedTransformed htop hleft hright.
  destruct hleft as [[himpossible _] | [_ hliftedInput]].
  { exfalso. exact (raw_not_lt_zero M hPA input himpossible). }
  destruct hright as [[himpossible _] | [_ hliftedTransformed]].
  { exfalso. exact (raw_not_lt_zero M hPA transformed himpossible). }
  subst liftedInput liftedTransformed.
  destruct htop as [[hbelow ->] | [habove ->]].
  - left. split.
    + exact (raw_termShiftProtection_add_right_lt
        M hPA input cutoff protection hbelow).
    + reflexivity.
  - right. split.
    + exact (raw_termShiftProtection_add_right_le
        M hPA cutoff input protection habove).
    + rewrite !raw_add_assoc by exact hPA.
      rewrite (raw_add_comm M hPA amount protection).
      reflexivity.
Qed.

(** ------------------------------------------------------------------
    Constructor inversions for public shift relations.

    These lemmas expose only the root constructor and reroot child traces.
    They prevent the four-way square proof below from expanding into 625
    combinations of traversal-row alternatives. *)

Lemma raw_codedTermShift_variable_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount inputIndex output,
  RawCodedTermShift M cutoff amount
    (rawTermVarCode M inputIndex) output ->
  exists outputIndex,
    output = rawTermVarCode M outputIndex /\
    RawShiftedIndex M cutoff amount inputIndex outputIndex.
Proof.
  intros M hPA cutoff amount inputIndex output
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & hroot & hlookup & hrows & _).
  pose proof (hrows rootIndex (rawTermVarCode M inputIndex) output
    hroot hlookup) as hrow.
  unfold RawCodedTermShiftTraversalRow,
    RawCodedTermOperationTraversalRow in hrow.
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - destruct hvar as
      (rowInputIndex & outputIndex & hinput & houtput & hshift).
    unfold rawTermVarCode in hinput.
    destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
      _ _ _ _ hinput) as [_ hindex].
    subst rowInputIndex. exists outputIndex. split; assumption.
  - destruct hzero as [hinput _].
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hsucc as
      (childIndex & inputChild & outputChild & _ & _ & hinput & _).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hadd as
      (leftIndex & inputLeft & outputLeft & rightIndex & inputRight &
       outputRight & _ & _ & _ & _ & hinput & _).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hmul as
      (leftIndex & inputLeft & outputLeft & rightIndex & inputRight &
       outputRight & _ & _ & _ & _ & hinput & _).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
Qed.

Lemma raw_codedTermShift_zero_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount output,
  RawCodedTermShift M cutoff amount (rawTermZeroCode M) output ->
  output = rawTermZeroCode M.
Proof.
  intros M hPA cutoff amount output
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & hroot & hlookup & hrows & _).
  pose proof (hrows rootIndex (rawTermZeroCode M) output
    hroot hlookup) as hrow.
  unfold RawCodedTermShiftTraversalRow,
    RawCodedTermOperationTraversalRow in hrow.
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - destruct hvar as
      (inputIndex & outputIndex & hinput & houtput & hshift).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - exact (proj2 hzero).
  - destruct hsucc as
      (childIndex & inputChild & outputChild & hchildIndex &
       hchildLookup & hinput & houtput).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hadd as
      (leftIndex & inputLeft & outputLeft & rightIndex & inputRight &
       outputRight & hleftIndex & hleftLookup & hrightIndex &
       hrightLookup & hinput & houtput).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hmul as
      (leftIndex & inputLeft & outputLeft & rightIndex & inputRight &
       outputRight & hleftIndex & hleftLookup & hrightIndex &
       hrightLookup & hinput & houtput).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
Qed.

Lemma raw_codedTermShift_succ_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount inputChild output,
  RawCodedTermShift M cutoff amount
    (rawTermSuccCode M inputChild) output ->
  exists outputChild,
    output = rawTermSuccCode M outputChild /\
    RawCodedTermShift M cutoff amount inputChild outputChild.
Proof.
  intros M hPA cutoff amount inputChild output
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & hroot & hlookup & hrows & _).
  pose proof (hrows rootIndex (rawTermSuccCode M inputChild) output
    hroot hlookup) as hrow.
  unfold RawCodedTermShiftTraversalRow,
    RawCodedTermOperationTraversalRow in hrow.
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - destruct hvar as
      (inputIndex & outputIndex & hinput & houtput & hshift).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hzero as [hinput _].
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hsucc as
      (childIndex & rowInputChild & outputChild & hchildIndex &
       hchildLookup & hinput & houtput).
    unfold rawTermSuccCode in hinput.
    destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
      _ _ _ _ hinput) as [_ hchild].
    subst rowInputChild.
    exists outputChild. split; [exact houtput |].
    exact (raw_codedTermShift_reroot M hPA cutoff amount
      sourceCode sourceStep targetCode targetStep bound rootIndex
      (rawTermSuccCode M inputChild) output htrace
      childIndex inputChild outputChild hchildIndex hchildLookup).
  - destruct hadd as
      (leftIndex & rowInputLeft & outputLeft & rightIndex & rowInputRight &
       outputRight & hleftIndex & hleftLookup & hrightIndex &
       hrightLookup & hinput & houtput).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hmul as
      (leftIndex & rowInputLeft & outputLeft & rightIndex & rowInputRight &
       outputRight & hleftIndex & hleftLookup & hrightIndex &
       hrightLookup & hinput & houtput).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
Qed.

Lemma raw_codedTermShift_add_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount inputLeft inputRight output,
  RawCodedTermShift M cutoff amount
    (rawTermAddCode M inputLeft inputRight) output ->
  exists outputLeft outputRight,
    output = rawTermAddCode M outputLeft outputRight /\
    RawCodedTermShift M cutoff amount inputLeft outputLeft /\
    RawCodedTermShift M cutoff amount inputRight outputRight.
Proof.
  intros M hPA cutoff amount inputLeft inputRight output
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & hroot & hlookup & hrows & _).
  pose proof (hrows rootIndex
    (rawTermAddCode M inputLeft inputRight) output hroot hlookup) as hrow.
  unfold RawCodedTermShiftTraversalRow,
    RawCodedTermOperationTraversalRow in hrow.
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - destruct hvar as
      (inputIndex & outputIndex & hinput & houtput & hshift).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hzero as [hinput _].
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hsucc as
      (childIndex & rowInputChild & outputChild & hchildIndex &
       hchildLookup & hinput & houtput).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hadd as
      (leftIndex & rowInputLeft & outputLeft &
       rightIndex & rowInputRight & outputRight &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup &
       hinput & houtput).
    unfold rawTermAddCode in hinput.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hinput) as [_ [hleft hright]].
    subst rowInputLeft. subst rowInputRight.
    exists outputLeft, outputRight. split; [exact houtput |]. split.
    + exact (raw_codedTermShift_reroot M hPA cutoff amount
        sourceCode sourceStep targetCode targetStep bound rootIndex
        (rawTermAddCode M inputLeft inputRight) output htrace
        leftIndex inputLeft outputLeft hleftIndex hleftLookup).
    + exact (raw_codedTermShift_reroot M hPA cutoff amount
        sourceCode sourceStep targetCode targetStep bound rootIndex
        (rawTermAddCode M inputLeft inputRight) output htrace
        rightIndex inputRight outputRight hrightIndex hrightLookup).
  - destruct hmul as
      (leftIndex & rowInputLeft & outputLeft & rightIndex & rowInputRight &
       outputRight & hleftIndex & hleftLookup & hrightIndex &
       hrightLookup & hinput & houtput).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
Qed.

Lemma raw_codedTermShift_mul_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount inputLeft inputRight output,
  RawCodedTermShift M cutoff amount
    (rawTermMulCode M inputLeft inputRight) output ->
  exists outputLeft outputRight,
    output = rawTermMulCode M outputLeft outputRight /\
    RawCodedTermShift M cutoff amount inputLeft outputLeft /\
    RawCodedTermShift M cutoff amount inputRight outputRight.
Proof.
  intros M hPA cutoff amount inputLeft inputRight output
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & hroot & hlookup & hrows & _).
  pose proof (hrows rootIndex
    (rawTermMulCode M inputLeft inputRight) output hroot hlookup) as hrow.
  unfold RawCodedTermShiftTraversalRow,
    RawCodedTermOperationTraversalRow in hrow.
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - destruct hvar as
      (inputIndex & outputIndex & hinput & houtput & hshift).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hzero as [hinput _].
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hsucc as
      (childIndex & rowInputChild & outputChild & hchildIndex &
       hchildLookup & hinput & houtput).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hadd as
      (leftIndex & rowInputLeft & outputLeft & rightIndex & rowInputRight &
       outputRight & hleftIndex & hleftLookup & hrightIndex &
       hrightLookup & hinput & houtput).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hmul as
      (leftIndex & rowInputLeft & outputLeft &
       rightIndex & rowInputRight & outputRight &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup &
       hinput & houtput).
    unfold rawTermMulCode in hinput.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hinput) as [_ [hleft hright]].
    subst rowInputLeft. subst rowInputRight.
    exists outputLeft, outputRight. split; [exact houtput |]. split.
    + exact (raw_codedTermShift_reroot M hPA cutoff amount
        sourceCode sourceStep targetCode targetStep bound rootIndex
        (rawTermMulCode M inputLeft inputRight) output htrace
        leftIndex inputLeft outputLeft hleftIndex hleftLookup).
    + exact (raw_codedTermShift_reroot M hPA cutoff amount
        sourceCode sourceStep targetCode targetStep bound rootIndex
        (rawTermMulCode M inputLeft inputRight) output htrace
        rightIndex inputRight outputRight hrightIndex hrightLookup).
Qed.

(** ------------------------------------------------------------------
    The represented induction invariant.

    The top trace is kept explicit because its root index is the induction
    measure.  The other three edges remain public existential relations;
    their constructor inversions may therefore use unrelated beta tables. *)

Definition RawCodedTermShiftProtectionIndexBelow
    (M : RawPAModel) (current : M) : Prop :=
  forall cutoff amount protection
      sourceCode sourceStep targetCode targetStep bound rootIndex
      input transformed liftedInput liftedTransformed candidate : M,
    rawLt M rootIndex current ->
    RawCodedTermShiftTrace M cutoff amount
      sourceCode sourceStep targetCode targetStep
      bound rootIndex input transformed ->
    RawCodedTermShift M (raw_zero M) protection input liftedInput ->
    RawCodedTermShift M (raw_zero M) protection
      transformed liftedTransformed ->
    RawCodedTermShift M (raw_add M cutoff protection) amount
      liftedInput candidate ->
    candidate = liftedTransformed.

Arguments RawCodedTermShiftProtectionIndexBelow M current
  : clear implicits.

Definition termShiftProtectionAll14 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll (pAll
    (pAll (pAll (pAll (pAll (pAll (pAll (pAll body))))))))))))).

(** Binder order, from outermost to innermost, is

      cutoff, amount, protection,
      sourceCode, sourceStep, targetCode, targetStep, bound, rootIndex,
      input, transformed, liftedInput, liftedTransformed, candidate.

    Hence those fields occupy de Bruijn variables 13 down to 0. *)
Definition codedTermShiftProtectionIndexBelowTermAt
    (current : term) : formula :=
  termShiftProtectionAll14
    (pImp
      (Formula.ltTermAt (tVar 5) (liftTerm 14 current))
      (pImp
        (codedTermShiftTraceTermAt
          (tVar 13) (tVar 12) (tVar 10) (tVar 9) (tVar 8)
          (tVar 7) (tVar 6) (tVar 5) (tVar 4) (tVar 3))
        (pImp
          (codedTermShiftTermAt
            tZero (tVar 11) (tVar 4) (tVar 2))
          (pImp
            (codedTermShiftTermAt
              tZero (tVar 11) (tVar 3) (tVar 1))
            (pImp
              (codedTermShiftTermAt
                (tAdd (tVar 13) (tVar 11))
                (tVar 12) (tVar 2) (tVar 0))
              (pEq (tVar 0) (tVar 1))))))).

Lemma raw_termShiftProtection_eval_liftTerm_fourteen : forall
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

Lemma raw_sat_codedTermShiftProtectionIndexBelowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) current,
  raw_formula_sat M e
    (codedTermShiftProtectionIndexBelowTermAt current) <->
  RawCodedTermShiftProtectionIndexBelow M
    (raw_term_eval M e current).
Proof.
  intros M e current.
  unfold codedTermShiftProtectionIndexBelowTermAt,
    termShiftProtectionAll14,
    RawCodedTermShiftProtectionIndexBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermShiftTraceTermAt_iff.
  repeat setoid_rewrite raw_sat_codedTermShiftTermAt_iff.
  repeat setoid_rewrite raw_termShiftProtection_eval_liftTerm_fourteen.
  cbn [raw_term_eval scons].
  split; intros h cutoff amount protection sourceCode sourceStep
    targetCode targetStep bound rootIndex input transformed liftedInput
    liftedTransformed candidate;
    exact (h cutoff amount protection sourceCode sourceStep
      targetCode targetStep bound rootIndex input transformed liftedInput
      liftedTransformed candidate).
Qed.

Theorem raw_codedTermShiftProtectionIndexBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedTermShiftProtectionIndexBelow M current ->
  RawCodedTermShiftProtectionIndexBelow M (raw_succ M current).
Proof.
  intros M hPA current hcurrent cutoff amount protection
    sourceCode sourceStep targetCode targetStep bound rootIndex
    input transformed liftedInput liftedTransformed candidate
    hrootIndex htopTrace hprotectInput hprotectTransformed hbottom.
  destruct (raw_lt_succ_cases M hPA rootIndex current hrootIndex)
    as [hbefore | hrootCurrent].
  - exact (hcurrent cutoff amount protection
      sourceCode sourceStep targetCode targetStep bound rootIndex
      input transformed liftedInput liftedTransformed candidate
      hbefore htopTrace hprotectInput hprotectTransformed hbottom).
  - subst rootIndex.
    pose proof htopTrace as htopFacts.
    destruct htopFacts as
      (_ & _ & htopRoot & htopLookup & htopRows & _).
    pose proof (htopRows current input transformed
      htopRoot htopLookup) as htopRow.
    unfold RawCodedTermShiftTraversalRow,
      RawCodedTermOperationTraversalRow in htopRow.
    destruct htopRow as
      [ htopVar
      | [ htopZero
        | [ htopSucc
          | [ htopAdd | htopMul ] ] ] ].
  + destruct htopVar as
      (inputIndex & transformedIndex & hinput & htransformed & htopIndex).
    subst input. subst transformed.
    destruct (raw_codedTermShift_variable_inversion M hPA
      (raw_zero M) protection inputIndex liftedInput hprotectInput)
      as (liftedInputIndex & hliftedInput & hleftIndex).
    subst liftedInput.
    destruct (raw_codedTermShift_variable_inversion M hPA
      (raw_zero M) protection transformedIndex liftedTransformed
      hprotectTransformed)
      as (liftedTransformedIndex & hliftedTransformed & hrightIndex).
    subst liftedTransformed.
    destruct (raw_codedTermShift_variable_inversion M hPA
      (raw_add M cutoff protection) amount liftedInputIndex candidate hbottom)
      as (candidateIndex & hcandidate & hbottomIndex).
    subst candidate.
    assert (hexpected : RawShiftedIndex M
        (raw_add M cutoff protection) amount
        liftedInputIndex liftedTransformedIndex).
    {
      exact (raw_shiftedIndex_protection M hPA
        cutoff amount protection inputIndex transformedIndex
        liftedInputIndex liftedTransformedIndex
        htopIndex hleftIndex hrightIndex).
    }
    pose proof (raw_shiftedIndex_functional M hPA
      (raw_add M cutoff protection) amount liftedInputIndex
      candidateIndex liftedTransformedIndex hbottomIndex hexpected)
      as ->.
    reflexivity.
  + destruct htopZero as [hinput htransformed].
    subst input. subst transformed.
    pose proof (raw_codedTermShift_zero_inversion M hPA
      (raw_zero M) protection liftedInput hprotectInput) as hliftedInput.
    pose proof (raw_codedTermShift_zero_inversion M hPA
      (raw_zero M) protection liftedTransformed hprotectTransformed)
      as hliftedTransformed.
    subst liftedInput. subst liftedTransformed.
    exact (raw_codedTermShift_zero_inversion M hPA
      (raw_add M cutoff protection) amount candidate hbottom).
  + destruct htopSucc as
      (childIndex & inputChild & transformedChild & hchildIndex &
       hchildLookup & hinput & htransformed).
    subst input. subst transformed.
    destruct (raw_codedTermShift_succ_inversion M hPA
      (raw_zero M) protection inputChild liftedInput hprotectInput)
      as (liftedInputChild & hliftedInput & hprotectInputChild).
    subst liftedInput.
    destruct (raw_codedTermShift_succ_inversion M hPA
      (raw_zero M) protection transformedChild liftedTransformed
      hprotectTransformed)
      as (liftedTransformedChild & hliftedTransformed &
          hprotectTransformedChild).
    subst liftedTransformed.
    destruct (raw_codedTermShift_succ_inversion M hPA
      (raw_add M cutoff protection) amount liftedInputChild candidate hbottom)
      as (candidateChild & hcandidate & hbottomChild).
    subst candidate.
    assert (hchild : candidateChild = liftedTransformedChild).
    {
      apply (hcurrent cutoff amount protection
        sourceCode sourceStep targetCode targetStep bound childIndex
        inputChild transformedChild liftedInputChild
        liftedTransformedChild candidateChild hchildIndex).
      - exact (raw_codedTermShiftTrace_reroot M hPA
          cutoff amount sourceCode sourceStep targetCode targetStep
          bound current
          (rawTermSuccCode M inputChild)
          (rawTermSuccCode M transformedChild) htopTrace
          childIndex inputChild transformedChild
          hchildIndex hchildLookup).
      - exact hprotectInputChild.
      - exact hprotectTransformedChild.
      - exact hbottomChild.
    }
    now rewrite hchild.
  + destruct htopAdd as
      (leftIndex & inputLeft & transformedLeft &
       rightIndex & inputRight & transformedRight &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup &
       hinput & htransformed).
    subst input. subst transformed.
    destruct (raw_codedTermShift_add_inversion M hPA
      (raw_zero M) protection inputLeft inputRight
      liftedInput hprotectInput)
      as (liftedInputLeft & liftedInputRight & hliftedInput &
          hprotectInputLeft & hprotectInputRight).
    subst liftedInput.
    destruct (raw_codedTermShift_add_inversion M hPA
      (raw_zero M) protection transformedLeft transformedRight
      liftedTransformed hprotectTransformed)
      as (liftedTransformedLeft & liftedTransformedRight &
          hliftedTransformed & hprotectTransformedLeft &
          hprotectTransformedRight).
    subst liftedTransformed.
    destruct (raw_codedTermShift_add_inversion M hPA
      (raw_add M cutoff protection) amount
      liftedInputLeft liftedInputRight candidate hbottom)
      as (candidateLeft & candidateRight & hcandidate &
          hbottomLeft & hbottomRight).
    subst candidate.
    assert (hleft : candidateLeft = liftedTransformedLeft).
    {
      apply (hcurrent cutoff amount protection
        sourceCode sourceStep targetCode targetStep bound leftIndex
        inputLeft transformedLeft liftedInputLeft
        liftedTransformedLeft candidateLeft hleftIndex).
      - exact (raw_codedTermShiftTrace_reroot M hPA
          cutoff amount sourceCode sourceStep targetCode targetStep
          bound current
          (rawTermAddCode M inputLeft inputRight)
          (rawTermAddCode M transformedLeft transformedRight) htopTrace
          leftIndex inputLeft transformedLeft hleftIndex hleftLookup).
      - exact hprotectInputLeft.
      - exact hprotectTransformedLeft.
      - exact hbottomLeft.
    }
    assert (hright : candidateRight = liftedTransformedRight).
    {
      apply (hcurrent cutoff amount protection
        sourceCode sourceStep targetCode targetStep bound rightIndex
        inputRight transformedRight liftedInputRight
        liftedTransformedRight candidateRight hrightIndex).
      - exact (raw_codedTermShiftTrace_reroot M hPA
          cutoff amount sourceCode sourceStep targetCode targetStep
          bound current
          (rawTermAddCode M inputLeft inputRight)
          (rawTermAddCode M transformedLeft transformedRight) htopTrace
          rightIndex inputRight transformedRight hrightIndex hrightLookup).
      - exact hprotectInputRight.
      - exact hprotectTransformedRight.
      - exact hbottomRight.
    }
    now rewrite hleft, hright.
  + destruct htopMul as
      (leftIndex & inputLeft & transformedLeft &
       rightIndex & inputRight & transformedRight &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup &
       hinput & htransformed).
    subst input. subst transformed.
    destruct (raw_codedTermShift_mul_inversion M hPA
      (raw_zero M) protection inputLeft inputRight
      liftedInput hprotectInput)
      as (liftedInputLeft & liftedInputRight & hliftedInput &
          hprotectInputLeft & hprotectInputRight).
    subst liftedInput.
    destruct (raw_codedTermShift_mul_inversion M hPA
      (raw_zero M) protection transformedLeft transformedRight
      liftedTransformed hprotectTransformed)
      as (liftedTransformedLeft & liftedTransformedRight &
          hliftedTransformed & hprotectTransformedLeft &
          hprotectTransformedRight).
    subst liftedTransformed.
    destruct (raw_codedTermShift_mul_inversion M hPA
      (raw_add M cutoff protection) amount
      liftedInputLeft liftedInputRight candidate hbottom)
      as (candidateLeft & candidateRight & hcandidate &
          hbottomLeft & hbottomRight).
    subst candidate.
    assert (hleft : candidateLeft = liftedTransformedLeft).
    {
      apply (hcurrent cutoff amount protection
        sourceCode sourceStep targetCode targetStep bound leftIndex
        inputLeft transformedLeft liftedInputLeft
        liftedTransformedLeft candidateLeft hleftIndex).
      - exact (raw_codedTermShiftTrace_reroot M hPA
          cutoff amount sourceCode sourceStep targetCode targetStep
          bound current
          (rawTermMulCode M inputLeft inputRight)
          (rawTermMulCode M transformedLeft transformedRight) htopTrace
          leftIndex inputLeft transformedLeft hleftIndex hleftLookup).
      - exact hprotectInputLeft.
      - exact hprotectTransformedLeft.
      - exact hbottomLeft.
    }
    assert (hright : candidateRight = liftedTransformedRight).
    {
      apply (hcurrent cutoff amount protection
        sourceCode sourceStep targetCode targetStep bound rightIndex
        inputRight transformedRight liftedInputRight
        liftedTransformedRight candidateRight hrightIndex).
      - exact (raw_codedTermShiftTrace_reroot M hPA
          cutoff amount sourceCode sourceStep targetCode targetStep
          bound current
          (rawTermMulCode M inputLeft inputRight)
          (rawTermMulCode M transformedLeft transformedRight) htopTrace
          rightIndex inputRight transformedRight hrightIndex hrightLookup).
      - exact hprotectInputRight.
      - exact hprotectTransformedRight.
      - exact hbottomRight.
    }
    now rewrite hleft, hright.
Qed.

Theorem raw_codedTermShiftProtectionIndexBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedTermShiftProtectionIndexBelow M current.
Proof.
  intros M hPA.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := codedTermShiftProtectionIndexBelowTermAt (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedTermShiftProtectionIndexBelowTermAt_iff M
          (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      intros cutoff amount protection sourceCode sourceStep
        targetCode targetStep bound rootIndex input transformed
        liftedInput liftedTransformed candidate hrootIndex.
      exfalso. exact (raw_not_lt_zero M hPA rootIndex hrootIndex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_codedTermShiftProtectionIndexBelowTermAt_iff M
          (scons M current parameterEnv) (tVar 0)) hcurrent) as hraw.
      apply (proj2
        (raw_sat_codedTermShiftProtectionIndexBelowTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hraw |- *.
      exact (raw_codedTermShiftProtectionIndexBelow_succ
        M hPA current hraw).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedTermShiftProtectionIndexBelowTermAt_iff M
      (scons M current parameterEnv) (tVar 0)) (hall current)) as hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

(** Endpoint uniqueness for a completed four-edge square. *)
Theorem raw_codedTermShift_protection_endpoint : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount protection input transformed
      liftedInput liftedTransformed candidate,
  RawCodedTermShift M cutoff amount input transformed ->
  RawCodedTermShift M (raw_zero M) protection input liftedInput ->
  RawCodedTermShift M (raw_zero M) protection
    transformed liftedTransformed ->
  RawCodedTermShift M (raw_add M cutoff protection) amount
    liftedInput candidate ->
  candidate = liftedTransformed.
Proof.
  intros M hPA cutoff amount protection input transformed
    liftedInput liftedTransformed candidate
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htopTrace)
    hprotectInput hprotectTransformed hbottom.
  exact (raw_codedTermShiftProtectionIndexBelow_all M hPA
    (raw_succ M rootIndex)
    cutoff amount protection sourceCode sourceStep targetCode targetStep
    bound rootIndex input transformed liftedInput liftedTransformed candidate
    (raw_assignment_lt_self_succ M hPA rootIndex)
    htopTrace hprotectInput hprotectTransformed hbottom).
Qed.

(** The bottom edge exists because [liftedInput] is already the target of a
    represented shift and hence carries an honest represented syntax
    certificate.  The endpoint theorem then identifies totality's candidate
    with the supplied right-hand target. *)
Theorem raw_codedTermShift_protection : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount protection input transformed
      liftedInput liftedTransformed,
  RawCodedTermShift M cutoff amount input transformed ->
  RawCodedTermShift M (raw_zero M) protection input liftedInput ->
  RawCodedTermShift M (raw_zero M) protection
    transformed liftedTransformed ->
  RawCodedTermShift M (raw_add M cutoff protection) amount
    liftedInput liftedTransformed.
Proof.
  intros M hPA cutoff amount protection input transformed
    liftedInput liftedTransformed htop hprotectInput hprotectTransformed.
  assert (hsyntax : RawTermSyntaxRealizable M liftedInput
      (raw_zero M) (raw_zero M)).
  {
    apply (raw_codedTermShift_target_syntax_realizable M hPA
      (raw_zero M) protection input liftedInput
      (raw_zero M) (raw_zero M) (raw_succ M liftedInput)).
    - exact hprotectInput.
    - exact (raw_assignment_lt_self_succ M hPA liftedInput).
    - exact (raw_codedZeroAssignment_defined_all M hPA
        (raw_succ M liftedInput)).
  }
  destruct (raw_codedTermShift_exists_of_syntax_realizable M hPA
    liftedInput (raw_zero M) (raw_zero M) hsyntax
    (raw_add M cutoff protection) amount) as [candidate hcandidate].
  pose proof (raw_codedTermShift_protection_endpoint M hPA
    cutoff amount protection input transformed liftedInput
    liftedTransformed candidate htop hprotectInput
    hprotectTransformed hcandidate) as ->.
  exact hcandidate.
Qed.

Lemma raw_termShiftProtection_add_one : forall
    (M : RawPAModel), RawPASatisfies M -> forall value,
  raw_add M value (rawNumeralValue M 1) = raw_succ M value.
Proof.
  intros M hPA value.
  change (raw_add M value (raw_succ M (raw_zero M)) = raw_succ M value).
  rewrite raw_add_succ by exact hPA.
  now rewrite raw_add_zero_right by exact hPA.
Qed.

Lemma raw_termShiftProtection_add_two : forall
    (M : RawPAModel), RawPASatisfies M -> forall value,
  raw_add M value (rawNumeralValue M 2) =
  raw_succ M (raw_succ M value).
Proof.
  intros M hPA value.
  change (raw_add M value (raw_succ M (raw_succ M (raw_zero M))) =
    raw_succ M (raw_succ M value)).
  rewrite !raw_add_succ by exact hPA.
  now rewrite raw_add_zero_right by exact hPA.
Qed.

Corollary raw_codedTermShift_protect_one : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount input transformed liftedInput liftedTransformed,
  RawCodedTermShift M cutoff amount input transformed ->
  RawCodedTermShift M (raw_zero M) (rawNumeralValue M 1)
    input liftedInput ->
  RawCodedTermShift M (raw_zero M) (rawNumeralValue M 1)
    transformed liftedTransformed ->
  RawCodedTermShift M (raw_succ M cutoff) amount
    liftedInput liftedTransformed.
Proof.
  intros M hPA cutoff amount input transformed
    liftedInput liftedTransformed htop hleft hright.
  pose proof (raw_codedTermShift_protection M hPA
    cutoff amount (rawNumeralValue M 1) input transformed
    liftedInput liftedTransformed htop hleft hright) as hbottom.
  now rewrite raw_termShiftProtection_add_one in hbottom by exact hPA.
Qed.

Corollary raw_codedTermShift_protect_two : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount input transformed liftedInput liftedTransformed,
  RawCodedTermShift M cutoff amount input transformed ->
  RawCodedTermShift M (raw_zero M) (rawNumeralValue M 2)
    input liftedInput ->
  RawCodedTermShift M (raw_zero M) (rawNumeralValue M 2)
    transformed liftedTransformed ->
  RawCodedTermShift M (raw_succ M (raw_succ M cutoff)) amount
    liftedInput liftedTransformed.
Proof.
  intros M hPA cutoff amount input transformed
    liftedInput liftedTransformed htop hleft hright.
  pose proof (raw_codedTermShift_protection M hPA
    cutoff amount (rawNumeralValue M 2) input transformed
    liftedInput liftedTransformed htop hleft hright) as hbottom.
  now rewrite raw_termShiftProtection_add_two in hbottom by exact hPA.
Qed.

End PABoundedRawCodedTermShiftProtection.
