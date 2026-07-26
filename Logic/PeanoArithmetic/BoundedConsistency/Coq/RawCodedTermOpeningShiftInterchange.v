(**
  Capture-avoiding term opening commutes with represented shifting.

  The formula single-substitution square eventually reaches the following
  term-level law at equality leaves.  If the opening cutoff [openingDepth]
  is no larger than the target shift cutoff [depth], then shifting above
  [S depth] before opening agrees with opening first and shifting above
  [depth].  The inserted replacements are related by that latter shift.

  As with the protective-shift theorem, the top trace may have a nonstandard
  root index.  The recursive proof is therefore a represented induction,
  not a Coq recursion over decoded syntax.
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
  RawCodedFormulaRankStep
  RawCodedPAAxiomContextSelfShift
  RawCodedFormulaShiftTotality RawCodedTermOpeningTotality
  RawCodedProofAtomicAdequacyStandard
  RawCodedTermOperationCrossTraceFunctionality
  RawCodedTermShiftProtection.

Module PABoundedRawCodedTermOpeningShiftInterchange.

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
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedTermOpeningTotality.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedTermOperationCrossTraceFunctionality.
Import PABoundedRawCodedTermShiftProtection.

(** An exact variable shift can be reconstructed from its index relation.
    Totality supplies some variable target; the inversion and functionality
    theorems identify its index with the requested one. *)
Lemma raw_codedTermShift_variable_of_shiftedIndex : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount inputIndex outputIndex,
  RawShiftedIndex M cutoff amount inputIndex outputIndex ->
  RawCodedTermShift M cutoff amount
    (rawTermVarCode M inputIndex) (rawTermVarCode M outputIndex).
Proof.
  intros M hPA cutoff amount inputIndex outputIndex hindex.
  destruct (raw_codedTermShift_variable_exists M hPA
    cutoff amount inputIndex) as [candidate hcandidate].
  destruct (raw_codedTermShift_variable_inversion M hPA
    cutoff amount inputIndex candidate hcandidate)
    as (candidateIndex & -> & hcandidateIndex).
  pose proof (raw_shiftedIndex_functional M hPA
    cutoff amount inputIndex candidateIndex outputIndex
    hcandidateIndex hindex) as ->.
  exact hcandidate.
Qed.

(** Public opening relations expose the same five source constructors as
    their synchronized traces. *)
Lemma raw_codedTermOpening_variable_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement inputIndex output,
  RawCodedTermOpening M cutoff liftedReplacement
    (rawTermVarCode M inputIndex) output ->
  (rawLt M inputIndex cutoff /\
      output = rawTermVarCode M inputIndex) \/
  (inputIndex = cutoff /\ output = liftedReplacement) \/
  (exists predecessor,
      inputIndex = raw_succ M predecessor /\
      rawLt M cutoff inputIndex /\
      output = rawTermVarCode M predecessor).
Proof.
  intros M hPA cutoff liftedReplacement inputIndex output
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & hroot & hlookup & hrows).
  pose proof (hrows rootIndex (rawTermVarCode M inputIndex) output
    hroot hlookup) as hrow.
  unfold RawCodedTermOpeningTraversalRow,
    RawCodedTermOperationTraversalRow in hrow.
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - destruct hvar as (rowInputIndex & hinput & hcases).
    unfold rawTermVarCode in hinput.
    destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
      _ _ _ _ hinput) as [_ hindex].
    subst rowInputIndex. exact hcases.
  - destruct hzero as [hinput _].
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
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

Lemma raw_codedTermOpening_zero_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement output,
  RawCodedTermOpening M cutoff liftedReplacement
    (rawTermZeroCode M) output ->
  output = rawTermZeroCode M.
Proof.
  intros M hPA cutoff liftedReplacement output
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & hroot & hlookup & hrows).
  pose proof (hrows rootIndex (rawTermZeroCode M) output
    hroot hlookup) as hrow.
  unfold RawCodedTermOpeningTraversalRow,
    RawCodedTermOperationTraversalRow in hrow.
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - destruct hvar as (inputIndex & hinput & hcases).
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

Lemma raw_codedTermOpening_succ_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement inputChild output,
  RawCodedTermOpening M cutoff liftedReplacement
    (rawTermSuccCode M inputChild) output ->
  exists outputChild,
    output = rawTermSuccCode M outputChild /\
    RawCodedTermOpening M cutoff liftedReplacement inputChild outputChild.
Proof.
  intros M hPA cutoff liftedReplacement inputChild output
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & hroot & hlookup & hrows).
  pose proof (hrows rootIndex (rawTermSuccCode M inputChild) output
    hroot hlookup) as hrow.
  unfold RawCodedTermOpeningTraversalRow,
    RawCodedTermOperationTraversalRow in hrow.
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - destruct hvar as (inputIndex & hinput & hcases).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hzero as [hinput _].
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hsucc as
      (childIndex & rowInputChild & outputChild & hchildIndex &
       hchildLookup & hinput & houtput).
    unfold rawTermSuccCode in hinput.
    destruct (raw_codeList2_injective M (rawListNode_injective M hPA)
      _ _ _ _ hinput) as [_ hchild].
    subst rowInputChild. exists outputChild. split; [exact houtput |].
    exact (raw_codedTermOpening_reroot M hPA cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep bound rootIndex
      (rawTermSuccCode M inputChild) output htrace
      childIndex inputChild outputChild hchildIndex hchildLookup).
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

Lemma raw_codedTermOpening_add_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement inputLeft inputRight output,
  RawCodedTermOpening M cutoff liftedReplacement
    (rawTermAddCode M inputLeft inputRight) output ->
  exists outputLeft outputRight,
    output = rawTermAddCode M outputLeft outputRight /\
    RawCodedTermOpening M cutoff liftedReplacement inputLeft outputLeft /\
    RawCodedTermOpening M cutoff liftedReplacement inputRight outputRight.
Proof.
  intros M hPA cutoff liftedReplacement inputLeft inputRight output
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & hroot & hlookup & hrows).
  pose proof (hrows rootIndex
    (rawTermAddCode M inputLeft inputRight) output hroot hlookup) as hrow.
  unfold RawCodedTermOpeningTraversalRow,
    RawCodedTermOperationTraversalRow in hrow.
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - destruct hvar as (inputIndex & hinput & hcases).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hzero as [hinput _].
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hsucc as
      (childIndex & inputChild & outputChild & hchildIndex &
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
    + exact (raw_codedTermOpening_reroot M hPA cutoff liftedReplacement
        sourceCode sourceStep targetCode targetStep bound rootIndex
        (rawTermAddCode M inputLeft inputRight) output htrace
        leftIndex inputLeft outputLeft hleftIndex hleftLookup).
    + exact (raw_codedTermOpening_reroot M hPA cutoff liftedReplacement
        sourceCode sourceStep targetCode targetStep bound rootIndex
        (rawTermAddCode M inputLeft inputRight) output htrace
        rightIndex inputRight outputRight hrightIndex hrightLookup).
  - destruct hmul as
      (leftIndex & inputLeft' & outputLeft & rightIndex & inputRight' &
       outputRight & hleftIndex & hleftLookup & hrightIndex &
       hrightLookup & hinput & houtput).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
Qed.

Lemma raw_codedTermOpening_mul_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement inputLeft inputRight output,
  RawCodedTermOpening M cutoff liftedReplacement
    (rawTermMulCode M inputLeft inputRight) output ->
  exists outputLeft outputRight,
    output = rawTermMulCode M outputLeft outputRight /\
    RawCodedTermOpening M cutoff liftedReplacement inputLeft outputLeft /\
    RawCodedTermOpening M cutoff liftedReplacement inputRight outputRight.
Proof.
  intros M hPA cutoff liftedReplacement inputLeft inputRight output
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & hroot & hlookup & hrows).
  pose proof (hrows rootIndex
    (rawTermMulCode M inputLeft inputRight) output hroot hlookup) as hrow.
  unfold RawCodedTermOpeningTraversalRow,
    RawCodedTermOperationTraversalRow in hrow.
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - destruct hvar as (inputIndex & hinput & hcases).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hzero as [hinput _].
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hsucc as
      (childIndex & inputChild & outputChild & hchildIndex &
       hchildLookup & hinput & houtput).
    exfalso. raw_standard_term_shape_contradiction M hPA hinput.
  - destruct hadd as
      (leftIndex & inputLeft' & outputLeft & rightIndex & inputRight' &
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
    + exact (raw_codedTermOpening_reroot M hPA cutoff liftedReplacement
        sourceCode sourceStep targetCode targetStep bound rootIndex
        (rawTermMulCode M inputLeft inputRight) output htrace
        leftIndex inputLeft outputLeft hleftIndex hleftLookup).
    + exact (raw_codedTermOpening_reroot M hPA cutoff liftedReplacement
        sourceCode sourceStep targetCode targetStep bound rootIndex
        (rawTermMulCode M inputLeft inputRight) output htrace
        rightIndex inputRight outputRight hrightIndex hrightLookup).
Qed.

(** Shifted indices never move down, and successor inputs can be inverted
    across a successor cutoff. *)
Lemma raw_openingShift_shiftedIndex_preserves_lower : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      lower cutoff amount input output,
  rawLt M lower input ->
  RawShiftedIndex M cutoff amount input output ->
  rawLt M lower output.
Proof.
  intros M hPA lower cutoff amount input output hlower hshift.
  destruct hshift as [[_ ->] | [_ ->]].
  - exact hlower.
  - exact (raw_lt_le_trans_pair M hPA lower input
      (raw_add M input amount) hlower (ex_intro _ amount eq_refl)).
Qed.

Lemma raw_openingShift_shiftedIndex_under_successors : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff amount inputIndex outputIndex,
  RawShiftedIndex M (raw_succ M cutoff) amount
    (raw_succ M inputIndex) outputIndex ->
  exists predecessorOutput,
    outputIndex = raw_succ M predecessorOutput /\
    RawShiftedIndex M cutoff amount inputIndex predecessorOutput.
Proof.
  intros M hPA cutoff amount inputIndex outputIndex
    [[hbelow houtput] | [habove houtput]].
  - assert (hinputBelow : rawLt M inputIndex cutoff).
    {
      destruct (raw_lt_succ_cases M hPA
        (raw_succ M inputIndex) cutoff hbelow) as [hstrict | hequal].
      - exact (raw_assignment_lt_trans M hPA inputIndex
          (raw_succ M inputIndex) cutoff
          (raw_assignment_lt_self_succ M hPA inputIndex) hstrict).
      - rewrite <- hequal.
        exact (raw_assignment_lt_self_succ M hPA inputIndex).
    }
    exists inputIndex. split; [exact houtput |].
    left. split; [exact hinputBelow | reflexivity].
  - assert (hinputAbove : rawLe M cutoff inputIndex).
    {
      destruct habove as [gap hgap]. exists gap.
      rewrite raw_succ_add_pair in hgap by exact hPA.
      exact (raw_succ_injective_syntax M hPA _ _ hgap).
    }
    exists (raw_add M inputIndex amount). split.
    + rewrite houtput. apply raw_succ_add_pair. exact hPA.
    + right. split; [exact hinputAbove | reflexivity].
Qed.

(** The only nonrecursive part of the interchange proof.  Opening has three
    variable branches; [openingDepth <= depth] ensures the outer shift fixes
    the replacement position and maps strict successors to strict
    successors. *)
Lemma raw_codedTermOpening_shift_variable_interchange : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      depth amount openingDepth replacement transformedReplacement
      inputIndex transformedIndex output transformedOutput,
  rawLe M openingDepth depth ->
  RawCodedTermShift M depth amount
    replacement transformedReplacement ->
  RawShiftedIndex M (raw_succ M depth) amount
    inputIndex transformedIndex ->
  RawCodedTermOpening M openingDepth replacement
    (rawTermVarCode M inputIndex) output ->
  RawCodedTermOpening M openingDepth transformedReplacement
    (rawTermVarCode M transformedIndex) transformedOutput ->
  RawCodedTermShift M depth amount output transformedOutput.
Proof.
  intros M hPA depth amount openingDepth replacement
    transformedReplacement inputIndex transformedIndex
    output transformedOutput hdepth hreplacement htop hleft hright.
  destruct (raw_codedTermOpening_variable_inversion M hPA
    openingDepth replacement inputIndex output hleft) as
    [[hinputBelow houtput] |
      [[hinputAt houtput] |
        (inputPredecessor & hinputSucc & hinputAbove & houtput)]].
  - assert (hinputDepth : rawLt M inputIndex depth).
    {
      exact (raw_lt_le_trans_pair M hPA
        inputIndex openingDepth depth hinputBelow hdepth).
    }
    assert (hinputSuccDepth : rawLt M inputIndex (raw_succ M depth)).
    {
      exact (raw_assignment_lt_trans M hPA inputIndex depth
        (raw_succ M depth) hinputDepth
        (raw_assignment_lt_self_succ M hPA depth)).
    }
    assert (htransformedIndex : transformedIndex = inputIndex).
    {
      apply (raw_shiftedIndex_functional M hPA
        (raw_succ M depth) amount inputIndex transformedIndex inputIndex
        htop).
      left. split; [exact hinputSuccDepth | reflexivity].
    }
    subst transformedIndex. subst output.
    destruct (raw_codedTermOpening_variable_inversion M hPA
      openingDepth transformedReplacement inputIndex transformedOutput
      hright) as
      [[_ htransformedOutput] |
        [[hrightAt _] |
          (rightPredecessor & _ & hrightAbove & _)]].
    + subst transformedOutput.
      apply raw_codedTermShift_variable_of_shiftedIndex; [exact hPA |].
      left. split; [exact hinputDepth | reflexivity].
    + subst inputIndex.
      exfalso. exact (raw_not_lt_self M hPA
        openingDepth hinputBelow).
    + exfalso. apply (raw_not_lt_self M hPA inputIndex).
      exact (raw_assignment_lt_trans M hPA inputIndex openingDepth
        inputIndex hinputBelow hrightAbove).
  - subst inputIndex. subst output.
    assert (hopeningSuccDepth :
        rawLt M openingDepth (raw_succ M depth)).
    { exact (raw_lt_succ_of_le M hPA openingDepth depth hdepth). }
    assert (htransformedIndex : transformedIndex = openingDepth).
    {
      apply (raw_shiftedIndex_functional M hPA
        (raw_succ M depth) amount openingDepth
        transformedIndex openingDepth htop).
      left. split; [exact hopeningSuccDepth | reflexivity].
    }
    subst transformedIndex.
    destruct (raw_codedTermOpening_variable_inversion M hPA
      openingDepth transformedReplacement openingDepth transformedOutput
      hright) as
      [[hrightBelow _] |
        [[_ htransformedOutput] |
          (rightPredecessor & _ & hrightAbove & _)]].
    + exfalso. exact (raw_not_lt_self M hPA
        openingDepth hrightBelow).
    + subst transformedOutput. exact hreplacement.
    + exfalso. exact (raw_not_lt_self M hPA
        openingDepth hrightAbove).
  - subst inputIndex. subst output.
    destruct (raw_openingShift_shiftedIndex_under_successors M hPA
      depth amount inputPredecessor transformedIndex htop)
      as (transformedPredecessor & htransformedSucc & hpredecessorShift).
    subst transformedIndex.
    assert (htransformedAbove : rawLt M openingDepth
        (raw_succ M transformedPredecessor)).
    {
      exact (raw_openingShift_shiftedIndex_preserves_lower M hPA
        openingDepth (raw_succ M depth) amount
        (raw_succ M inputPredecessor)
        (raw_succ M transformedPredecessor) hinputAbove htop).
    }
    destruct (raw_codedTermOpening_variable_inversion M hPA
      openingDepth transformedReplacement
      (raw_succ M transformedPredecessor) transformedOutput hright) as
      [[hrightBelow _] |
        [[hrightAt _] |
          (rightPredecessor & hrightSucc & _ & htransformedOutput)]].
    + exfalso. apply (raw_not_lt_self M hPA
        (raw_succ M transformedPredecessor)).
      exact (raw_assignment_lt_trans M hPA
        (raw_succ M transformedPredecessor) openingDepth
        (raw_succ M transformedPredecessor)
        hrightBelow htransformedAbove).
    + subst openingDepth.
      exfalso. exact (raw_not_lt_self M hPA
        (raw_succ M transformedPredecessor) htransformedAbove).
    + assert (hrightPredecessor :
          rightPredecessor = transformedPredecessor).
      {
        symmetry.
        exact (raw_succ_injective_syntax M hPA _ _ hrightSucc).
      }
      subst rightPredecessor. subst transformedOutput.
      exact (raw_codedTermShift_variable_of_shiftedIndex M hPA
        depth amount inputPredecessor transformedPredecessor
        hpredecessorShift).
Qed.

(** ------------------------------------------------------------------
    PA-definable structural induction for the complete term square. *)

Definition RawCodedTermOpeningShiftInterchangeIndexBelow
    (M : RawPAModel) (current : M) : Prop :=
  forall depth amount openingDepth replacement transformedReplacement
      sourceCode sourceStep targetCode targetStep bound rootIndex
      input transformedInput output transformedOutput : M,
    rawLt M rootIndex current ->
    rawLe M openingDepth depth ->
    RawCodedTermShift M depth amount
      replacement transformedReplacement ->
    RawCodedTermShiftTrace M (raw_succ M depth) amount
      sourceCode sourceStep targetCode targetStep bound rootIndex
      input transformedInput ->
    RawCodedTermOpening M openingDepth replacement input output ->
    RawCodedTermOpening M openingDepth transformedReplacement
      transformedInput transformedOutput ->
    RawCodedTermShift M depth amount output transformedOutput.

Arguments RawCodedTermOpeningShiftInterchangeIndexBelow M current
  : clear implicits.

Definition termOpeningShiftAll15 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll (pAll (pAll
    (pAll (pAll (pAll (pAll (pAll (pAll (pAll body)))))))))))))).

(** Binder order is

      depth, amount, openingDepth, replacement, transformedReplacement,
      sourceCode, sourceStep, targetCode, targetStep, bound, rootIndex,
      input, transformedInput, output, transformedOutput,

    occupying variables 14 down to 0. *)
Definition codedTermOpeningShiftInterchangeIndexBelowTermAt
    (current : term) : formula :=
  termOpeningShiftAll15
    (pImp
      (Formula.ltTermAt (tVar 4) (liftTerm 15 current))
      (pImp
        (Formula.leTermAt (tVar 12) (tVar 14))
        (pImp
          (codedTermShiftTermAt
            (tVar 14) (tVar 13) (tVar 11) (tVar 10))
          (pImp
            (codedTermShiftTraceTermAt
              (tSucc (tVar 14)) (tVar 13)
              (tVar 9) (tVar 8) (tVar 7) (tVar 6)
              (tVar 5) (tVar 4) (tVar 3) (tVar 2))
            (pImp
              (codedTermOpeningTermAt
                (tVar 12) (tVar 11) (tVar 3) (tVar 1))
              (pImp
                (codedTermOpeningTermAt
                  (tVar 12) (tVar 10) (tVar 2) (tVar 0))
                (codedTermShiftTermAt
                  (tVar 14) (tVar 13) (tVar 1) (tVar 0)))))))).

Lemma raw_termOpeningShift_eval_liftTerm_fifteen : forall
    (M : RawPAModel)
    a b c d f g h i j k l n o p q (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i
        (scons M j (scons M k (scons M l (scons M n
          (scons M o (scons M p (scons M q e)))))))))))))))
    (liftTerm 15 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i j k l n o p q e t.
  unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro x.
  replace (x + 15) with
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x)))))))))))))))
    by lia.
  reflexivity.
Qed.

Lemma raw_sat_codedTermOpeningShiftInterchangeIndexBelowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) current,
  raw_formula_sat M e
    (codedTermOpeningShiftInterchangeIndexBelowTermAt current) <->
  RawCodedTermOpeningShiftInterchangeIndexBelow M
    (raw_term_eval M e current).
Proof.
  intros M e current.
  unfold codedTermOpeningShiftInterchangeIndexBelowTermAt,
    termOpeningShiftAll15,
    RawCodedTermOpeningShiftInterchangeIndexBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_leTermAt_iff_rank.
  repeat setoid_rewrite raw_sat_codedTermShiftTermAt_iff.
  setoid_rewrite raw_sat_codedTermShiftTraceTermAt_iff.
  repeat setoid_rewrite raw_sat_codedTermOpeningTermAt_iff.
  repeat setoid_rewrite raw_termOpeningShift_eval_liftTerm_fifteen.
  cbn [raw_term_eval scons].
  split; intros h depth amount openingDepth replacement
    transformedReplacement sourceCode sourceStep targetCode targetStep
    bound rootIndex input transformedInput output transformedOutput;
    exact (h depth amount openingDepth replacement transformedReplacement
      sourceCode sourceStep targetCode targetStep bound rootIndex
      input transformedInput output transformedOutput).
Qed.

Theorem raw_codedTermOpeningShiftInterchangeIndexBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedTermOpeningShiftInterchangeIndexBelow M current ->
  RawCodedTermOpeningShiftInterchangeIndexBelow M (raw_succ M current).
Proof.
  intros M hPA current hcurrent depth amount openingDepth
    replacement transformedReplacement sourceCode sourceStep
    targetCode targetStep bound rootIndex input transformedInput
    output transformedOutput hrootIndex hdepth hreplacement
    htopTrace hleft hright.
  destruct (raw_lt_succ_cases M hPA rootIndex current hrootIndex)
    as [hbefore | hrootCurrent].
  - exact (hcurrent depth amount openingDepth replacement
      transformedReplacement sourceCode sourceStep targetCode targetStep
      bound rootIndex input transformedInput output transformedOutput
      hbefore hdepth hreplacement htopTrace hleft hright).
  - subst rootIndex.
    pose proof htopTrace as htopFacts.
    destruct htopFacts as
      (_ & _ & htopRoot & htopLookup & htopRows & _).
    pose proof (htopRows current input transformedInput
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
    subst input. subst transformedInput.
    exact (raw_codedTermOpening_shift_variable_interchange M hPA
      depth amount openingDepth replacement transformedReplacement
      inputIndex transformedIndex output transformedOutput
      hdepth hreplacement htopIndex hleft hright).
  + destruct htopZero as [hinput htransformed].
    subst input. subst transformedInput.
    pose proof (raw_codedTermOpening_zero_inversion M hPA
      openingDepth replacement output hleft) as houtput.
    pose proof (raw_codedTermOpening_zero_inversion M hPA
      openingDepth transformedReplacement transformedOutput hright)
      as htransformedOutput.
    subst output. subst transformedOutput.
    exact (raw_codedTermShift_zero_identity M hPA depth amount).
  + destruct htopSucc as
      (childIndex & inputChild & transformedChild & hchildIndex &
       hchildLookup & hinput & htransformed).
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
    apply (raw_codedTermShift_succ M hPA depth amount).
    exact (hcurrent depth amount openingDepth replacement
      transformedReplacement sourceCode sourceStep targetCode targetStep
      bound childIndex inputChild transformedChild
      outputChild transformedOutputChild hchildIndex hdepth hreplacement
      (raw_codedTermShiftTrace_reroot M hPA
        (raw_succ M depth) amount
        sourceCode sourceStep targetCode targetStep bound current
        (rawTermSuccCode M inputChild)
        (rawTermSuccCode M transformedChild) htopTrace
        childIndex inputChild transformedChild hchildIndex hchildLookup)
      hleftChild hrightChild).
  + destruct htopAdd as
      (leftIndex & inputLeft & transformedLeft &
       rightIndex & inputRight & transformedRight &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup &
       hinput & htransformed).
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
    assert (hdesiredLeft : RawCodedTermShift M depth amount
        outputLeft transformedOutputLeft).
    {
      exact (hcurrent depth amount openingDepth replacement
        transformedReplacement sourceCode sourceStep targetCode targetStep
        bound leftIndex inputLeft transformedLeft
        outputLeft transformedOutputLeft hleftIndex hdepth hreplacement
        (raw_codedTermShiftTrace_reroot M hPA
          (raw_succ M depth) amount
          sourceCode sourceStep targetCode targetStep bound current
          (rawTermAddCode M inputLeft inputRight)
          (rawTermAddCode M transformedLeft transformedRight) htopTrace
          leftIndex inputLeft transformedLeft hleftIndex hleftLookup)
        hleftLeft hrightLeft).
    }
    assert (hdesiredRight : RawCodedTermShift M depth amount
        outputRight transformedOutputRight).
    {
      exact (hcurrent depth amount openingDepth replacement
        transformedReplacement sourceCode sourceStep targetCode targetStep
        bound rightIndex inputRight transformedRight
        outputRight transformedOutputRight hrightIndex hdepth hreplacement
        (raw_codedTermShiftTrace_reroot M hPA
          (raw_succ M depth) amount
          sourceCode sourceStep targetCode targetStep bound current
          (rawTermAddCode M inputLeft inputRight)
          (rawTermAddCode M transformedLeft transformedRight) htopTrace
          rightIndex inputRight transformedRight hrightIndex hrightLookup)
        hleftRight hrightRight).
    }
    exact (raw_codedTermShift_add M hPA depth amount
      outputLeft transformedOutputLeft outputRight transformedOutputRight
      hdesiredLeft hdesiredRight).
  + destruct htopMul as
      (leftIndex & inputLeft & transformedLeft &
       rightIndex & inputRight & transformedRight &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup &
       hinput & htransformed).
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
    assert (hdesiredLeft : RawCodedTermShift M depth amount
        outputLeft transformedOutputLeft).
    {
      exact (hcurrent depth amount openingDepth replacement
        transformedReplacement sourceCode sourceStep targetCode targetStep
        bound leftIndex inputLeft transformedLeft
        outputLeft transformedOutputLeft hleftIndex hdepth hreplacement
        (raw_codedTermShiftTrace_reroot M hPA
          (raw_succ M depth) amount
          sourceCode sourceStep targetCode targetStep bound current
          (rawTermMulCode M inputLeft inputRight)
          (rawTermMulCode M transformedLeft transformedRight) htopTrace
          leftIndex inputLeft transformedLeft hleftIndex hleftLookup)
        hleftLeft hrightLeft).
    }
    assert (hdesiredRight : RawCodedTermShift M depth amount
        outputRight transformedOutputRight).
    {
      exact (hcurrent depth amount openingDepth replacement
        transformedReplacement sourceCode sourceStep targetCode targetStep
        bound rightIndex inputRight transformedRight
        outputRight transformedOutputRight hrightIndex hdepth hreplacement
        (raw_codedTermShiftTrace_reroot M hPA
          (raw_succ M depth) amount
          sourceCode sourceStep targetCode targetStep bound current
          (rawTermMulCode M inputLeft inputRight)
          (rawTermMulCode M transformedLeft transformedRight) htopTrace
          rightIndex inputRight transformedRight hrightIndex hrightLookup)
        hleftRight hrightRight).
    }
    exact (raw_codedTermShift_mul M hPA depth amount
      outputLeft transformedOutputLeft outputRight transformedOutputRight
      hdesiredLeft hdesiredRight).
Qed.

Theorem raw_codedTermOpeningShiftInterchangeIndexBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedTermOpeningShiftInterchangeIndexBelow M current.
Proof.
  intros M hPA.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi :=
    codedTermOpeningShiftInterchangeIndexBelowTermAt (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_codedTermOpeningShiftInterchangeIndexBelowTermAt_iff M
          (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      intros depth amount openingDepth replacement transformedReplacement
        sourceCode sourceStep targetCode targetStep bound rootIndex
        input transformedInput output transformedOutput hrootIndex.
      exfalso. exact (raw_not_lt_zero M hPA rootIndex hrootIndex).
    - intros current hcurrent.
      unfold phi in hcurrent |- *.
      pose proof (proj1
        (raw_sat_codedTermOpeningShiftInterchangeIndexBelowTermAt_iff M
          (scons M current parameterEnv) (tVar 0)) hcurrent) as hraw.
      apply (proj2
        (raw_sat_codedTermOpeningShiftInterchangeIndexBelowTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hraw |- *.
      exact (raw_codedTermOpeningShiftInterchangeIndexBelow_succ
        M hPA current hraw).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedTermOpeningShiftInterchangeIndexBelowTermAt_iff M
      (scons M current parameterEnv) (tVar 0)) (hall current)) as hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

(** Public arbitrary-code interchange theorem. *)
Theorem raw_codedTermOpening_shift_interchange : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      depth amount openingDepth replacement transformedReplacement
      input transformedInput output transformedOutput,
  rawLe M openingDepth depth ->
  RawCodedTermShift M depth amount
    replacement transformedReplacement ->
  RawCodedTermShift M (raw_succ M depth) amount
    input transformedInput ->
  RawCodedTermOpening M openingDepth replacement input output ->
  RawCodedTermOpening M openingDepth transformedReplacement
    transformedInput transformedOutput ->
  RawCodedTermShift M depth amount output transformedOutput.
Proof.
  intros M hPA depth amount openingDepth replacement
    transformedReplacement input transformedInput output transformedOutput
    hdepth hreplacement
    (sourceCode & sourceStep & targetCode & targetStep &
     bound & rootIndex & htopTrace)
    hleft hright.
  exact (raw_codedTermOpeningShiftInterchangeIndexBelow_all M hPA
    (raw_succ M rootIndex)
    depth amount openingDepth replacement transformedReplacement
    sourceCode sourceStep targetCode targetStep bound rootIndex
    input transformedInput output transformedOutput
    (raw_assignment_lt_self_succ M hPA rootIndex)
    hdepth hreplacement htopTrace hleft hright).
Qed.

End PABoundedRawCodedTermOpeningShiftInterchange.
