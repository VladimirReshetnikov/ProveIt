(**
  PA-definable induction for formula shift/substitution interchange.

  The constructor inversions and term-level algebra live in
  [RawCodedFormulaShiftSubstitutionInterchange].  Importing them through an
  opaque [.vo] keeps the elaboration footprint of the seventeen-parameter
  represented invariant manageable.
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
  RawCodedProofAtomicAdequacyStandard
  RawCodedFormulaShiftTreeRealization
  RawCodedFormulaShiftTotality
  RawCodedFormulaOperationTraceConcatenation
  RawCodedFormulaOperationCompositionality
  RawCodedTermOperationCrossTraceFunctionality
  RawCodedFormulaOperationCrossTraceFunctionality
  RawCodedTermShiftProtection
  RawCodedTermOpeningShiftInterchange
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedFormulaShiftSubstitutionInterchange.

Module PABoundedRawCodedFormulaShiftSubstitutionInterchangeInvariant.

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
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedFormulaOperationTraceConcatenation.
Import PABoundedRawCodedFormulaOperationCompositionality.
Import PABoundedRawCodedTermOperationCrossTraceFunctionality.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
Import PABoundedRawCodedTermShiftProtection.
Import PABoundedRawCodedTermOpeningShiftInterchange.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedFormulaShiftSubstitutionInterchange.

(** The invariant follows the root index of the outer formula-shift trace.
    It deliberately quantifies every trace component, so it applies to
    nonstandard codes and nonstandard traversal bounds. *)
Definition RawCodedFormulaShiftSubstitutionInterchangeIndexBelow
    (M : RawPAModel) (current : M) : Prop :=
  forall depth amount openingDepth replacement transformedReplacement
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex input transformedInput output transformedOutput : M,
    rawLt M rootIndex current ->
    RawCodedTermShift M depth amount
      replacement transformedReplacement ->
    RawCodedFormulaOperationTrace M (RawCodedFormulaShiftAtom M)
      amount (raw_succ M (raw_add M depth openingDepth))
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex input transformedInput ->
    RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
      replacement openingDepth input output ->
    RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
      transformedReplacement openingDepth
      transformedInput transformedOutput ->
    RawCodedFormulaShift M (raw_add M depth openingDepth) amount
      output transformedOutput.

Arguments RawCodedFormulaShiftSubstitutionInterchangeIndexBelow M current
  : clear implicits.

Definition formulaShiftSubstitutionAll17 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll (pAll (pAll (pAll
    (pAll (pAll (pAll (pAll (pAll (pAll (pAll (pAll body)))))))))))))))).

(** Binder order is

      depth, amount, openingDepth, replacement, transformedReplacement,
      sourceCode, sourceStep, targetCode, targetStep, depthCode, depthStep,
      bound, rootIndex, input, transformedInput, output, transformedOutput,

    occupying variables 16 down to 0. *)
Definition codedFormulaShiftSubstitutionInterchangeIndexBelowTermAt
    (current : term) : formula :=
  formulaShiftSubstitutionAll17
    (pImp
      (Formula.ltTermAt (tVar 4) (liftTerm 17 current))
      (pImp
        (codedTermShiftTermAt
          (tVar 16) (tVar 15) (tVar 13) (tVar 12))
        (pImp
          (codedFormulaOperationTraceTermAt codedFormulaShiftAtomTermAt
            (tVar 15) (tSucc (tAdd (tVar 16) (tVar 14)))
            (tVar 11) (tVar 10) (tVar 9) (tVar 8)
            (tVar 7) (tVar 6) (tVar 5) (tVar 4)
            (tVar 3) (tVar 2))
          (pImp
            (codedFormulaOperationTermAt codedFormulaSubstitutionAtomTermAt
              (tVar 13) (tVar 14) (tVar 3) (tVar 1))
            (pImp
              (codedFormulaOperationTermAt
                codedFormulaSubstitutionAtomTermAt
                (tVar 12) (tVar 14) (tVar 2) (tVar 0))
              (codedFormulaShiftTermAt
                (tAdd (tVar 16) (tVar 14))
                (tVar 15) (tVar 1) (tVar 0))))))).

Lemma raw_formulaShiftSubstitution_eval_liftTerm_seventeen : forall
    (M : RawPAModel)
    a b c d f g h i j k l n o p q r s (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i
        (scons M j (scons M k (scons M l (scons M n
          (scons M o (scons M p (scons M q (scons M r
            (scons M s e)))))))))))))))))
    (liftTerm 17 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i j k l n o p q r s e t.
  unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro x.
  replace (x + 17) with
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x)))))))))))))))))
    by lia.
  reflexivity.
Qed.

Lemma raw_sat_codedFormulaShiftSubstitutionInterchangeIndexBelowTermAt_iff :
  forall (M : RawPAModel) (e : nat -> M) current,
  raw_formula_sat M e
    (codedFormulaShiftSubstitutionInterchangeIndexBelowTermAt current) <->
  RawCodedFormulaShiftSubstitutionInterchangeIndexBelow M
    (raw_term_eval M e current).
Proof.
  intros M e current.
  unfold codedFormulaShiftSubstitutionInterchangeIndexBelowTermAt,
    formulaShiftSubstitutionAll17,
    RawCodedFormulaShiftSubstitutionInterchangeIndexBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermShiftTermAt_iff.
  setoid_rewrite (raw_sat_codedFormulaOperationTraceTermAt_iff M _
    codedFormulaShiftAtomTermAt (RawCodedFormulaShiftAtom M)
    (raw_sat_codedFormulaShiftAtomTermAt_iff M)).
  repeat setoid_rewrite (raw_sat_codedFormulaOperationTermAt_iff M _
    codedFormulaSubstitutionAtomTermAt
    (RawCodedFormulaSubstitutionAtom M)
    (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M)).
  setoid_rewrite raw_sat_codedFormulaShiftTermAt_iff.
  repeat setoid_rewrite raw_formulaShiftSubstitution_eval_liftTerm_seventeen.
  cbn [raw_term_eval scons].
  split; intros h depth amount openingDepth replacement
    transformedReplacement sourceCode sourceStep targetCode targetStep
    depthCode depthStep bound rootIndex input transformedInput
    output transformedOutput;
    exact (h depth amount openingDepth replacement transformedReplacement
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex input transformedInput output transformedOutput).
Qed.

Theorem raw_codedFormulaShiftSubstitutionInterchangeIndexBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedFormulaShiftSubstitutionInterchangeIndexBelow M current ->
  RawCodedFormulaShiftSubstitutionInterchangeIndexBelow M
    (raw_succ M current).
Proof.
  intros M hPA current hcurrent depth amount openingDepth
    replacement transformedReplacement
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input transformedInput output transformedOutput
    hrootIndex hreplacement htopTrace hleft hright.
  destruct (raw_lt_succ_cases M hPA rootIndex current hrootIndex)
    as [hbefore | hrootCurrent].
  - exact (hcurrent depth amount openingDepth replacement
      transformedReplacement sourceCode sourceStep targetCode targetStep
      depthCode depthStep bound rootIndex input transformedInput
      output transformedOutput hbefore hreplacement htopTrace hleft hright).
  - subst rootIndex.
    pose proof htopTrace as htopFacts.
    destruct htopFacts as
      (_ & _ & _ & htopRoot & htopLookup & htopRows).
    pose proof (htopRows current input transformedInput
      (raw_succ M (raw_add M depth openingDepth))
      htopRoot htopLookup) as htopRow.
    destruct htopRow as
      [ htopEq
      | [ htopBot
        | [ htopImp
          | [ htopAnd
            | [ htopOr
              | [ htopAll | htopEx ] ] ] ] ] ].
  + destruct htopEq as
      (inputLeft & transformedLeft & inputRight & transformedRight &
       hinput & htransformed & htopLeft & htopRight).
    subst input. subst transformedInput.
    destruct (raw_codedFormulaOperation_eq_inversion M hPA
      (RawCodedFormulaSubstitutionAtom M) replacement openingDepth
      inputLeft inputRight output hleft)
      as (outputLeft & outputRight & houtput & hleftLeft & hleftRight).
    subst output.
    destruct (raw_codedFormulaOperation_eq_inversion M hPA
      (RawCodedFormulaSubstitutionAtom M) transformedReplacement
      openingDepth transformedLeft transformedRight transformedOutput hright)
      as (transformedOutputLeft & transformedOutputRight &
          htransformedOutput & hrightLeft & hrightRight).
    subst transformedOutput.
    exact (raw_codedFormulaShift_eq_of_term_shifts M hPA
      (raw_add M depth openingDepth) amount
      outputLeft transformedOutputLeft outputRight transformedOutputRight
      (raw_codedFormulaShift_substitutionAtom_interchange M hPA
        depth amount openingDepth replacement transformedReplacement
        inputLeft transformedLeft outputLeft transformedOutputLeft
        hreplacement htopLeft hleftLeft hrightLeft)
      (raw_codedFormulaShift_substitutionAtom_interchange M hPA
        depth amount openingDepth replacement transformedReplacement
        inputRight transformedRight outputRight transformedOutputRight
        hreplacement htopRight hleftRight hrightRight)).
  + destruct htopBot as [hinput htransformed].
    subst input. subst transformedInput.
    pose proof (raw_codedFormulaOperation_bot_inversion M hPA
      (RawCodedFormulaSubstitutionAtom M) replacement openingDepth
      output hleft) as houtput.
    pose proof (raw_codedFormulaOperation_bot_inversion M hPA
      (RawCodedFormulaSubstitutionAtom M) transformedReplacement openingDepth
      transformedOutput hright) as htransformedOutput.
    subst output. subst transformedOutput.
    destruct (raw_codedFormulaShift_bot_exists M hPA
      (raw_add M depth openingDepth) amount) as (botTarget & hbot).
    pose proof (raw_codedFormulaOperation_bot_inversion M hPA
      (RawCodedFormulaShiftAtom M) amount
      (raw_add M depth openingDepth) botTarget hbot) as hbotTarget.
    subst botTarget. exact hbot.
  + destruct htopImp as
      (leftIndex & inputLeft & transformedLeft & leftDepth &
       rightIndex & inputRight & transformedRight & rightDepth &
       hleftIndex & hleftLookup & hleftDepth &
       hrightIndex & hrightLookup & hrightDepth &
       hinput & htransformed).
    subst input. subst transformedInput.
    subst leftDepth. subst rightDepth.
    destruct (raw_codedFormulaOperation_imp_inversion M hPA
      (RawCodedFormulaSubstitutionAtom M) replacement openingDepth
      inputLeft inputRight output hleft)
      as (outputLeft & outputRight & houtput & hleftLeft & hleftRight).
    subst output.
    destruct (raw_codedFormulaOperation_imp_inversion M hPA
      (RawCodedFormulaSubstitutionAtom M) transformedReplacement
      openingDepth transformedLeft transformedRight transformedOutput hright)
      as (transformedOutputLeft & transformedOutputRight &
          htransformedOutput & hrightLeft & hrightRight).
    subst transformedOutput.
    assert (hdesiredLeft : RawCodedFormulaShift M
        (raw_add M depth openingDepth) amount
        outputLeft transformedOutputLeft).
    {
      exact (hcurrent depth amount openingDepth replacement
        transformedReplacement sourceCode sourceStep targetCode targetStep
        depthCode depthStep bound leftIndex inputLeft transformedLeft
        outputLeft transformedOutputLeft hleftIndex hreplacement
        (raw_codedFormulaOperationTrace_reroot_exact M hPA
          (RawCodedFormulaShiftAtom M) amount
          (raw_succ M (raw_add M depth openingDepth))
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          bound current
          (rawFormulaImpCode M inputLeft inputRight)
          (rawFormulaImpCode M transformedLeft transformedRight) htopTrace
          leftIndex inputLeft transformedLeft
          (raw_succ M (raw_add M depth openingDepth))
          hleftIndex hleftLookup)
        hleftLeft hrightLeft).
    }
    assert (hdesiredRight : RawCodedFormulaShift M
        (raw_add M depth openingDepth) amount
        outputRight transformedOutputRight).
    {
      exact (hcurrent depth amount openingDepth replacement
        transformedReplacement sourceCode sourceStep targetCode targetStep
        depthCode depthStep bound rightIndex inputRight transformedRight
        outputRight transformedOutputRight hrightIndex hreplacement
        (raw_codedFormulaOperationTrace_reroot_exact M hPA
          (RawCodedFormulaShiftAtom M) amount
          (raw_succ M (raw_add M depth openingDepth))
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          bound current
          (rawFormulaImpCode M inputLeft inputRight)
          (rawFormulaImpCode M transformedLeft transformedRight) htopTrace
          rightIndex inputRight transformedRight
          (raw_succ M (raw_add M depth openingDepth))
          hrightIndex hrightLookup)
        hleftRight hrightRight).
    }
    exact (raw_codedFormulaShift_binary_composition M hPA RFSBImp
      (raw_add M depth openingDepth) amount
      outputLeft transformedOutputLeft outputRight transformedOutputRight
      hdesiredLeft hdesiredRight).
  + destruct htopAnd as
      (leftIndex & inputLeft & transformedLeft & leftDepth &
       rightIndex & inputRight & transformedRight & rightDepth &
       hleftIndex & hleftLookup & hleftDepth &
       hrightIndex & hrightLookup & hrightDepth &
       hinput & htransformed).
    subst input. subst transformedInput.
    subst leftDepth. subst rightDepth.
    destruct (raw_codedFormulaOperation_and_inversion M hPA
      (RawCodedFormulaSubstitutionAtom M) replacement openingDepth
      inputLeft inputRight output hleft)
      as (outputLeft & outputRight & houtput & hleftLeft & hleftRight).
    subst output.
    destruct (raw_codedFormulaOperation_and_inversion M hPA
      (RawCodedFormulaSubstitutionAtom M) transformedReplacement
      openingDepth transformedLeft transformedRight transformedOutput hright)
      as (transformedOutputLeft & transformedOutputRight &
          htransformedOutput & hrightLeft & hrightRight).
    subst transformedOutput.
    assert (hdesiredLeft : RawCodedFormulaShift M
        (raw_add M depth openingDepth) amount
        outputLeft transformedOutputLeft).
    {
      exact (hcurrent depth amount openingDepth replacement
        transformedReplacement sourceCode sourceStep targetCode targetStep
        depthCode depthStep bound leftIndex inputLeft transformedLeft
        outputLeft transformedOutputLeft hleftIndex hreplacement
        (raw_codedFormulaOperationTrace_reroot_exact M hPA
          (RawCodedFormulaShiftAtom M) amount
          (raw_succ M (raw_add M depth openingDepth))
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          bound current
          (rawFormulaAndCode M inputLeft inputRight)
          (rawFormulaAndCode M transformedLeft transformedRight) htopTrace
          leftIndex inputLeft transformedLeft
          (raw_succ M (raw_add M depth openingDepth))
          hleftIndex hleftLookup)
        hleftLeft hrightLeft).
    }
    assert (hdesiredRight : RawCodedFormulaShift M
        (raw_add M depth openingDepth) amount
        outputRight transformedOutputRight).
    {
      exact (hcurrent depth amount openingDepth replacement
        transformedReplacement sourceCode sourceStep targetCode targetStep
        depthCode depthStep bound rightIndex inputRight transformedRight
        outputRight transformedOutputRight hrightIndex hreplacement
        (raw_codedFormulaOperationTrace_reroot_exact M hPA
          (RawCodedFormulaShiftAtom M) amount
          (raw_succ M (raw_add M depth openingDepth))
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          bound current
          (rawFormulaAndCode M inputLeft inputRight)
          (rawFormulaAndCode M transformedLeft transformedRight) htopTrace
          rightIndex inputRight transformedRight
          (raw_succ M (raw_add M depth openingDepth))
          hrightIndex hrightLookup)
        hleftRight hrightRight).
    }
    exact (raw_codedFormulaShift_binary_composition M hPA RFSBAnd
      (raw_add M depth openingDepth) amount
      outputLeft transformedOutputLeft outputRight transformedOutputRight
      hdesiredLeft hdesiredRight).
  + destruct htopOr as
      (leftIndex & inputLeft & transformedLeft & leftDepth &
       rightIndex & inputRight & transformedRight & rightDepth &
       hleftIndex & hleftLookup & hleftDepth &
       hrightIndex & hrightLookup & hrightDepth &
       hinput & htransformed).
    subst input. subst transformedInput.
    subst leftDepth. subst rightDepth.
    destruct (raw_codedFormulaOperation_or_inversion M hPA
      (RawCodedFormulaSubstitutionAtom M) replacement openingDepth
      inputLeft inputRight output hleft)
      as (outputLeft & outputRight & houtput & hleftLeft & hleftRight).
    subst output.
    destruct (raw_codedFormulaOperation_or_inversion M hPA
      (RawCodedFormulaSubstitutionAtom M) transformedReplacement
      openingDepth transformedLeft transformedRight transformedOutput hright)
      as (transformedOutputLeft & transformedOutputRight &
          htransformedOutput & hrightLeft & hrightRight).
    subst transformedOutput.
    assert (hdesiredLeft : RawCodedFormulaShift M
        (raw_add M depth openingDepth) amount
        outputLeft transformedOutputLeft).
    {
      exact (hcurrent depth amount openingDepth replacement
        transformedReplacement sourceCode sourceStep targetCode targetStep
        depthCode depthStep bound leftIndex inputLeft transformedLeft
        outputLeft transformedOutputLeft hleftIndex hreplacement
        (raw_codedFormulaOperationTrace_reroot_exact M hPA
          (RawCodedFormulaShiftAtom M) amount
          (raw_succ M (raw_add M depth openingDepth))
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          bound current
          (rawFormulaOrCode M inputLeft inputRight)
          (rawFormulaOrCode M transformedLeft transformedRight) htopTrace
          leftIndex inputLeft transformedLeft
          (raw_succ M (raw_add M depth openingDepth))
          hleftIndex hleftLookup)
        hleftLeft hrightLeft).
    }
    assert (hdesiredRight : RawCodedFormulaShift M
        (raw_add M depth openingDepth) amount
        outputRight transformedOutputRight).
    {
      exact (hcurrent depth amount openingDepth replacement
        transformedReplacement sourceCode sourceStep targetCode targetStep
        depthCode depthStep bound rightIndex inputRight transformedRight
        outputRight transformedOutputRight hrightIndex hreplacement
        (raw_codedFormulaOperationTrace_reroot_exact M hPA
          (RawCodedFormulaShiftAtom M) amount
          (raw_succ M (raw_add M depth openingDepth))
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          bound current
          (rawFormulaOrCode M inputLeft inputRight)
          (rawFormulaOrCode M transformedLeft transformedRight) htopTrace
          rightIndex inputRight transformedRight
          (raw_succ M (raw_add M depth openingDepth))
          hrightIndex hrightLookup)
        hleftRight hrightRight).
    }
    exact (raw_codedFormulaShift_binary_composition M hPA RFSBOr
      (raw_add M depth openingDepth) amount
      outputLeft transformedOutputLeft outputRight transformedOutputRight
      hdesiredLeft hdesiredRight).
  + destruct htopAll as
      (childIndex & inputChild & transformedChild & childDepth &
       hchildIndex & hchildLookup & hchildDepth & hinput & htransformed).
    subst input. subst transformedInput. subst childDepth.
    destruct (raw_codedFormulaOperation_all_inversion M hPA
      (RawCodedFormulaSubstitutionAtom M) replacement openingDepth
      inputChild output hleft)
      as (outputChild & houtput & hleftChild).
    subst output.
    destruct (raw_codedFormulaOperation_all_inversion M hPA
      (RawCodedFormulaSubstitutionAtom M) transformedReplacement
      openingDepth transformedChild transformedOutput hright)
      as (transformedOutputChild & htransformedOutput & hrightChild).
    subst transformedOutput.
    assert (htopChild : RawCodedFormulaOperationTrace M
        (RawCodedFormulaShiftAtom M) amount
        (raw_succ M (raw_add M depth (raw_succ M openingDepth)))
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound childIndex inputChild transformedChild).
    {
      rewrite raw_add_succ by exact hPA.
      exact (raw_codedFormulaOperationTrace_reroot_exact M hPA
        (RawCodedFormulaShiftAtom M) amount
        (raw_succ M (raw_add M depth openingDepth))
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound current (rawFormulaAllCode M inputChild)
        (rawFormulaAllCode M transformedChild) htopTrace
        childIndex inputChild transformedChild
        (raw_succ M (raw_succ M (raw_add M depth openingDepth)))
        hchildIndex hchildLookup).
    }
    assert (hdesiredChild : RawCodedFormulaShift M
        (raw_add M depth (raw_succ M openingDepth)) amount
        outputChild transformedOutputChild).
    {
      exact (hcurrent depth amount (raw_succ M openingDepth)
        replacement transformedReplacement
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound childIndex inputChild transformedChild
        outputChild transformedOutputChild hchildIndex hreplacement
        htopChild hleftChild hrightChild).
    }
    rewrite raw_add_succ in hdesiredChild by exact hPA.
    exact (raw_codedFormulaShift_unary_composition M hPA RFSUAll
      (raw_add M depth openingDepth) amount
      outputChild transformedOutputChild hdesiredChild).
  + destruct htopEx as
      (childIndex & inputChild & transformedChild & childDepth &
       hchildIndex & hchildLookup & hchildDepth & hinput & htransformed).
    subst input. subst transformedInput. subst childDepth.
    destruct (raw_codedFormulaOperation_ex_inversion M hPA
      (RawCodedFormulaSubstitutionAtom M) replacement openingDepth
      inputChild output hleft)
      as (outputChild & houtput & hleftChild).
    subst output.
    destruct (raw_codedFormulaOperation_ex_inversion M hPA
      (RawCodedFormulaSubstitutionAtom M) transformedReplacement
      openingDepth transformedChild transformedOutput hright)
      as (transformedOutputChild & htransformedOutput & hrightChild).
    subst transformedOutput.
    assert (htopChild : RawCodedFormulaOperationTrace M
        (RawCodedFormulaShiftAtom M) amount
        (raw_succ M (raw_add M depth (raw_succ M openingDepth)))
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound childIndex inputChild transformedChild).
    {
      rewrite raw_add_succ by exact hPA.
      exact (raw_codedFormulaOperationTrace_reroot_exact M hPA
        (RawCodedFormulaShiftAtom M) amount
        (raw_succ M (raw_add M depth openingDepth))
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound current (rawFormulaExCode M inputChild)
        (rawFormulaExCode M transformedChild) htopTrace
        childIndex inputChild transformedChild
        (raw_succ M (raw_succ M (raw_add M depth openingDepth)))
        hchildIndex hchildLookup).
    }
    assert (hdesiredChild : RawCodedFormulaShift M
        (raw_add M depth (raw_succ M openingDepth)) amount
        outputChild transformedOutputChild).
    {
      exact (hcurrent depth amount (raw_succ M openingDepth)
        replacement transformedReplacement
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound childIndex inputChild transformedChild
        outputChild transformedOutputChild hchildIndex hreplacement
        htopChild hleftChild hrightChild).
    }
    rewrite raw_add_succ in hdesiredChild by exact hPA.
    exact (raw_codedFormulaShift_unary_composition M hPA RFSUEx
      (raw_add M depth openingDepth) amount
      outputChild transformedOutputChild hdesiredChild).
Qed.

End PABoundedRawCodedFormulaShiftSubstitutionInterchangeInvariant.
