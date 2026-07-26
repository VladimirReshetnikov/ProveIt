(**
  PA-definable induction for substitution/substitution interchange.

  The constructor inversions and term-level algebra live in
  [RawCodedFormulaSubstitutionAtomSubstitutionInterchange].  Importing them through an
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
  RawCodedFormulaSubstitutionAtomInterchange
  RawCodedFormulaShiftSubstitutionInterchange.

Module PABoundedRawCodedFormulaSubstitutionAtomSubstitutionInterchangeInvariant.

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
Import PABoundedRawCodedFormulaSubstitutionAtomInterchange.
Import PABoundedRawCodedFormulaShiftSubstitutionInterchange.

(** The invariant follows the root index of the outer substitution trace.
    It deliberately quantifies every trace component, so it applies to
    nonstandard codes and nonstandard traversal bounds. *)
Definition RawCodedFormulaSubstitutionAtomSubstitutionInterchangeIndexBelow
    (M : RawPAModel) (current : M) : Prop :=
  forall depth outerReplacement openingDepth replacement transformedReplacement
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex input transformedInput output transformedOutput : M,
    rawLt M rootIndex current ->
    RawCodedFormulaSubstitutionAtom M outerReplacement depth
      replacement transformedReplacement ->
    RawCodedFormulaOperationTrace M (RawCodedFormulaSubstitutionAtom M)
      outerReplacement (raw_succ M (raw_add M depth openingDepth))
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex input transformedInput ->
    RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
      replacement openingDepth input output ->
    RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
      transformedReplacement openingDepth
      transformedInput transformedOutput ->
    RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
      outerReplacement (raw_add M depth openingDepth)
      output transformedOutput.

Arguments RawCodedFormulaSubstitutionAtomSubstitutionInterchangeIndexBelow M current
  : clear implicits.

Definition formulaSubstitutionAtomSubstitutionAll17 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll (pAll (pAll (pAll (pAll
    (pAll (pAll (pAll (pAll (pAll (pAll (pAll (pAll body)))))))))))))))).

(** Binder order is

      depth, outerReplacement, openingDepth, replacement, transformedReplacement,
      sourceCode, sourceStep, targetCode, targetStep, depthCode, depthStep,
      bound, rootIndex, input, transformedInput, output, transformedOutput,

    occupying variables 16 down to 0. *)
Definition codedFormulaSubstitutionAtomSubstitutionInterchangeIndexBelowTermAt
    (current : term) : formula :=
  formulaSubstitutionAtomSubstitutionAll17
    (pImp
      (Formula.ltTermAt (tVar 4) (liftTerm 17 current))
      (pImp
        (codedFormulaSubstitutionAtomTermAt
          (tVar 15) (tVar 16) (tVar 13) (tVar 12))
        (pImp
          (codedFormulaOperationTraceTermAt codedFormulaSubstitutionAtomTermAt
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
              (codedFormulaOperationTermAt
                codedFormulaSubstitutionAtomTermAt
                (tVar 15) (tAdd (tVar 16) (tVar 14))
                (tVar 1) (tVar 0))))))).

Lemma raw_formulaSubstitutionAtomSubstitution_eval_liftTerm_seventeen : forall
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

Lemma raw_sat_codedFormulaSubstitutionAtomSubstitutionInterchangeIndexBelowTermAt_iff :
  forall (M : RawPAModel) (e : nat -> M) current,
  raw_formula_sat M e
    (codedFormulaSubstitutionAtomSubstitutionInterchangeIndexBelowTermAt current) <->
  RawCodedFormulaSubstitutionAtomSubstitutionInterchangeIndexBelow M
    (raw_term_eval M e current).
Proof.
  intros M e current.
  unfold codedFormulaSubstitutionAtomSubstitutionInterchangeIndexBelowTermAt,
    formulaSubstitutionAtomSubstitutionAll17,
    RawCodedFormulaSubstitutionAtomSubstitutionInterchangeIndexBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaSubstitutionAtomTermAt_iff.
  setoid_rewrite (raw_sat_codedFormulaOperationTraceTermAt_iff M _
    codedFormulaSubstitutionAtomTermAt (RawCodedFormulaSubstitutionAtom M)
    (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M)).
  repeat setoid_rewrite (raw_sat_codedFormulaOperationTermAt_iff M _
    codedFormulaSubstitutionAtomTermAt
    (RawCodedFormulaSubstitutionAtom M)
    (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M)).
  repeat setoid_rewrite (raw_sat_codedFormulaOperationTermAt_iff M _
    codedFormulaSubstitutionAtomTermAt
    (RawCodedFormulaSubstitutionAtom M)
    (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M)).
  repeat setoid_rewrite raw_formulaSubstitutionAtomSubstitution_eval_liftTerm_seventeen.
  cbn [raw_term_eval scons].
  split; intros h depth outerReplacement openingDepth replacement
    transformedReplacement sourceCode sourceStep targetCode targetStep
    depthCode depthStep bound rootIndex input transformedInput
    output transformedOutput;
    exact (h depth outerReplacement openingDepth replacement transformedReplacement
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex input transformedInput output transformedOutput).
Qed.

Theorem raw_codedFormulaSubstitutionAtomSubstitutionInterchangeIndexBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedFormulaSubstitutionAtomSubstitutionInterchangeIndexBelow M current ->
  RawCodedFormulaSubstitutionAtomSubstitutionInterchangeIndexBelow M
    (raw_succ M current).
Proof.
  intros M hPA current hcurrent depth outerReplacement openingDepth
    replacement transformedReplacement
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input transformedInput output transformedOutput
    hrootIndex houterAtom htopTrace hleft hright.
  destruct (raw_lt_succ_cases M hPA rootIndex current hrootIndex)
    as [hbefore | hrootCurrent].
  - exact (hcurrent depth outerReplacement openingDepth replacement
      transformedReplacement sourceCode sourceStep targetCode targetStep
      depthCode depthStep bound rootIndex input transformedInput
      output transformedOutput hbefore houterAtom htopTrace hleft hright).
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
    exact (raw_codedFormulaSubstitution_eq_of_term_atoms M hPA
      outerReplacement (raw_add M depth openingDepth)
      outputLeft transformedOutputLeft outputRight transformedOutputRight
      (raw_codedFormulaSubstitutionAtom_substitutionAtom_interchange M hPA
        outerReplacement depth openingDepth replacement transformedReplacement
        inputLeft transformedLeft outputLeft transformedOutputLeft
        houterAtom htopLeft hleftLeft hrightLeft)
      (raw_codedFormulaSubstitutionAtom_substitutionAtom_interchange M hPA
        outerReplacement depth openingDepth replacement transformedReplacement
        inputRight transformedRight outputRight transformedOutputRight
        houterAtom htopRight hleftRight hrightRight)).
  + destruct htopBot as [hinput htransformed].
    subst input. subst transformedInput.
    pose proof (raw_codedFormulaOperation_bot_inversion M hPA
      (RawCodedFormulaSubstitutionAtom M) replacement openingDepth
      output hleft) as houtput.
    pose proof (raw_codedFormulaOperation_bot_inversion M hPA
      (RawCodedFormulaSubstitutionAtom M) transformedReplacement openingDepth
      transformedOutput hright) as htransformedOutput.
    subst output. subst transformedOutput.
    exact (raw_codedFormulaSubstitution_bot M hPA
      outerReplacement (raw_add M depth openingDepth)).
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
    assert (hdesiredLeft : RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
        outerReplacement (raw_add M depth openingDepth)
        outputLeft transformedOutputLeft).
    {
      exact (hcurrent depth outerReplacement openingDepth replacement
        transformedReplacement sourceCode sourceStep targetCode targetStep
        depthCode depthStep bound leftIndex inputLeft transformedLeft
        outputLeft transformedOutputLeft hleftIndex houterAtom
        (raw_codedFormulaOperationTrace_reroot_exact M hPA
          (RawCodedFormulaSubstitutionAtom M) outerReplacement
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
    assert (hdesiredRight : RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
        outerReplacement (raw_add M depth openingDepth)
        outputRight transformedOutputRight).
    {
      exact (hcurrent depth outerReplacement openingDepth replacement
        transformedReplacement sourceCode sourceStep targetCode targetStep
        depthCode depthStep bound rightIndex inputRight transformedRight
        outputRight transformedOutputRight hrightIndex houterAtom
        (raw_codedFormulaOperationTrace_reroot_exact M hPA
          (RawCodedFormulaSubstitutionAtom M) outerReplacement
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
    exact (raw_codedFormulaSubstitution_binary_composition M hPA
      outerReplacement RFSBImp (raw_add M depth openingDepth)
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
    assert (hdesiredLeft : RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
        outerReplacement (raw_add M depth openingDepth)
        outputLeft transformedOutputLeft).
    {
      exact (hcurrent depth outerReplacement openingDepth replacement
        transformedReplacement sourceCode sourceStep targetCode targetStep
        depthCode depthStep bound leftIndex inputLeft transformedLeft
        outputLeft transformedOutputLeft hleftIndex houterAtom
        (raw_codedFormulaOperationTrace_reroot_exact M hPA
          (RawCodedFormulaSubstitutionAtom M) outerReplacement
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
    assert (hdesiredRight : RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
        outerReplacement (raw_add M depth openingDepth)
        outputRight transformedOutputRight).
    {
      exact (hcurrent depth outerReplacement openingDepth replacement
        transformedReplacement sourceCode sourceStep targetCode targetStep
        depthCode depthStep bound rightIndex inputRight transformedRight
        outputRight transformedOutputRight hrightIndex houterAtom
        (raw_codedFormulaOperationTrace_reroot_exact M hPA
          (RawCodedFormulaSubstitutionAtom M) outerReplacement
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
    exact (raw_codedFormulaSubstitution_binary_composition M hPA
      outerReplacement RFSBAnd (raw_add M depth openingDepth)
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
    assert (hdesiredLeft : RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
        outerReplacement (raw_add M depth openingDepth)
        outputLeft transformedOutputLeft).
    {
      exact (hcurrent depth outerReplacement openingDepth replacement
        transformedReplacement sourceCode sourceStep targetCode targetStep
        depthCode depthStep bound leftIndex inputLeft transformedLeft
        outputLeft transformedOutputLeft hleftIndex houterAtom
        (raw_codedFormulaOperationTrace_reroot_exact M hPA
          (RawCodedFormulaSubstitutionAtom M) outerReplacement
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
    assert (hdesiredRight : RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
        outerReplacement (raw_add M depth openingDepth)
        outputRight transformedOutputRight).
    {
      exact (hcurrent depth outerReplacement openingDepth replacement
        transformedReplacement sourceCode sourceStep targetCode targetStep
        depthCode depthStep bound rightIndex inputRight transformedRight
        outputRight transformedOutputRight hrightIndex houterAtom
        (raw_codedFormulaOperationTrace_reroot_exact M hPA
          (RawCodedFormulaSubstitutionAtom M) outerReplacement
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
    exact (raw_codedFormulaSubstitution_binary_composition M hPA
      outerReplacement RFSBOr (raw_add M depth openingDepth)
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
        (RawCodedFormulaSubstitutionAtom M) outerReplacement
        (raw_succ M (raw_add M depth (raw_succ M openingDepth)))
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound childIndex inputChild transformedChild).
    {
      rewrite raw_add_succ by exact hPA.
      exact (raw_codedFormulaOperationTrace_reroot_exact M hPA
        (RawCodedFormulaSubstitutionAtom M) outerReplacement
        (raw_succ M (raw_add M depth openingDepth))
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound current (rawFormulaAllCode M inputChild)
        (rawFormulaAllCode M transformedChild) htopTrace
        childIndex inputChild transformedChild
        (raw_succ M (raw_succ M (raw_add M depth openingDepth)))
        hchildIndex hchildLookup).
    }
    assert (hdesiredChild : RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
        outerReplacement (raw_add M depth (raw_succ M openingDepth))
        outputChild transformedOutputChild).
    {
      exact (hcurrent depth outerReplacement (raw_succ M openingDepth)
        replacement transformedReplacement
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound childIndex inputChild transformedChild
        outputChild transformedOutputChild hchildIndex houterAtom
        htopChild hleftChild hrightChild).
    }
    rewrite raw_add_succ in hdesiredChild by exact hPA.
    exact (raw_codedFormulaSubstitution_unary_composition M hPA
      outerReplacement RFSUAll (raw_add M depth openingDepth)
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
        (RawCodedFormulaSubstitutionAtom M) outerReplacement
        (raw_succ M (raw_add M depth (raw_succ M openingDepth)))
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound childIndex inputChild transformedChild).
    {
      rewrite raw_add_succ by exact hPA.
      exact (raw_codedFormulaOperationTrace_reroot_exact M hPA
        (RawCodedFormulaSubstitutionAtom M) outerReplacement
        (raw_succ M (raw_add M depth openingDepth))
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound current (rawFormulaExCode M inputChild)
        (rawFormulaExCode M transformedChild) htopTrace
        childIndex inputChild transformedChild
        (raw_succ M (raw_succ M (raw_add M depth openingDepth)))
        hchildIndex hchildLookup).
    }
    assert (hdesiredChild : RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
        outerReplacement (raw_add M depth (raw_succ M openingDepth))
        outputChild transformedOutputChild).
    {
      exact (hcurrent depth outerReplacement (raw_succ M openingDepth)
        replacement transformedReplacement
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        bound childIndex inputChild transformedChild
        outputChild transformedOutputChild hchildIndex houterAtom
        htopChild hleftChild hrightChild).
    }
    rewrite raw_add_succ in hdesiredChild by exact hPA.
    exact (raw_codedFormulaSubstitution_unary_composition M hPA
      outerReplacement RFSUEx (raw_add M depth openingDepth)
      outputChild transformedOutputChild hdesiredChild).
Qed.

End PABoundedRawCodedFormulaSubstitutionAtomSubstitutionInterchangeInvariant.
