(**
  Represented formula shift commutes with one capture-avoiding substitution.

  The term algebra is provided by [RawCodedTermShiftProtection] and
  [RawCodedTermOpeningShiftInterchange].  This file lifts those laws through
  arbitrary nonstandard formula-operation traces.  Formula codes are never
  decoded in Coq; a PA-definable induction follows the root index of the
  outer shift trace.
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
  RawCodedTemplateTernaryApplicationFunctionality.

Module PABoundedRawCodedFormulaShiftSubstitutionInterchange.

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

(** Extract the source-code equation from a row known to have the wrong
    constructor.  Keeping this local makes each public inversion below state
    only its useful matching branch. *)
Ltac raw_formulaShiftSubstitution_source_mismatch M hPA row :=
  lazymatch type of row with
  | RawCodedFormulaEqOperationRow _ _ _ _ _ _ =>
      let il := fresh "inputLeft" in let ol := fresh "outputLeft" in
      let ir := fresh "inputRight" in let orr := fresh "outputRight" in
      let hin := fresh "hinput" in let hout := fresh "houtput" in
      let hl := fresh "hleft" in let hr := fresh "hright" in
      destruct row as (il & ol & ir & orr & hin & hout & hl & hr);
      exfalso; raw_standard_formula_shape_contradiction M hPA hin
  | RawCodedFormulaBotOperationRow _ _ _ =>
      let hin := fresh "hinput" in let hout := fresh "houtput" in
      destruct row as [hin hout];
      exfalso; raw_standard_formula_shape_contradiction M hPA hin
  | RawCodedFormulaBinaryOperationRow _ _ _ _ _ _ _ _ _ _ _ _ =>
      let li := fresh "leftIndex" in let il := fresh "inputLeft" in
      let ol := fresh "outputLeft" in let ld := fresh "leftDepth" in
      let ri := fresh "rightIndex" in let ir := fresh "inputRight" in
      let orr := fresh "outputRight" in let rd := fresh "rightDepth" in
      let hli := fresh "hleftIndex" in let hll := fresh "hleftLookup" in
      let hld := fresh "hleftDepth" in let hri := fresh "hrightIndex" in
      let hrl := fresh "hrightLookup" in let hrd := fresh "hrightDepth" in
      let hin := fresh "hinput" in let hout := fresh "houtput" in
      destruct row as
        (li & il & ol & ld & ri & ir & orr & rd &
         hli & hll & hld & hri & hrl & hrd & hin & hout);
      exfalso; raw_standard_formula_shape_contradiction M hPA hin
  | RawCodedFormulaUnaryOperationRow _ _ _ _ _ _ _ _ _ _ _ _ =>
      let ci := fresh "childIndex" in let cin := fresh "inputChild" in
      let cout := fresh "outputChild" in let cd := fresh "childDepth" in
      let hci := fresh "hchildIndex" in let hcl := fresh "hchildLookup" in
      let hcd := fresh "hchildDepth" in
      let hin := fresh "hinput" in let hout := fresh "houtput" in
      destruct row as
        (ci & cin & cout & cd & hci & hcl & hcd & hin & hout);
      exfalso; raw_standard_formula_shape_contradiction M hPA hin
  end.

Lemma raw_codedFormulaOperation_eq_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      atom parameter depth inputLeft inputRight output,
  RawCodedFormulaOperation M atom parameter depth
    (rawFormulaEqCode M inputLeft inputRight) output ->
  exists outputLeft outputRight,
    output = rawFormulaEqCode M outputLeft outputRight /\
    atom parameter depth inputLeft outputLeft /\
    atom parameter depth inputRight outputRight.
Proof.
  intros M hPA atom parameter depth inputLeft inputRight output
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & _ & hroot & hlookup & hrows).
  pose proof (hrows rootIndex
    (rawFormulaEqCode M inputLeft inputRight) output depth
    hroot hlookup) as hrow.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - destruct heq as
      (rowInputLeft & outputLeft & rowInputRight & outputRight &
       hinput & houtput & hleft & hright).
    unfold rawFormulaEqCode in hinput.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hinput) as [_ [hinputLeft hinputRight]].
    subst rowInputLeft. subst rowInputRight.
    exists outputLeft, outputRight. repeat split; assumption.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hbot.
  - raw_formulaShiftSubstitution_source_mismatch M hPA himp.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hand.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hor.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hall.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hex.
Qed.

Lemma raw_codedFormulaOperation_bot_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      atom parameter depth output,
  RawCodedFormulaOperation M atom parameter depth
    (rawFormulaBotCode M) output ->
  output = rawFormulaBotCode M.
Proof.
  intros M hPA atom parameter depth output
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & _ & hroot & hlookup & hrows).
  pose proof (hrows rootIndex (rawFormulaBotCode M) output depth
    hroot hlookup) as hrow.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - raw_formulaShiftSubstitution_source_mismatch M hPA heq.
  - exact (proj2 hbot).
  - raw_formulaShiftSubstitution_source_mismatch M hPA himp.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hand.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hor.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hall.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hex.
Qed.

Lemma raw_codedFormulaOperation_binary_matching_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      atom parameter depth constructor,
  RawBinaryCodeConstructorInjective M constructor ->
  forall sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex inputLeft inputRight output,
  RawCodedFormulaOperationTrace M atom parameter depth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex (constructor inputLeft inputRight) output ->
  RawCodedFormulaBinaryOperationRow M constructor
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    rootIndex (constructor inputLeft inputRight) output depth ->
  exists outputLeft outputRight,
    output = constructor outputLeft outputRight /\
    RawCodedFormulaOperation M atom parameter depth
      inputLeft outputLeft /\
    RawCodedFormulaOperation M atom parameter depth
      inputRight outputRight.
Proof.
  intros M hPA atom parameter depth constructor hinjective
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex inputLeft inputRight output htrace hrow.
  destruct hrow as
    (leftIndex & rowInputLeft & outputLeft & leftDepth &
     rightIndex & rowInputRight & outputRight & rightDepth &
     hleftIndex & hleftLookup & hleftDepth &
     hrightIndex & hrightLookup & hrightDepth & hinput & houtput).
  destruct (hinjective _ _ _ _ hinput) as [hinputLeft hinputRight].
  subst rowInputLeft. subst rowInputRight.
  subst leftDepth. subst rightDepth.
  exists outputLeft, outputRight. split; [exact houtput |]. split.
  - exact (raw_codedFormulaOperation_reroot M hPA
      atom parameter depth
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex (constructor inputLeft inputRight) output htrace
      leftIndex inputLeft outputLeft depth hleftIndex hleftLookup).
  - exact (raw_codedFormulaOperation_reroot M hPA
      atom parameter depth
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex (constructor inputLeft inputRight) output htrace
      rightIndex inputRight outputRight depth hrightIndex hrightLookup).
Qed.

Lemma raw_codedFormulaOperation_unary_matching_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      atom parameter depth constructor,
  RawUnaryCodeConstructorInjective M constructor ->
  forall sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex inputChild output,
  RawCodedFormulaOperationTrace M atom parameter depth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex (constructor inputChild) output ->
  RawCodedFormulaUnaryOperationRow M constructor
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    rootIndex (constructor inputChild) output depth ->
  exists outputChild,
    output = constructor outputChild /\
    RawCodedFormulaOperation M atom parameter (raw_succ M depth)
      inputChild outputChild.
Proof.
  intros M hPA atom parameter depth constructor hinjective
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex inputChild output htrace hrow.
  destruct hrow as
    (childIndex & rowInputChild & outputChild & childDepth &
     hchildIndex & hchildLookup & hchildDepth & hinput & houtput).
  assert (hinputChild : rowInputChild = inputChild).
  { symmetry. exact (hinjective _ _ hinput). }
  subst rowInputChild. subst childDepth.
  exists outputChild. split; [exact houtput |].
  exact (raw_codedFormulaOperation_reroot M hPA
    atom parameter depth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex (constructor inputChild) output htrace
    childIndex inputChild outputChild (raw_succ M depth)
    hchildIndex hchildLookup).
Qed.

Lemma raw_codedFormulaOperation_imp_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      atom parameter depth inputLeft inputRight output,
  RawCodedFormulaOperation M atom parameter depth
    (rawFormulaImpCode M inputLeft inputRight) output ->
  exists outputLeft outputRight,
    output = rawFormulaImpCode M outputLeft outputRight /\
    RawCodedFormulaOperation M atom parameter depth inputLeft outputLeft /\
    RawCodedFormulaOperation M atom parameter depth inputRight outputRight.
Proof.
  intros M hPA atom parameter depth inputLeft inputRight output
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & _ & hroot & hlookup & hrows).
  pose proof (hrows rootIndex
    (rawFormulaImpCode M inputLeft inputRight) output depth
    hroot hlookup) as hrow.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - raw_formulaShiftSubstitution_source_mismatch M hPA heq.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hbot.
  - exact (raw_codedFormulaOperation_binary_matching_inversion M hPA
      atom parameter depth (rawFormulaImpCode M)
      (rawFormulaImpCode_injective_cross M hPA)
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex inputLeft inputRight output htrace himp).
  - raw_formulaShiftSubstitution_source_mismatch M hPA hand.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hor.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hall.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hex.
Qed.

Lemma raw_codedFormulaOperation_and_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      atom parameter depth inputLeft inputRight output,
  RawCodedFormulaOperation M atom parameter depth
    (rawFormulaAndCode M inputLeft inputRight) output ->
  exists outputLeft outputRight,
    output = rawFormulaAndCode M outputLeft outputRight /\
    RawCodedFormulaOperation M atom parameter depth inputLeft outputLeft /\
    RawCodedFormulaOperation M atom parameter depth inputRight outputRight.
Proof.
  intros M hPA atom parameter depth inputLeft inputRight output
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & _ & hroot & hlookup & hrows).
  pose proof (hrows rootIndex
    (rawFormulaAndCode M inputLeft inputRight) output depth
    hroot hlookup) as hrow.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - raw_formulaShiftSubstitution_source_mismatch M hPA heq.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hbot.
  - raw_formulaShiftSubstitution_source_mismatch M hPA himp.
  - exact (raw_codedFormulaOperation_binary_matching_inversion M hPA
      atom parameter depth (rawFormulaAndCode M)
      (rawFormulaAndCode_injective_cross M hPA)
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex inputLeft inputRight output htrace hand).
  - raw_formulaShiftSubstitution_source_mismatch M hPA hor.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hall.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hex.
Qed.

Lemma raw_codedFormulaOperation_or_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      atom parameter depth inputLeft inputRight output,
  RawCodedFormulaOperation M atom parameter depth
    (rawFormulaOrCode M inputLeft inputRight) output ->
  exists outputLeft outputRight,
    output = rawFormulaOrCode M outputLeft outputRight /\
    RawCodedFormulaOperation M atom parameter depth inputLeft outputLeft /\
    RawCodedFormulaOperation M atom parameter depth inputRight outputRight.
Proof.
  intros M hPA atom parameter depth inputLeft inputRight output
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & _ & hroot & hlookup & hrows).
  pose proof (hrows rootIndex
    (rawFormulaOrCode M inputLeft inputRight) output depth
    hroot hlookup) as hrow.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - raw_formulaShiftSubstitution_source_mismatch M hPA heq.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hbot.
  - raw_formulaShiftSubstitution_source_mismatch M hPA himp.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hand.
  - exact (raw_codedFormulaOperation_binary_matching_inversion M hPA
      atom parameter depth (rawFormulaOrCode M)
      (rawFormulaOrCode_injective_cross M hPA)
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex inputLeft inputRight output htrace hor).
  - raw_formulaShiftSubstitution_source_mismatch M hPA hall.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hex.
Qed.

Lemma raw_codedFormulaOperation_all_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      atom parameter depth inputChild output,
  RawCodedFormulaOperation M atom parameter depth
    (rawFormulaAllCode M inputChild) output ->
  exists outputChild,
    output = rawFormulaAllCode M outputChild /\
    RawCodedFormulaOperation M atom parameter (raw_succ M depth)
      inputChild outputChild.
Proof.
  intros M hPA atom parameter depth inputChild output
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & _ & hroot & hlookup & hrows).
  pose proof (hrows rootIndex
    (rawFormulaAllCode M inputChild) output depth hroot hlookup) as hrow.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - raw_formulaShiftSubstitution_source_mismatch M hPA heq.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hbot.
  - raw_formulaShiftSubstitution_source_mismatch M hPA himp.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hand.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hor.
  - exact (raw_codedFormulaOperation_unary_matching_inversion M hPA
      atom parameter depth (rawFormulaAllCode M)
      (rawFormulaAllCode_injective_cross M hPA)
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex inputChild output htrace hall).
  - raw_formulaShiftSubstitution_source_mismatch M hPA hex.
Qed.

Lemma raw_codedFormulaOperation_ex_inversion : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      atom parameter depth inputChild output,
  RawCodedFormulaOperation M atom parameter depth
    (rawFormulaExCode M inputChild) output ->
  exists outputChild,
    output = rawFormulaExCode M outputChild /\
    RawCodedFormulaOperation M atom parameter (raw_succ M depth)
      inputChild outputChild.
Proof.
  intros M hPA atom parameter depth inputChild output
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex & htrace).
  pose proof htrace as hfacts.
  destruct hfacts as (_ & _ & _ & hroot & hlookup & hrows).
  pose proof (hrows rootIndex
    (rawFormulaExCode M inputChild) output depth hroot hlookup) as hrow.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - raw_formulaShiftSubstitution_source_mismatch M hPA heq.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hbot.
  - raw_formulaShiftSubstitution_source_mismatch M hPA himp.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hand.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hor.
  - raw_formulaShiftSubstitution_source_mismatch M hPA hall.
  - exact (raw_codedFormulaOperation_unary_matching_inversion M hPA
      atom parameter depth (rawFormulaExCode M)
      (rawFormulaExCode_injective_cross M hPA)
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex inputChild output htrace hex).
Qed.

(** Equality-leaf algebra after [openingDepth] enclosing binders.  The two
    substitution atoms reveal independently shifted replacements.  The
    general protection theorem relates those shifts at cutoff
    [depth + openingDepth], and the opening/shift theorem closes the leaf. *)
Lemma raw_codedFormulaShift_substitutionAtom_interchange : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      depth amount openingDepth replacement transformedReplacement
      input transformedInput output transformedOutput,
  RawCodedTermShift M depth amount
    replacement transformedReplacement ->
  RawCodedTermShift M (raw_succ M (raw_add M depth openingDepth)) amount
    input transformedInput ->
  RawCodedFormulaSubstitutionAtom M replacement openingDepth
    input output ->
  RawCodedFormulaSubstitutionAtom M transformedReplacement openingDepth
    transformedInput transformedOutput ->
  RawCodedTermShift M (raw_add M depth openingDepth) amount
    output transformedOutput.
Proof.
  intros M hPA depth amount openingDepth replacement
    transformedReplacement input transformedInput output transformedOutput
    hreplacement htop
    (liftedReplacement & hleftLift & hleftOpen)
    (liftedTransformedReplacement & hrightLift & hrightOpen).
  assert (hliftedReplacement : RawCodedTermShift M
      (raw_add M depth openingDepth) amount
      liftedReplacement liftedTransformedReplacement).
  {
    exact (raw_codedTermShift_protection M hPA
      depth amount openingDepth replacement transformedReplacement
      liftedReplacement liftedTransformedReplacement
      hreplacement hleftLift hrightLift).
  }
  assert (hopeningDepth : rawLe M openingDepth
      (raw_add M depth openingDepth)).
  {
    exists depth. exact (raw_add_comm M hPA openingDepth depth).
  }
  exact (raw_codedTermOpening_shift_interchange M hPA
    (raw_add M depth openingDepth) amount openingDepth
    liftedReplacement liftedTransformedReplacement
    input transformedInput output transformedOutput
    hopeningDepth hliftedReplacement htop hleftOpen hrightOpen).
Qed.

Lemma raw_codedFormulaShift_eq_of_term_shifts : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      depth amount inputLeft outputLeft inputRight outputRight,
  RawCodedTermShift M depth amount inputLeft outputLeft ->
  RawCodedTermShift M depth amount inputRight outputRight ->
  RawCodedFormulaShift M depth amount
    (rawFormulaEqCode M inputLeft inputRight)
    (rawFormulaEqCode M outputLeft outputRight).
Proof.
  intros M hPA depth amount inputLeft outputLeft inputRight outputRight
    hleft hright.
  pose proof (raw_codedFormulaShift_of_valid_tree M hPA amount
    (RFSTEq M depth inputLeft outputLeft inputRight outputRight)) as htree.
  cbn [RawFormulaShiftTreeValid rawFormulaShiftTreeDepth
    rawFormulaShiftTreeSource rawFormulaShiftTreeTarget] in htree.
  exact (htree (conj hleft hright)).
Qed.

(** The represented formula induction is compiled in the separate
    [RawCodedFormulaShiftSubstitutionInterchangeInduction] module.  Keeping
    the constructor inversions and term algebra opaque substantially lowers
    peak memory during kernel elaboration of the 17-parameter invariant. *)
End PABoundedRawCodedFormulaShiftSubstitutionInterchange.
