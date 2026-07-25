(**
  Concatenation of arbitrary formula-operation traces.

  Formula operations use three synchronized beta tables: a source column,
  a target column, and a binder-depth column.  A binary constructor may be
  given two independently realized children, so their tables must be joined
  before the parent row can be appended.  The bounds and indices below are
  carrier elements of an arbitrary model of PA; in particular, this is not a
  metatheoretic list append.  The second trace is copied by PA-definable
  induction, with every recursive edge shifted by the first trace's bound.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity
  RawCodedSyntaxConstructors
  RawCodedAssignment RawCodedAssignmentTotality
  RawCodedProofDescent
  RawCodedFormulaRankStep RawCodedFormulaRankTraversal
  RawCodedFormulaRankTotality
  RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthReindexing
  RawCodedPAAxiomContextSelfShift
  RawCodedFormulaShiftTreeRealization
  RawCodedFormulaShiftTotality.

Module PABoundedRawCodedFormulaOperationTraceConcatenation.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthReindexing.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaShiftTotality.

(** A simultaneous prefix extension of all three operation columns. *)
Definition RawFormulaOperationTablePrefixExtension (M : RawPAModel)
    (bound
      oldSourceCode oldSourceStep oldTargetCode oldTargetStep
      oldDepthCode oldDepthStep
      newSourceCode newSourceStep newTargetCode newTargetStep
      newDepthCode newDepthStep : M) : Prop :=
  (forall index input,
    rawLt M index bound ->
    RawCodedAssignmentLookup M oldSourceCode oldSourceStep index input ->
    RawCodedAssignmentLookup M newSourceCode newSourceStep index input) /\
  (forall index output,
    rawLt M index bound ->
    RawCodedAssignmentLookup M oldTargetCode oldTargetStep index output ->
    RawCodedAssignmentLookup M newTargetCode newTargetStep index output) /\
  (forall index depth,
    rawLt M index bound ->
    RawCodedAssignmentLookup M oldDepthCode oldDepthStep index depth ->
    RawCodedAssignmentLookup M newDepthCode newDepthStep index depth).

Arguments RawFormulaOperationTablePrefixExtension M bound
  oldSourceCode oldSourceStep oldTargetCode oldTargetStep
  oldDepthCode oldDepthStep newSourceCode newSourceStep
  newTargetCode newTargetStep newDepthCode newDepthStep : clear implicits.

Lemma raw_formulaOperationTriple_prefix_extend : forall
    (M : RawPAModel) bound
      oldSourceCode oldSourceStep oldTargetCode oldTargetStep
      oldDepthCode oldDepthStep
      newSourceCode newSourceStep newTargetCode newTargetStep
      newDepthCode newDepthStep index input output depth,
  RawFormulaOperationTablePrefixExtension M bound
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    oldDepthCode oldDepthStep newSourceCode newSourceStep
    newTargetCode newTargetStep newDepthCode newDepthStep ->
  rawLt M index bound ->
  RawCodedFormulaOperationTripleLookup M
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    oldDepthCode oldDepthStep index input output depth ->
  RawCodedFormulaOperationTripleLookup M
    newSourceCode newSourceStep newTargetCode newTargetStep
    newDepthCode newDepthStep index input output depth.
Proof.
  intros M bound oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    oldDepthCode oldDepthStep newSourceCode newSourceStep
    newTargetCode newTargetStep newDepthCode newDepthStep
    index input output depth [hsource [htarget hdepth]] hindex
    [hinput [houtput hrowDepth]].
  repeat split.
  - exact (hsource index input hindex hinput).
  - exact (htarget index output hindex houtput).
  - exact (hdepth index depth hindex hrowDepth).
Qed.

Lemma raw_formulaOperationBinaryRow_prefix_extend : forall
    (M : RawPAModel), RawPASatisfies M -> forall bound current
      (constructor : M -> M -> M)
      oldSourceCode oldSourceStep oldTargetCode oldTargetStep
      oldDepthCode oldDepthStep
      newSourceCode newSourceStep newTargetCode newTargetStep
      newDepthCode newDepthStep input output depth,
  RawFormulaOperationTablePrefixExtension M bound
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    oldDepthCode oldDepthStep newSourceCode newSourceStep
    newTargetCode newTargetStep newDepthCode newDepthStep ->
  rawLe M current bound ->
  RawCodedFormulaBinaryOperationRow M constructor
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    oldDepthCode oldDepthStep current input output depth ->
  RawCodedFormulaBinaryOperationRow M constructor
    newSourceCode newSourceStep newTargetCode newTargetStep
    newDepthCode newDepthStep current input output depth.
Proof.
  intros M hPA bound current constructor
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    oldDepthCode oldDepthStep newSourceCode newSourceStep
    newTargetCode newTargetStep newDepthCode newDepthStep
    input output depth hext hcurrent
    (leftIndex & inputLeft & outputLeft & leftDepth &
     rightIndex & inputRight & outputRight & rightDepth &
     hleft & hleftLookup & hleftDepth & hright & hrightLookup &
     hrightDepth & hinput & houtput).
  exists leftIndex, inputLeft, outputLeft, leftDepth,
    rightIndex, inputRight, outputRight, rightDepth.
  split; [exact hleft |]. split.
  - apply (raw_formulaOperationTriple_prefix_extend M bound
      oldSourceCode oldSourceStep oldTargetCode oldTargetStep
      oldDepthCode oldDepthStep newSourceCode newSourceStep
      newTargetCode newTargetStep newDepthCode newDepthStep
      leftIndex inputLeft outputLeft leftDepth hext).
    + exact (raw_lt_le_trans_pair M hPA
        leftIndex current bound hleft hcurrent).
    + exact hleftLookup.
  - split; [exact hleftDepth |]. split; [exact hright |]. split.
    + apply (raw_formulaOperationTriple_prefix_extend M bound
        oldSourceCode oldSourceStep oldTargetCode oldTargetStep
        oldDepthCode oldDepthStep newSourceCode newSourceStep
        newTargetCode newTargetStep newDepthCode newDepthStep
        rightIndex inputRight outputRight rightDepth hext).
      * exact (raw_lt_le_trans_pair M hPA
          rightIndex current bound hright hcurrent).
      * exact hrightLookup.
    + repeat split; assumption.
Qed.

Lemma raw_formulaOperationUnaryRow_prefix_extend : forall
    (M : RawPAModel), RawPASatisfies M -> forall bound current
      (constructor : M -> M)
      oldSourceCode oldSourceStep oldTargetCode oldTargetStep
      oldDepthCode oldDepthStep
      newSourceCode newSourceStep newTargetCode newTargetStep
      newDepthCode newDepthStep input output depth,
  RawFormulaOperationTablePrefixExtension M bound
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    oldDepthCode oldDepthStep newSourceCode newSourceStep
    newTargetCode newTargetStep newDepthCode newDepthStep ->
  rawLe M current bound ->
  RawCodedFormulaUnaryOperationRow M constructor
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    oldDepthCode oldDepthStep current input output depth ->
  RawCodedFormulaUnaryOperationRow M constructor
    newSourceCode newSourceStep newTargetCode newTargetStep
    newDepthCode newDepthStep current input output depth.
Proof.
  intros M hPA bound current constructor
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    oldDepthCode oldDepthStep newSourceCode newSourceStep
    newTargetCode newTargetStep newDepthCode newDepthStep
    input output depth hext hcurrent
    (childIndex & inputChild & outputChild & childDepth &
     hchild & hchildLookup & hchildDepth & hinput & houtput).
  exists childIndex, inputChild, outputChild, childDepth.
  split; [exact hchild |]. split.
  - apply (raw_formulaOperationTriple_prefix_extend M bound
      oldSourceCode oldSourceStep oldTargetCode oldTargetStep
      oldDepthCode oldDepthStep newSourceCode newSourceStep
      newTargetCode newTargetStep newDepthCode newDepthStep
      childIndex inputChild outputChild childDepth hext).
    + exact (raw_lt_le_trans_pair M hPA
        childIndex current bound hchild hcurrent).
    + exact hchildLookup.
  - repeat split; assumption.
Qed.

Lemma raw_formulaOperationTraversalRow_prefix_extend : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop) parameter bound current
      oldSourceCode oldSourceStep oldTargetCode oldTargetStep
      oldDepthCode oldDepthStep
      newSourceCode newSourceStep newTargetCode newTargetStep
      newDepthCode newDepthStep input output depth,
  RawFormulaOperationTablePrefixExtension M bound
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    oldDepthCode oldDepthStep newSourceCode newSourceStep
    newTargetCode newTargetStep newDepthCode newDepthStep ->
  rawLe M current bound ->
  RawCodedFormulaOperationTraversalRow M atom parameter
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    oldDepthCode oldDepthStep current input output depth ->
  RawCodedFormulaOperationTraversalRow M atom parameter
    newSourceCode newSourceStep newTargetCode newTargetStep
    newDepthCode newDepthStep current input output depth.
Proof.
  intros M hPA atom parameter bound current
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    oldDepthCode oldDepthStep newSourceCode newSourceStep
    newTargetCode newTargetStep newDepthCode newDepthStep
    input output depth hext hcurrent hrow.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]];
    [left; exact heq
    |right; left; exact hbot
    |right; right; left
    |right; right; right; left
    |right; right; right; right; left
    |right; right; right; right; right; left
    |right; right; right; right; right; right].
  - eapply raw_formulaOperationBinaryRow_prefix_extend; eassumption.
  - eapply raw_formulaOperationBinaryRow_prefix_extend; eassumption.
  - eapply raw_formulaOperationBinaryRow_prefix_extend; eassumption.
  - eapply raw_formulaOperationUnaryRow_prefix_extend; eassumption.
  - eapply raw_formulaOperationUnaryRow_prefix_extend; eassumption.
Qed.

(** [offset + index] in a target table contains the complete source triple
    at [index].  Keeping this as one four-variable formula is what makes the
    three synchronized columns survive nonstandard induction. *)
Definition RawFormulaOperationOffsetEmbedding (M : RawPAModel)
    (offset current
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep
      targetSourceCode targetSourceStep targetTargetCode targetTargetStep
      targetDepthCode targetDepthStep : M) : Prop :=
  forall index input output depth,
    rawLt M index current ->
    RawCodedFormulaOperationTripleLookup M
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep index input output depth ->
    RawCodedFormulaOperationTripleLookup M
      targetSourceCode targetSourceStep targetTargetCode targetTargetStep
      targetDepthCode targetDepthStep (raw_add M offset index)
      input output depth.

Arguments RawFormulaOperationOffsetEmbedding M offset current
  sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
  sourceDepthCode sourceDepthStep targetSourceCode targetSourceStep
  targetTargetCode targetTargetStep targetDepthCode targetDepthStep
  : clear implicits.

Definition formulaOperationOffsetEmbeddingTermAt
    (offset current
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep
      targetSourceCode targetSourceStep targetTargetCode targetTargetStep
      targetDepthCode targetDepthStep : term) : formula :=
  pAll (pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 3) (liftTerm 4 current))
      (pImp
        (codedFormulaOperationTripleLookupTermAt
          (liftTerm 4 sourceSourceCode) (liftTerm 4 sourceSourceStep)
          (liftTerm 4 sourceTargetCode) (liftTerm 4 sourceTargetStep)
          (liftTerm 4 sourceDepthCode) (liftTerm 4 sourceDepthStep)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))
        (codedFormulaOperationTripleLookupTermAt
          (liftTerm 4 targetSourceCode) (liftTerm 4 targetSourceStep)
          (liftTerm 4 targetTargetCode) (liftTerm 4 targetTargetStep)
          (liftTerm 4 targetDepthCode) (liftTerm 4 targetDepthStep)
          (tAdd (liftTerm 4 offset) (tVar 3))
          (tVar 2) (tVar 1) (tVar 0))))))).

Lemma raw_sat_formulaOperationOffsetEmbeddingTermAt_iff : forall
    (M : RawPAModel) e offset current
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep
      targetSourceCode targetSourceStep targetTargetCode targetTargetStep
      targetDepthCode targetDepthStep,
  raw_formula_sat M e
    (formulaOperationOffsetEmbeddingTermAt offset current
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep
      targetSourceCode targetSourceStep targetTargetCode targetTargetStep
      targetDepthCode targetDepthStep) <->
  RawFormulaOperationOffsetEmbedding M
    (raw_term_eval M e offset) (raw_term_eval M e current)
    (raw_term_eval M e sourceSourceCode)
    (raw_term_eval M e sourceSourceStep)
    (raw_term_eval M e sourceTargetCode)
    (raw_term_eval M e sourceTargetStep)
    (raw_term_eval M e sourceDepthCode)
    (raw_term_eval M e sourceDepthStep)
    (raw_term_eval M e targetSourceCode)
    (raw_term_eval M e targetSourceStep)
    (raw_term_eval M e targetTargetCode)
    (raw_term_eval M e targetTargetStep)
    (raw_term_eval M e targetDepthCode)
    (raw_term_eval M e targetDepthStep).
Proof.
  intros. unfold formulaOperationOffsetEmbeddingTermAt,
    RawFormulaOperationOffsetEmbedding.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaOperationTripleLookupTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_four.
  cbn [raw_term_eval scons].
  split; intros h index input output depth hindex hlookup;
    specialize (h index input output depth hindex hlookup).
  - rewrite (raw_rankTraversal_eval_liftTerm_four M
      depth output input index e offset) in h.
    exact h.
  - rewrite (raw_rankTraversal_eval_liftTerm_four M
      depth output input index e offset).
    exact h.
Qed.

Lemma raw_formulaOperationBinaryRow_offset : forall
    (M : RawPAModel), RawPASatisfies M -> forall offset current
      (constructor : M -> M -> M)
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep
      targetSourceCode targetSourceStep targetTargetCode targetTargetStep
      targetDepthCode targetDepthStep input output depth,
  RawFormulaOperationOffsetEmbedding M offset current
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep targetSourceCode targetSourceStep
    targetTargetCode targetTargetStep targetDepthCode targetDepthStep ->
  RawCodedFormulaBinaryOperationRow M constructor
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep current input output depth ->
  RawCodedFormulaBinaryOperationRow M constructor
    targetSourceCode targetSourceStep targetTargetCode targetTargetStep
    targetDepthCode targetDepthStep (raw_add M offset current)
    input output depth.
Proof.
  intros M hPA offset current constructor
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep targetSourceCode targetSourceStep
    targetTargetCode targetTargetStep targetDepthCode targetDepthStep
    input output depth hembed
    (leftIndex & inputLeft & outputLeft & leftDepth &
     rightIndex & inputRight & outputRight & rightDepth &
     hleft & hleftLookup & hleftDepth & hright & hrightLookup &
     hrightDepth & hinput & houtput).
  exists (raw_add M offset leftIndex), inputLeft, outputLeft, leftDepth,
    (raw_add M offset rightIndex), inputRight, outputRight, rightDepth.
  split.
  - exact (raw_lt_add_left_fixedTruth M hPA offset
      leftIndex current hleft).
  - split; [exact (hembed leftIndex inputLeft outputLeft leftDepth
      hleft hleftLookup) |].
    split; [exact hleftDepth |]. split.
    + exact (raw_lt_add_left_fixedTruth M hPA offset
        rightIndex current hright).
    + split; [exact (hembed rightIndex inputRight outputRight rightDepth
        hright hrightLookup) |].
      repeat split; assumption.
Qed.

Lemma raw_formulaOperationUnaryRow_offset : forall
    (M : RawPAModel), RawPASatisfies M -> forall offset current
      (constructor : M -> M)
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep
      targetSourceCode targetSourceStep targetTargetCode targetTargetStep
      targetDepthCode targetDepthStep input output depth,
  RawFormulaOperationOffsetEmbedding M offset current
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep targetSourceCode targetSourceStep
    targetTargetCode targetTargetStep targetDepthCode targetDepthStep ->
  RawCodedFormulaUnaryOperationRow M constructor
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep current input output depth ->
  RawCodedFormulaUnaryOperationRow M constructor
    targetSourceCode targetSourceStep targetTargetCode targetTargetStep
    targetDepthCode targetDepthStep (raw_add M offset current)
    input output depth.
Proof.
  intros M hPA offset current constructor
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep targetSourceCode targetSourceStep
    targetTargetCode targetTargetStep targetDepthCode targetDepthStep
    input output depth hembed
    (childIndex & inputChild & outputChild & childDepth &
     hchild & hchildLookup & hchildDepth & hinput & houtput).
  exists (raw_add M offset childIndex), inputChild, outputChild, childDepth.
  split.
  - exact (raw_lt_add_left_fixedTruth M hPA offset
      childIndex current hchild).
  - split; [exact (hembed childIndex inputChild outputChild childDepth
      hchild hchildLookup) |].
    repeat split; assumption.
Qed.

Lemma raw_formulaOperationTraversalRow_offset : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop) parameter offset current
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep
      targetSourceCode targetSourceStep targetTargetCode targetTargetStep
      targetDepthCode targetDepthStep input output depth,
  RawFormulaOperationOffsetEmbedding M offset current
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep targetSourceCode targetSourceStep
    targetTargetCode targetTargetStep targetDepthCode targetDepthStep ->
  RawCodedFormulaOperationTraversalRow M atom parameter
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep current input output depth ->
  RawCodedFormulaOperationTraversalRow M atom parameter
    targetSourceCode targetSourceStep targetTargetCode targetTargetStep
    targetDepthCode targetDepthStep (raw_add M offset current)
    input output depth.
Proof.
  intros M hPA atom parameter offset current
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep targetSourceCode targetSourceStep
    targetTargetCode targetTargetStep targetDepthCode targetDepthStep
    input output depth hembed hrow.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]];
    [left; exact heq
    |right; left; exact hbot
    |right; right; left
    |right; right; right; left
    |right; right; right; right; left
    |right; right; right; right; right; left
    |right; right; right; right; right; right].
  - eapply raw_formulaOperationBinaryRow_offset; eassumption.
  - eapply raw_formulaOperationBinaryRow_offset; eassumption.
  - eapply raw_formulaOperationBinaryRow_offset; eassumption.
  - eapply raw_formulaOperationUnaryRow_offset; eassumption.
  - eapply raw_formulaOperationUnaryRow_offset; eassumption.
Qed.

(** A bundle is a trace without a distinguished root. *)
Definition RawFormulaOperationTraversalBundle (M : RawPAModel)
    (atom : M -> M -> M -> M -> Prop)
    (parameter sourceCode sourceStep targetCode targetStep
      depthCode depthStep bound : M) : Prop :=
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep bound /\
  RawCodedAssignmentDefinedThrough M targetCode targetStep bound /\
  RawCodedAssignmentDefinedThrough M depthCode depthStep bound /\
  RawCodedFormulaOperationRows M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep bound.

Arguments RawFormulaOperationTraversalBundle M atom parameter
  sourceCode sourceStep targetCode targetStep depthCode depthStep bound
  : clear implicits.

Definition formulaOperationTraversalBundleTermAt
    (atom : term -> term -> term -> term -> formula)
    (parameter sourceCode sourceStep targetCode targetStep
      depthCode depthStep bound : term) : formula :=
  operationAnd4
    (codedAssignmentDefinedThroughTermAt sourceCode sourceStep bound)
    (codedAssignmentDefinedThroughTermAt targetCode targetStep bound)
    (codedAssignmentDefinedThroughTermAt depthCode depthStep bound)
    (codedFormulaOperationRowsTermAt atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep bound).

Lemma raw_sat_formulaOperationTraversalBundleTermAt_iff : forall
    (M : RawPAModel) e
    (atom : term -> term -> term -> term -> formula)
    (rawAtom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atom parameter depth input output) <->
    rawAtom (raw_term_eval M e' parameter)
      (raw_term_eval M e' depth) (raw_term_eval M e' input)
      (raw_term_eval M e' output)) ->
  forall parameter sourceCode sourceStep targetCode targetStep
      depthCode depthStep bound,
  raw_formula_sat M e
    (formulaOperationTraversalBundleTermAt atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep bound)
  <->
  RawFormulaOperationTraversalBundle M rawAtom
    (raw_term_eval M e parameter)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e bound).
Proof.
  intros M e atom rawAtom hatom.
  intros. unfold formulaOperationTraversalBundleTermAt,
    RawFormulaOperationTraversalBundle, operationAnd4.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  rewrite (raw_sat_codedFormulaOperationRowsTermAt_iff
    M e atom rawAtom hatom). reflexivity.
Qed.

Theorem raw_formulaOperationTraversalBundle_append : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop) parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound input output depth,
  RawFormulaOperationTraversalBundle M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep bound ->
  RawCodedFormulaOperationTraversalRow M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound input output depth ->
  exists newSourceCode newSourceStep newTargetCode newTargetStep
      newDepthCode newDepthStep : M,
    RawFormulaOperationTraversalBundle M atom parameter
      newSourceCode newSourceStep newTargetCode newTargetStep
      newDepthCode newDepthStep (raw_succ M bound) /\
    RawFormulaOperationTablePrefixExtension M bound
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      newSourceCode newSourceStep newTargetCode newTargetStep
      newDepthCode newDepthStep /\
    RawCodedFormulaOperationTripleLookup M
      newSourceCode newSourceStep newTargetCode newTargetStep
      newDepthCode newDepthStep bound input output depth.
Proof.
  intros M hPA atom parameter sourceCode sourceStep targetCode targetStep
    depthCode depthStep bound input output depth
    [hsourceDefined [htargetDefined [hdepthDefined hrows]]] hclosed.
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    sourceCode sourceStep bound input hsourceDefined)
    as (newSourceCode & newSourceStep & hnewSourceDefined &
        hsourcePrefix & hsourceRoot).
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    targetCode targetStep bound output htargetDefined)
    as (newTargetCode & newTargetStep & hnewTargetDefined &
        htargetPrefix & htargetRoot).
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    depthCode depthStep bound depth hdepthDefined)
    as (newDepthCode & newDepthStep & hnewDepthDefined &
        hdepthPrefix & hdepthRoot).
  set (hext := conj hsourcePrefix (conj htargetPrefix hdepthPrefix)).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    newDepthCode, newDepthStep.
  split.
  - split; [exact hnewSourceDefined |].
    split; [exact hnewTargetDefined |].
    split; [exact hnewDepthDefined |].
    intros index rowInput rowOutput rowDepth hindex hlookup.
    destruct (raw_lt_succ_cases M hPA index bound hindex)
      as [hindexOld | ->].
    + destruct (hsourceDefined index hindexOld)
        as [oldInput holdInput].
      destruct (htargetDefined index hindexOld)
        as [oldOutput holdOutput].
      destruct (hdepthDefined index hindexOld)
        as [oldDepth holdDepth].
      assert (hnewOld : RawCodedFormulaOperationTripleLookup M
          newSourceCode newSourceStep newTargetCode newTargetStep
          newDepthCode newDepthStep index oldInput oldOutput oldDepth).
      {
        apply (raw_formulaOperationTriple_prefix_extend M bound
          sourceCode sourceStep targetCode targetStep depthCode depthStep
          newSourceCode newSourceStep newTargetCode newTargetStep
          newDepthCode newDepthStep index oldInput oldOutput oldDepth
          hext hindexOld).
        repeat split; assumption.
      }
      destruct hlookup as [hlookupInput [hlookupOutput hlookupDepth]].
      destruct hnewOld as [hnewOldInput [hnewOldOutput hnewOldDepth]].
      assert (hinputEq : rowInput = oldInput).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newSourceCode newSourceStep index rowInput oldInput
          hlookupInput hnewOldInput).
      }
      assert (houtputEq : rowOutput = oldOutput).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newTargetCode newTargetStep index rowOutput oldOutput
          hlookupOutput hnewOldOutput).
      }
      assert (hdepthEq : rowDepth = oldDepth).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newDepthCode newDepthStep index rowDepth oldDepth
          hlookupDepth hnewOldDepth).
      }
      subst rowInput. subst rowOutput. subst rowDepth.
      apply (raw_formulaOperationTraversalRow_prefix_extend M hPA
        atom parameter bound index
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        newDepthCode newDepthStep oldInput oldOutput oldDepth hext).
      * exact (raw_lt_to_le M index bound hindexOld).
      * apply (hrows index oldInput oldOutput oldDepth hindexOld).
        repeat split; assumption.
    + destruct hlookup as [hlookupInput [hlookupOutput hlookupDepth]].
      assert (hinputEq : rowInput = input).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newSourceCode newSourceStep bound rowInput input
          hlookupInput hsourceRoot).
      }
      assert (houtputEq : rowOutput = output).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newTargetCode newTargetStep bound rowOutput output
          hlookupOutput htargetRoot).
      }
      assert (hdepthEq : rowDepth = depth).
      {
        exact (raw_codedAssignmentLookup_functional M hPA
          newDepthCode newDepthStep bound rowDepth depth
          hlookupDepth hdepthRoot).
      }
      subst rowInput. subst rowOutput. subst rowDepth.
      apply (raw_formulaOperationTraversalRow_prefix_extend M hPA
        atom parameter bound bound
        sourceCode sourceStep targetCode targetStep depthCode depthStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        newDepthCode newDepthStep input output depth hext).
      * apply raw_rank_le_refl. exact hPA.
      * exact hclosed.
  - split; [exact hext |]. repeat split; assumption.
Qed.

(** The represented invariant used while copying the second trace.  The
    implication guard is essential because definable induction ranges over
    every carrier element, while source rows exist only below [sourceBound]. *)
Definition RawFormulaOperationCopyState (M : RawPAModel)
    (atom : M -> M -> M -> M -> Prop)
    (parameter
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep sourceBound offset
      initialRootIndex initialInput initialOutput initialDepth current : M)
    : Prop :=
  rawLe M current sourceBound ->
  exists targetSourceCode targetSourceStep targetTargetCode targetTargetStep
      targetDepthCode targetDepthStep : M,
    RawFormulaOperationTraversalBundle M atom parameter
      targetSourceCode targetSourceStep targetTargetCode targetTargetStep
      targetDepthCode targetDepthStep (raw_add M offset current) /\
    RawCodedFormulaOperationTripleLookup M
      targetSourceCode targetSourceStep targetTargetCode targetTargetStep
      targetDepthCode targetDepthStep
      initialRootIndex initialInput initialOutput initialDepth /\
    RawFormulaOperationOffsetEmbedding M offset current
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep
      targetSourceCode targetSourceStep targetTargetCode targetTargetStep
      targetDepthCode targetDepthStep.

Arguments RawFormulaOperationCopyState M atom parameter
  sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
  sourceDepthCode sourceDepthStep sourceBound offset initialRootIndex
  initialInput initialOutput initialDepth current : clear implicits.

Definition formulaOperationCopyStateTermAt
    (atom : term -> term -> term -> term -> formula)
    (parameter
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep sourceBound offset
      initialRootIndex initialInput initialOutput initialDepth current : term)
    : formula :=
  pImp
    (Formula.leTermAt current sourceBound)
    (operationEx6
      (operationAnd3
        (formulaOperationTraversalBundleTermAt atom
          (liftTerm 6 parameter)
          (tVar 5) (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0)
          (tAdd (liftTerm 6 offset) (liftTerm 6 current)))
        (codedFormulaOperationTripleLookupTermAt
          (tVar 5) (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0)
          (liftTerm 6 initialRootIndex) (liftTerm 6 initialInput)
          (liftTerm 6 initialOutput) (liftTerm 6 initialDepth))
        (formulaOperationOffsetEmbeddingTermAt
          (liftTerm 6 offset) (liftTerm 6 current)
          (liftTerm 6 sourceSourceCode) (liftTerm 6 sourceSourceStep)
          (liftTerm 6 sourceTargetCode) (liftTerm 6 sourceTargetStep)
          (liftTerm 6 sourceDepthCode) (liftTerm 6 sourceDepthStep)
          (tVar 5) (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0)))).

Lemma raw_sat_formulaOperationCopyStateTermAt_iff : forall
    (M : RawPAModel) e
    (atom : term -> term -> term -> term -> formula)
    (rawAtom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atom parameter depth input output) <->
    rawAtom (raw_term_eval M e' parameter)
      (raw_term_eval M e' depth) (raw_term_eval M e' input)
      (raw_term_eval M e' output)) ->
  forall parameter
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep sourceBound offset
      initialRootIndex initialInput initialOutput initialDepth current,
  raw_formula_sat M e
    (formulaOperationCopyStateTermAt atom parameter
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep sourceBound offset
      initialRootIndex initialInput initialOutput initialDepth current)
  <->
  RawFormulaOperationCopyState M rawAtom
    (raw_term_eval M e parameter)
    (raw_term_eval M e sourceSourceCode)
    (raw_term_eval M e sourceSourceStep)
    (raw_term_eval M e sourceTargetCode)
    (raw_term_eval M e sourceTargetStep)
    (raw_term_eval M e sourceDepthCode)
    (raw_term_eval M e sourceDepthStep)
    (raw_term_eval M e sourceBound) (raw_term_eval M e offset)
    (raw_term_eval M e initialRootIndex)
    (raw_term_eval M e initialInput) (raw_term_eval M e initialOutput)
    (raw_term_eval M e initialDepth) (raw_term_eval M e current).
Proof.
  intros M e atom rawAtom hatom.
  intros. unfold formulaOperationCopyStateTermAt, operationEx6,
    operationAnd3, RawFormulaOperationCopyState.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank.
  setoid_rewrite (raw_sat_formulaOperationTraversalBundleTermAt_iff
    M _ atom rawAtom hatom).
  setoid_rewrite raw_sat_codedFormulaOperationTripleLookupTermAt_iff.
  setoid_rewrite raw_sat_formulaOperationOffsetEmbeddingTermAt_iff.
  cbn [raw_term_eval scons].
  split; intros h hle;
    destruct (h hle) as
      (targetSourceCode & targetSourceStep & targetTargetCode &
       targetTargetStep & targetDepthCode & targetDepthStep & hresult);
    exists targetSourceCode, targetSourceStep, targetTargetCode,
      targetTargetStep, targetDepthCode, targetDepthStep.
  - repeat rewrite (raw_operation_eval_liftTerm_six M
      targetDepthStep targetDepthCode targetTargetStep targetTargetCode
      targetSourceStep targetSourceCode e) in hresult.
    exact hresult.
  - repeat rewrite (raw_operation_eval_liftTerm_six M
      targetDepthStep targetDepthCode targetTargetStep targetTargetCode
      targetSourceStep targetSourceCode e).
    exact hresult.
Qed.

Lemma raw_formulaOperationOffsetEmbedding_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall offset
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep
      targetSourceCode targetSourceStep targetTargetCode targetTargetStep
      targetDepthCode targetDepthStep,
  RawFormulaOperationOffsetEmbedding M offset (raw_zero M)
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep targetSourceCode targetSourceStep
    targetTargetCode targetTargetStep targetDepthCode targetDepthStep.
Proof.
  intros M hPA offset sourceSourceCode sourceSourceStep
    sourceTargetCode sourceTargetStep sourceDepthCode sourceDepthStep
    targetSourceCode targetSourceStep targetTargetCode targetTargetStep
    targetDepthCode targetDepthStep index input output depth hindex _.
  exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

Lemma raw_formulaOperationCopyState_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop) parameter
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep sourceBound offset
      initialSourceCode initialSourceStep initialTargetCode initialTargetStep
      initialDepthCode initialDepthStep
      initialRootIndex initialInput initialOutput initialDepth,
  RawFormulaOperationTraversalBundle M atom parameter
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep
    initialDepthCode initialDepthStep offset ->
  RawCodedFormulaOperationTripleLookup M
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep
    initialDepthCode initialDepthStep
    initialRootIndex initialInput initialOutput initialDepth ->
  RawFormulaOperationCopyState M atom parameter
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep sourceBound offset
    initialRootIndex initialInput initialOutput initialDepth (raw_zero M).
Proof.
  intros M hPA atom parameter
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep sourceBound offset
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep
    initialDepthCode initialDepthStep
    initialRootIndex initialInput initialOutput initialDepth
    hinitialBundle hinitialRoot _.
  exists initialSourceCode, initialSourceStep, initialTargetCode,
    initialTargetStep, initialDepthCode, initialDepthStep.
  rewrite raw_assignmentTotality_add_zero_right by exact hPA.
  split; [exact hinitialBundle |]. split; [exact hinitialRoot |].
  exact (raw_formulaOperationOffsetEmbedding_zero M hPA offset
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep initialSourceCode initialSourceStep
    initialTargetCode initialTargetStep initialDepthCode initialDepthStep).
Qed.

Lemma raw_formulaOperationCopyState_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atom : M -> M -> M -> M -> Prop) parameter
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep sourceBound sourceRootIndex
      sourceInput sourceOutput sourceRootDepth
      offset initialRootIndex initialInput initialOutput initialDepth current,
  RawCodedFormulaOperationTrace M atom parameter sourceRootDepth
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep sourceBound sourceRootIndex
    sourceInput sourceOutput ->
  rawLt M initialRootIndex offset ->
  RawFormulaOperationCopyState M atom parameter
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep sourceBound offset
    initialRootIndex initialInput initialOutput initialDepth current ->
  RawFormulaOperationCopyState M atom parameter
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep sourceBound offset
    initialRootIndex initialInput initialOutput initialDepth
    (raw_succ M current).
Proof.
  intros M hPA atom parameter
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep sourceBound sourceRootIndex
    sourceInput sourceOutput sourceRootDepth
    offset initialRootIndex initialInput initialOutput initialDepth current
    hsource hinitialBelow hcurrent hsuccLe.
  destruct hsource as
    [hsourceSourceDefined
      [hsourceTargetDefined
        [hsourceDepthDefined
          [hsourceRootBelow [hsourceRoot hsourceRows]]]]].
  assert (hcurrentBelow : rawLt M current sourceBound).
  { exact (raw_rank_lt_of_succ_le M hPA current sourceBound hsuccLe). }
  assert (hcurrentLe : rawLe M current sourceBound).
  { exact (raw_lt_to_le M current sourceBound hcurrentBelow). }
  destruct (hcurrent hcurrentLe) as
    (targetSourceCode & targetSourceStep & targetTargetCode &
     targetTargetStep & targetDepthCode & targetDepthStep &
     htargetBundle & hinitialRoot & hembed).
  destruct (hsourceSourceDefined current hcurrentBelow)
    as [rowInput hrowInput].
  destruct (hsourceTargetDefined current hcurrentBelow)
    as [rowOutput hrowOutput].
  destruct (hsourceDepthDefined current hcurrentBelow)
    as [rowDepth hrowDepth].
  assert (hsourceLookup : RawCodedFormulaOperationTripleLookup M
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep current rowInput rowOutput rowDepth).
  { repeat split; assumption. }
  pose proof (hsourceRows current rowInput rowOutput rowDepth
    hcurrentBelow hsourceLookup) as hsourceRow.
  pose proof (raw_formulaOperationTraversalRow_offset M hPA
    atom parameter offset current
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep targetSourceCode targetSourceStep
    targetTargetCode targetTargetStep targetDepthCode targetDepthStep
    rowInput rowOutput rowDepth hembed hsourceRow) as htargetRow.
  destruct (raw_formulaOperationTraversalBundle_append M hPA
    atom parameter targetSourceCode targetSourceStep
    targetTargetCode targetTargetStep targetDepthCode targetDepthStep
    (raw_add M offset current) rowInput rowOutput rowDepth
    htargetBundle htargetRow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        newDepthCode & newDepthStep & hnewBundle & hprefix & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    newDepthCode, newDepthStep.
  split.
  - rewrite raw_add_succ by exact hPA. exact hnewBundle.
  - split.
    + apply (raw_formulaOperationTriple_prefix_extend M
        (raw_add M offset current)
        targetSourceCode targetSourceStep targetTargetCode targetTargetStep
        targetDepthCode targetDepthStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        newDepthCode newDepthStep initialRootIndex initialInput
        initialOutput initialDepth hprefix).
      * exact (raw_lt_le_trans_pair M hPA
          initialRootIndex offset (raw_add M offset current)
          hinitialBelow (raw_proof_left_le_sum M offset current)).
      * exact hinitialRoot.
    + intros index input output depth hindex hlookup.
      destruct (raw_lt_succ_cases M hPA index current hindex)
        as [hindexOld | ->].
      * apply (raw_formulaOperationTriple_prefix_extend M
          (raw_add M offset current)
          targetSourceCode targetSourceStep targetTargetCode targetTargetStep
          targetDepthCode targetDepthStep
          newSourceCode newSourceStep newTargetCode newTargetStep
          newDepthCode newDepthStep (raw_add M offset index)
          input output depth hprefix).
        -- exact (raw_lt_add_left_fixedTruth M hPA offset
             index current hindexOld).
        -- exact (hembed index input output depth hindexOld hlookup).
      * destruct hlookup as [hlookupInput [hlookupOutput hlookupDepth]].
        assert (hinputEq : input = rowInput).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            sourceSourceCode sourceSourceStep current input rowInput
            hlookupInput hrowInput).
        }
        assert (houtputEq : output = rowOutput).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            sourceTargetCode sourceTargetStep current output rowOutput
            hlookupOutput hrowOutput).
        }
        assert (hdepthEq : depth = rowDepth).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            sourceDepthCode sourceDepthStep current depth rowDepth
            hlookupDepth hrowDepth).
        }
        subst input. subst output. subst depth. exact hnewRoot.
Qed.

Theorem raw_formulaOperationCopyState_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atomFormula : term -> term -> term -> term -> formula)
      (atom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atomFormula parameter depth input output) <->
    atom (raw_term_eval M e' parameter)
      (raw_term_eval M e' depth) (raw_term_eval M e' input)
      (raw_term_eval M e' output)) ->
  forall parameter
      sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
      sourceDepthCode sourceDepthStep sourceBound sourceRootIndex
      sourceInput sourceOutput sourceRootDepth
      offset
      initialSourceCode initialSourceStep initialTargetCode initialTargetStep
      initialDepthCode initialDepthStep
      initialRootIndex initialInput initialOutput initialDepth,
  RawCodedFormulaOperationTrace M atom parameter sourceRootDepth
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep sourceBound sourceRootIndex
    sourceInput sourceOutput ->
  RawFormulaOperationTraversalBundle M atom parameter
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep
    initialDepthCode initialDepthStep offset ->
  rawLt M initialRootIndex offset ->
  RawCodedFormulaOperationTripleLookup M
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep
    initialDepthCode initialDepthStep
    initialRootIndex initialInput initialOutput initialDepth ->
  forall current,
  RawFormulaOperationCopyState M atom parameter
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep sourceBound offset
    initialRootIndex initialInput initialOutput initialDepth current.
Proof.
  intros M hPA atomFormula atom hatom parameter
    sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
    sourceDepthCode sourceDepthStep sourceBound sourceRootIndex
    sourceInput sourceOutput sourceRootDepth offset
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep
    initialDepthCode initialDepthStep
    initialRootIndex initialInput initialOutput initialDepth
    hsource hinitialBundle hinitialBelow hinitialRoot.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => parameter
    | 1 => sourceSourceCode
    | 2 => sourceSourceStep
    | 3 => sourceTargetCode
    | 4 => sourceTargetStep
    | 5 => sourceDepthCode
    | 6 => sourceDepthStep
    | 7 => sourceBound
    | 8 => offset
    | 9 => initialRootIndex
    | 10 => initialInput
    | 11 => initialOutput
    | _ => initialDepth
    end).
  set (phi := formulaOperationCopyStateTermAt atomFormula
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 6)
    (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11) (tVar 12)
    (tVar 13) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_formulaOperationCopyStateTermAt_iff M
        (scons M (raw_zero M) parameterEnv) atomFormula atom hatom
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 6)
        (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11) (tVar 12)
        (tVar 13) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exact (raw_formulaOperationCopyState_zero M hPA atom parameter
        sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
        sourceDepthCode sourceDepthStep sourceBound offset
        initialSourceCode initialSourceStep initialTargetCode initialTargetStep
        initialDepthCode initialDepthStep
        initialRootIndex initialInput initialOutput initialDepth
        hinitialBundle hinitialRoot).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1 (raw_sat_formulaOperationCopyStateTermAt_iff M
        (scons M current parameterEnv) atomFormula atom hatom
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 6)
        (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11) (tVar 12)
        (tVar 13) (tVar 0)) hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_formulaOperationCopyStateTermAt_iff M
        (scons M (raw_succ M current) parameterEnv) atomFormula atom hatom
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 6)
        (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11) (tVar 12)
        (tVar 13) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_formulaOperationCopyState_succ M hPA atom parameter
        sourceSourceCode sourceSourceStep sourceTargetCode sourceTargetStep
        sourceDepthCode sourceDepthStep sourceBound sourceRootIndex
        sourceInput sourceOutput sourceRootDepth
        offset initialRootIndex initialInput initialOutput initialDepth current
        hsource hinitialBelow hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1 (raw_sat_formulaOperationCopyStateTermAt_iff M
    (scons M current parameterEnv) atomFormula atom hatom
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 6)
    (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11) (tVar 12)
    (tVar 13) (tVar 0)) (hall current)) as hcurrent.
  unfold parameterEnv in hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

Theorem raw_formulaOperationTraces_concatenate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (atomFormula : term -> term -> term -> term -> formula)
      (atom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atomFormula parameter depth input output) <->
    atom (raw_term_eval M e' parameter)
      (raw_term_eval M e' depth) (raw_term_eval M e' input)
      (raw_term_eval M e' output)) ->
  forall parameter rootDepth
      firstSourceCode firstSourceStep firstTargetCode firstTargetStep
      firstDepthCode firstDepthStep firstBound firstRootIndex
      firstInput firstOutput
      secondSourceCode secondSourceStep secondTargetCode secondTargetStep
      secondDepthCode secondDepthStep secondBound secondRootIndex
      secondInput secondOutput,
  RawCodedFormulaOperationTrace M atom parameter rootDepth
    firstSourceCode firstSourceStep firstTargetCode firstTargetStep
    firstDepthCode firstDepthStep firstBound firstRootIndex
    firstInput firstOutput ->
  RawCodedFormulaOperationTrace M atom parameter rootDepth
    secondSourceCode secondSourceStep secondTargetCode secondTargetStep
    secondDepthCode secondDepthStep secondBound secondRootIndex
    secondInput secondOutput ->
  exists newSourceCode newSourceStep newTargetCode newTargetStep
      newDepthCode newDepthStep : M,
    RawCodedFormulaOperationTrace M atom parameter rootDepth
      newSourceCode newSourceStep newTargetCode newTargetStep
      newDepthCode newDepthStep (raw_add M firstBound secondBound)
      (raw_add M firstBound secondRootIndex) secondInput secondOutput /\
    RawCodedFormulaOperationTripleLookup M
      newSourceCode newSourceStep newTargetCode newTargetStep
      newDepthCode newDepthStep
      firstRootIndex firstInput firstOutput rootDepth.
Proof.
  intros M hPA atomFormula atom hatom parameter rootDepth
    firstSourceCode firstSourceStep firstTargetCode firstTargetStep
    firstDepthCode firstDepthStep firstBound firstRootIndex
    firstInput firstOutput
    secondSourceCode secondSourceStep secondTargetCode secondTargetStep
    secondDepthCode secondDepthStep secondBound secondRootIndex
    secondInput secondOutput hfirst hsecond.
  destruct hfirst as
    [hfirstSourceDefined
      [hfirstTargetDefined
        [hfirstDepthDefined
          [hfirstBelow [hfirstRoot hfirstRows]]]]].
  set (hfirstBundle := conj hfirstSourceDefined
    (conj hfirstTargetDefined (conj hfirstDepthDefined hfirstRows))).
  pose proof (raw_formulaOperationCopyState_all M hPA
    atomFormula atom hatom parameter
    secondSourceCode secondSourceStep secondTargetCode secondTargetStep
    secondDepthCode secondDepthStep secondBound secondRootIndex
    secondInput secondOutput rootDepth firstBound
    firstSourceCode firstSourceStep firstTargetCode firstTargetStep
    firstDepthCode firstDepthStep firstRootIndex firstInput firstOutput
    rootDepth hsecond hfirstBundle hfirstBelow hfirstRoot secondBound)
    as hguard.
  destruct (hguard (raw_rank_le_refl M hPA secondBound)) as
    (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
     newDepthCode & newDepthStep & hnewBundle & hfirstRetained & hembed).
  destruct hsecond as
    [hsecondSourceDefined
      [hsecondTargetDefined
        [hsecondDepthDefined
          [hsecondBelow [hsecondRoot hsecondRows]]]]].
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    newDepthCode, newDepthStep.
  split.
  - destruct hnewBundle as
      [hnewSourceDefined [hnewTargetDefined [hnewDepthDefined hnewRows]]].
    split; [exact hnewSourceDefined |].
    split; [exact hnewTargetDefined |].
    split; [exact hnewDepthDefined |].
    split.
    + exact (raw_lt_add_left_fixedTruth M hPA firstBound
        secondRootIndex secondBound hsecondBelow).
    + split.
      * exact (hembed secondRootIndex secondInput secondOutput rootDepth
          hsecondBelow hsecondRoot).
      * exact hnewRows.
  - exact hfirstRetained.
Qed.

(** ------------------------------------------------------------------
    Capture-avoiding shift constructors.

    After concatenation, the old left root remains at its original index and
    the right root is found at [leftBound + rightRootIndex].  Appending one
    final row therefore gives the desired binary parent certificate. *)

Lemma raw_codedFormulaShift_binary_composition : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      kind cutoff amount sourceLeft targetLeft sourceRight targetRight,
  RawCodedFormulaShift M cutoff amount sourceLeft targetLeft ->
  RawCodedFormulaShift M cutoff amount sourceRight targetRight ->
  RawCodedFormulaShift M cutoff amount
    (rawFormulaShiftBinaryCode M kind sourceLeft sourceRight)
    (rawFormulaShiftBinaryCode M kind targetLeft targetRight).
Proof.
  intros M hPA kind cutoff amount sourceLeft targetLeft
    sourceRight targetRight hleft hright.
  unfold RawCodedFormulaShift, RawCodedFormulaOperation in hleft, hright |- *.
  destruct hleft as
    (leftSourceCode & leftSourceStep & leftTargetCode & leftTargetStep &
     leftDepthCode & leftDepthStep & leftBound & leftRootIndex &
     hleftSourceDefined & hleftTargetDefined & hleftDepthDefined &
     hleftBelow & hleftRoot & hleftRows).
  destruct hright as
    (rightSourceCode & rightSourceStep & rightTargetCode & rightTargetStep &
     rightDepthCode & rightDepthStep & rightBound & rightRootIndex &
     hrightSourceDefined & hrightTargetDefined & hrightDepthDefined &
     hrightBelow & hrightRoot & hrightRows).
  set (hleftTrace := conj hleftSourceDefined
    (conj hleftTargetDefined
      (conj hleftDepthDefined
        (conj hleftBelow (conj hleftRoot hleftRows))))).
  set (hrightTrace := conj hrightSourceDefined
    (conj hrightTargetDefined
      (conj hrightDepthDefined
        (conj hrightBelow (conj hrightRoot hrightRows))))).
  destruct (raw_formulaOperationTraces_concatenate M hPA
    codedFormulaShiftAtomTermAt (RawCodedFormulaShiftAtom M)
    (raw_sat_codedFormulaShiftAtomTermAt_iff M) amount cutoff
    leftSourceCode leftSourceStep leftTargetCode leftTargetStep
    leftDepthCode leftDepthStep leftBound leftRootIndex
    sourceLeft targetLeft
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightDepthCode rightDepthStep rightBound rightRootIndex
    sourceRight targetRight hleftTrace hrightTrace)
    as (sourceCode & sourceStep & targetCode & targetStep &
        depthCode & depthStep & hcombined & hleftRetained).
  destruct hcombined as
    [hsourceDefined
      [htargetDefined
        [hdepthDefined
          [hrightCombinedBelow [hrightCombinedRoot hrows]]]]].
  set (combinedBound := raw_add M leftBound rightBound).
  assert (hleftCombinedBelow : rawLt M leftRootIndex combinedBound).
  {
    unfold combinedBound.
    exact (raw_lt_le_trans_pair M hPA leftRootIndex leftBound
      (raw_add M leftBound rightBound) hleftBelow
      (raw_proof_left_le_sum M leftBound rightBound)).
  }
  assert (hbinary : RawCodedFormulaBinaryOperationRow M
      (rawFormulaShiftBinaryCode M kind)
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      combinedBound
      (rawFormulaShiftBinaryCode M kind sourceLeft sourceRight)
      (rawFormulaShiftBinaryCode M kind targetLeft targetRight) cutoff).
  {
    exists leftRootIndex, sourceLeft, targetLeft, cutoff,
      (raw_add M leftBound rightRootIndex),
      sourceRight, targetRight, cutoff.
    split; [exact hleftCombinedBelow |].
    split; [exact hleftRetained |].
    split; [reflexivity |].
    split; [exact hrightCombinedBelow |].
    split; [exact hrightCombinedRoot |].
    repeat split; reflexivity.
  }
  assert (hrow : RawCodedFormulaOperationTraversalRow M
      (RawCodedFormulaShiftAtom M) amount
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      combinedBound
      (rawFormulaShiftBinaryCode M kind sourceLeft sourceRight)
      (rawFormulaShiftBinaryCode M kind targetLeft targetRight) cutoff).
  {
    destruct kind; cbn [rawFormulaShiftBinaryCode] in hbinary |- *.
    - right. right. left. exact hbinary.
    - right. right. right. left. exact hbinary.
    - right. right. right. right. left. exact hbinary.
  }
  set (hbundle := conj hsourceDefined
    (conj htargetDefined (conj hdepthDefined hrows))).
  destruct (raw_formulaOperationTraversalBundle_append M hPA
    (RawCodedFormulaShiftAtom M) amount
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    combinedBound
    (rawFormulaShiftBinaryCode M kind sourceLeft sourceRight)
    (rawFormulaShiftBinaryCode M kind targetLeft targetRight)
    cutoff hbundle hrow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        newDepthCode & newDepthStep & hnewBundle & hprefix & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    newDepthCode, newDepthStep, (raw_succ M combinedBound), combinedBound.
  destruct hnewBundle as
    [hnewSourceDefined [hnewTargetDefined [hnewDepthDefined hnewRows]]].
  split; [exact hnewSourceDefined |].
  split; [exact hnewTargetDefined |].
  split; [exact hnewDepthDefined |].
  split.
  - exact (raw_assignment_lt_self_succ M hPA combinedBound).
  - split; [exact hnewRoot | exact hnewRows].
Qed.

Lemma raw_codedFormulaShift_unary_composition : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      kind cutoff amount sourceChild targetChild,
  RawCodedFormulaShift M (raw_succ M cutoff) amount
    sourceChild targetChild ->
  RawCodedFormulaShift M cutoff amount
    (rawFormulaShiftUnaryCode M kind sourceChild)
    (rawFormulaShiftUnaryCode M kind targetChild).
Proof.
  intros M hPA kind cutoff amount sourceChild targetChild hchild.
  unfold RawCodedFormulaShift, RawCodedFormulaOperation in hchild |- *.
  destruct hchild as
    (sourceCode & sourceStep & targetCode & targetStep &
     depthCode & depthStep & bound & rootIndex &
     hsourceDefined & htargetDefined & hdepthDefined &
     hrootBelow & hroot & hrows).
  assert (hunary : RawCodedFormulaUnaryOperationRow M
      (rawFormulaShiftUnaryCode M kind)
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound
      (rawFormulaShiftUnaryCode M kind sourceChild)
      (rawFormulaShiftUnaryCode M kind targetChild) cutoff).
  {
    exists rootIndex, sourceChild, targetChild, (raw_succ M cutoff).
    split; [exact hrootBelow |]. split; [exact hroot |].
    repeat split; reflexivity.
  }
  assert (hrow : RawCodedFormulaOperationTraversalRow M
      (RawCodedFormulaShiftAtom M) amount
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound
      (rawFormulaShiftUnaryCode M kind sourceChild)
      (rawFormulaShiftUnaryCode M kind targetChild) cutoff).
  {
    destruct kind; cbn [rawFormulaShiftUnaryCode] in hunary |- *.
    - right. right. right. right. right. left. exact hunary.
    - right. right. right. right. right. right. exact hunary.
  }
  set (hbundle := conj hsourceDefined
    (conj htargetDefined (conj hdepthDefined hrows))).
  destruct (raw_formulaOperationTraversalBundle_append M hPA
    (RawCodedFormulaShiftAtom M) amount
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound (rawFormulaShiftUnaryCode M kind sourceChild)
    (rawFormulaShiftUnaryCode M kind targetChild) cutoff hbundle hrow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        newDepthCode & newDepthStep & hnewBundle & hprefix & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    newDepthCode, newDepthStep, (raw_succ M bound), bound.
  destruct hnewBundle as
    [hnewSourceDefined [hnewTargetDefined [hnewDepthDefined hnewRows]]].
  split; [exact hnewSourceDefined |].
  split; [exact hnewTargetDefined |].
  split; [exact hnewDepthDefined |].
  split.
  - exact (raw_assignment_lt_self_succ M hPA bound).
  - split; [exact hnewRoot | exact hnewRows].
Qed.

Theorem raw_codedFormulaShift_compositional : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaShiftCompositional M.
Proof.
  intros M hPA. split.
  - intros. eapply raw_codedFormulaShift_binary_composition; eassumption.
  - intros. eapply raw_codedFormulaShift_unary_composition; eassumption.
Qed.

End PABoundedRawCodedFormulaOperationTraceConcatenation.
