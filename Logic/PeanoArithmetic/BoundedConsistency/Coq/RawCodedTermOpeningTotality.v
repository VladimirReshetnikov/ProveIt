(**
  Totality of represented term opening on nonstandard syntax codes.

  A [RawTermSyntaxRealizable] certificate may describe a genuinely
  nonstandard term code, so this proof cannot decode the input into a Rocq
  term.  Instead it performs two PA-definable inductions.  The first copies
  an arbitrary already represented opening trace after an offset, allowing
  independently constructed child traces to be concatenated.  The second is
  strong induction over the represented syntax support and builds the
  opening trace constructor by constructor.

  The lifted replacement is an arbitrary carrier value.  This is deliberate:
  opening only inspects the source syntax and may insert that value at a
  variable leaf.  No standard quotation or target-syntax premise is used.
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity
  RawCodedSyntaxConstructors RawCodedAssignment RawCodedAssignmentTotality
  RawCodedProofDescent RawCodedFormulaRankStep RawCodedFormulaRankTraversal
  RawCodedFormulaRankTotality RawCodedFormulaOperations
  RawCodedTermEvaluationTraversal RawCodedTermEvaluationRealization
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthReindexing
  RawCodedPAAxiomContextSelfShift
  RawCodedTermOperationTreeRealization RawCodedFormulaShiftTotality.

Module PABoundedRawCodedTermOpeningTotality.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthReindexing.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedTermOperationTreeRealization.
Import PABoundedRawCodedFormulaShiftTotality.

(** Prefix transport is structural: only recursive child lookups mention the
    beta tables.  The opening-specific variable row is table-independent. *)
Lemma raw_termOpeningTraversalRow_prefix_extend : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff liftedReplacement bound current
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    newSourceCode newSourceStep newTargetCode newTargetStep input output,
  RawTermShiftTablePrefixExtension M bound
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    newSourceCode newSourceStep newTargetCode newTargetStep ->
  rawLe M current bound ->
  RawCodedTermOpeningTraversalRow M cutoff liftedReplacement
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    current input output ->
  RawCodedTermOpeningTraversalRow M cutoff liftedReplacement
    newSourceCode newSourceStep newTargetCode newTargetStep
    current input output.
Proof.
  intros M hPA cutoff liftedReplacement bound current
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    newSourceCode newSourceStep newTargetCode newTargetStep
    input output hext hcurrent hrow.
  destruct hrow as
    [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - left. exact hvar.
  - right. left. exact hzero.
  - right. right. left.
    destruct hsucc as
      (childIndex & inputChild & outputChild & hchild & hlookup &
       hinput & houtput).
    exists childIndex, inputChild, outputChild.
    split; [exact hchild |]. split.
    + apply (raw_termShiftPairLookup_prefix_extend M bound
        oldSourceCode oldSourceStep oldTargetCode oldTargetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        childIndex inputChild outputChild hext).
      * exact (raw_lt_le_trans_pair M hPA
          childIndex current bound hchild hcurrent).
      * exact hlookup.
    + split; assumption.
  - right. right. right. left.
    destruct hadd as
      (leftIndex & inputLeft & outputLeft &
       rightIndex & inputRight & outputRight &
       hleft & hleftLookup & hright & hrightLookup & hinput & houtput).
    exists leftIndex, inputLeft, outputLeft,
      rightIndex, inputRight, outputRight.
    split; [exact hleft |]. split.
    + apply (raw_termShiftPairLookup_prefix_extend M bound
        oldSourceCode oldSourceStep oldTargetCode oldTargetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        leftIndex inputLeft outputLeft hext).
      * exact (raw_lt_le_trans_pair M hPA
          leftIndex current bound hleft hcurrent).
      * exact hleftLookup.
    + split; [exact hright |]. split.
      * apply (raw_termShiftPairLookup_prefix_extend M bound
          oldSourceCode oldSourceStep oldTargetCode oldTargetStep
          newSourceCode newSourceStep newTargetCode newTargetStep
          rightIndex inputRight outputRight hext).
        -- exact (raw_lt_le_trans_pair M hPA
             rightIndex current bound hright hcurrent).
        -- exact hrightLookup.
      * split; assumption.
  - right. right. right. right.
    destruct hmul as
      (leftIndex & inputLeft & outputLeft &
       rightIndex & inputRight & outputRight &
       hleft & hleftLookup & hright & hrightLookup & hinput & houtput).
    exists leftIndex, inputLeft, outputLeft,
      rightIndex, inputRight, outputRight.
    split; [exact hleft |]. split.
    + apply (raw_termShiftPairLookup_prefix_extend M bound
        oldSourceCode oldSourceStep oldTargetCode oldTargetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        leftIndex inputLeft outputLeft hext).
      * exact (raw_lt_le_trans_pair M hPA
          leftIndex current bound hleft hcurrent).
      * exact hleftLookup.
    + split; [exact hright |]. split.
      * apply (raw_termShiftPairLookup_prefix_extend M bound
          oldSourceCode oldSourceStep oldTargetCode oldTargetStep
          newSourceCode newSourceStep newTargetCode newTargetStep
          rightIndex inputRight outputRight hext).
        -- exact (raw_lt_le_trans_pair M hPA
             rightIndex current bound hright hcurrent).
        -- exact hrightLookup.
      * split; assumption.
Qed.

Definition RawTermOpeningTraversalBundle (M : RawPAModel)
    (cutoff liftedReplacement sourceCode sourceStep
      targetCode targetStep bound : M) : Prop :=
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep bound /\
  RawCodedAssignmentDefinedThrough M targetCode targetStep bound /\
  RawCodedTermOpeningRows M cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep bound.

Arguments RawTermOpeningTraversalBundle M cutoff liftedReplacement
  sourceCode sourceStep targetCode targetStep bound : clear implicits.

Definition termOpeningTraversalBundleTermAt
    (cutoff liftedReplacement sourceCode sourceStep
      targetCode targetStep bound : term) : formula :=
  operationAnd3
    (codedAssignmentDefinedThroughTermAt sourceCode sourceStep bound)
    (codedAssignmentDefinedThroughTermAt targetCode targetStep bound)
    (codedTermOpeningRowsTermAt cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep bound).

Lemma raw_sat_termOpeningTraversalBundleTermAt_iff : forall
    (M : RawPAModel) e cutoff liftedReplacement sourceCode sourceStep
      targetCode targetStep bound,
  raw_formula_sat M e
    (termOpeningTraversalBundleTermAt cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep bound) <->
  RawTermOpeningTraversalBundle M
    (raw_term_eval M e cutoff) (raw_term_eval M e liftedReplacement)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e bound).
Proof.
  intros. unfold termOpeningTraversalBundleTermAt,
    RawTermOpeningTraversalBundle, operationAnd3.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff,
    raw_sat_codedTermOpeningRowsTermAt_iff.
  reflexivity.
Qed.

Theorem raw_termOpeningTraversalBundle_append : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
      bound input output,
  RawTermOpeningTraversalBundle M cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep bound ->
  RawCodedTermOpeningTraversalRow M cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep bound input output ->
  exists newSourceCode newSourceStep newTargetCode newTargetStep : M,
    RawTermOpeningTraversalBundle M cutoff liftedReplacement
      newSourceCode newSourceStep newTargetCode newTargetStep
      (raw_succ M bound) /\
    RawTermShiftTablePrefixExtension M bound
      sourceCode sourceStep targetCode targetStep
      newSourceCode newSourceStep newTargetCode newTargetStep /\
    RawCodedTermOperationPairLookup M
      newSourceCode newSourceStep newTargetCode newTargetStep
      bound input output.
Proof.
  intros M hPA cutoff liftedReplacement sourceCode sourceStep
    targetCode targetStep bound input output
    [hsourceDefined [htargetDefined hrows]] hclosed.
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    sourceCode sourceStep bound input hsourceDefined)
    as [newSourceCode [newSourceStep
      [hnewSourceDefined [hsourcePrefix hsourceRoot]]]].
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    targetCode targetStep bound output htargetDefined)
    as [newTargetCode [newTargetStep
      [hnewTargetDefined [htargetPrefix htargetRoot]]]].
  set (hext := conj hsourcePrefix htargetPrefix).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep.
  split.
  - split; [exact hnewSourceDefined |].
    split; [exact hnewTargetDefined |].
    intros index rowInput rowOutput hindex hlookup.
    destruct (raw_lt_succ_cases M hPA index bound hindex)
      as [hindexOld | ->].
    + destruct (hsourceDefined index hindexOld)
        as [oldInput holdInput].
      destruct (htargetDefined index hindexOld)
        as [oldOutput holdOutput].
      assert (hnewOld : RawCodedTermOperationPairLookup M
          newSourceCode newSourceStep newTargetCode newTargetStep
          index oldInput oldOutput).
      {
        apply (raw_termShiftPairLookup_prefix_extend M bound
          sourceCode sourceStep targetCode targetStep
          newSourceCode newSourceStep newTargetCode newTargetStep
          index oldInput oldOutput hext hindexOld).
        split; assumption.
      }
      destruct hlookup as [hlookupInput hlookupOutput].
      destruct hnewOld as [hnewOldInput hnewOldOutput].
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
      subst rowInput. subst rowOutput.
      apply (raw_termOpeningTraversalRow_prefix_extend M hPA
        cutoff liftedReplacement bound index
        sourceCode sourceStep targetCode targetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        oldInput oldOutput hext).
      * exact (raw_lt_to_le M index bound hindexOld).
      * apply (hrows index oldInput oldOutput hindexOld).
        split; assumption.
    + destruct hlookup as [hlookupInput hlookupOutput].
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
      subst rowInput. subst rowOutput.
      apply (raw_termOpeningTraversalRow_prefix_extend M hPA
        cutoff liftedReplacement bound bound
        sourceCode sourceStep targetCode targetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        input output hext).
      * apply raw_rank_le_refl. exact hPA.
      * exact hclosed.
  - split; [exact hext |]. split; assumption.
Qed.

(** Offset embeddings are independent of the operation's variable clause,
    so the existing pair-table relation can be reused verbatim. *)
Lemma raw_termOpeningTraversalRow_offset : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    cutoff liftedReplacement offset current
    sourceCode sourceStep targetCode targetStep
    copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
    input output,
  RawTermShiftPairOffsetEmbedding M offset current
    sourceCode sourceStep targetCode targetStep
    copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep ->
  RawCodedTermOpeningTraversalRow M cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep current input output ->
  RawCodedTermOpeningTraversalRow M cutoff liftedReplacement
    copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
    (raw_add M offset current) input output.
Proof.
  intros M hPA cutoff liftedReplacement offset current
    sourceCode sourceStep targetCode targetStep
    copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
    input output hembed hrow.
  destruct hrow as
    [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - left. exact hvar.
  - right. left. exact hzero.
  - right. right. left.
    destruct hsucc as
      (childIndex & inputChild & outputChild & hchild & hlookup &
       hinput & houtput).
    exists (raw_add M offset childIndex), inputChild, outputChild.
    split.
    + exact (raw_lt_add_left_fixedTruth M hPA offset
        childIndex current hchild).
    + split.
      * exact (hembed childIndex inputChild outputChild hchild hlookup).
      * split; assumption.
  - right. right. right. left.
    destruct hadd as
      (leftIndex & inputLeft & outputLeft &
       rightIndex & inputRight & outputRight &
       hleft & hleftLookup & hright & hrightLookup & hinput & houtput).
    exists (raw_add M offset leftIndex), inputLeft, outputLeft,
      (raw_add M offset rightIndex), inputRight, outputRight.
    split.
    + exact (raw_lt_add_left_fixedTruth M hPA offset
        leftIndex current hleft).
    + split.
      * exact (hembed leftIndex inputLeft outputLeft hleft hleftLookup).
      * split.
        -- exact (raw_lt_add_left_fixedTruth M hPA offset
             rightIndex current hright).
        -- split.
           ++ exact (hembed rightIndex inputRight outputRight
                hright hrightLookup).
           ++ split; assumption.
  - right. right. right. right.
    destruct hmul as
      (leftIndex & inputLeft & outputLeft &
       rightIndex & inputRight & outputRight &
       hleft & hleftLookup & hright & hrightLookup & hinput & houtput).
    exists (raw_add M offset leftIndex), inputLeft, outputLeft,
      (raw_add M offset rightIndex), inputRight, outputRight.
    split.
    + exact (raw_lt_add_left_fixedTruth M hPA offset
        leftIndex current hleft).
    + split.
      * exact (hembed leftIndex inputLeft outputLeft hleft hleftLookup).
      * split.
        -- exact (raw_lt_add_left_fixedTruth M hPA offset
             rightIndex current hright).
        -- split.
           ++ exact (hembed rightIndex inputRight outputRight
                hright hrightLookup).
           ++ split; assumption.
Qed.

(** The copy state is guarded by [current <= sourceBound].  Consequently its
    successor proof may inspect the source row at [current], while definable
    induction remains total beyond the source bound. *)
Definition RawTermOpeningTraversalCopyState (M : RawPAModel)
    (cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep sourceBound offset
      initialRootIndex initialInput initialOutput current : M) : Prop :=
  rawLe M current sourceBound ->
  exists copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep,
    RawTermOpeningTraversalBundle M cutoff liftedReplacement
      copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
      (raw_add M offset current) /\
    RawCodedTermOperationPairLookup M
      copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
      initialRootIndex initialInput initialOutput /\
    RawTermShiftPairOffsetEmbedding M offset current
      sourceCode sourceStep targetCode targetStep
      copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep.

Arguments RawTermOpeningTraversalCopyState M cutoff liftedReplacement
  sourceCode sourceStep targetCode targetStep sourceBound offset
  initialRootIndex initialInput initialOutput current : clear implicits.

Definition termOpeningTraversalCopyStateTermAt
    (cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep sourceBound offset
      initialRootIndex initialInput initialOutput current : term) : formula :=
  pImp
    (Formula.leTermAt current sourceBound)
    (operationEx4
      (operationAnd3
        (termOpeningTraversalBundleTermAt
          (liftTerm 4 cutoff) (liftTerm 4 liftedReplacement)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)
          (tAdd (liftTerm 4 offset) (liftTerm 4 current)))
        (codedTermOperationPairLookupTermAt
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)
          (liftTerm 4 initialRootIndex)
          (liftTerm 4 initialInput) (liftTerm 4 initialOutput))
        (termShiftPairOffsetEmbeddingTermAt
          (liftTerm 4 offset) (liftTerm 4 current)
          (liftTerm 4 sourceCode) (liftTerm 4 sourceStep)
          (liftTerm 4 targetCode) (liftTerm 4 targetStep)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)))).

Lemma raw_sat_termOpeningTraversalCopyStateTermAt_iff : forall
    (M : RawPAModel) e cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep sourceBound offset
      initialRootIndex initialInput initialOutput current,
  raw_formula_sat M e
    (termOpeningTraversalCopyStateTermAt cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep sourceBound offset
      initialRootIndex initialInput initialOutput current) <->
  RawTermOpeningTraversalCopyState M
    (raw_term_eval M e cutoff) (raw_term_eval M e liftedReplacement)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e sourceBound) (raw_term_eval M e offset)
    (raw_term_eval M e initialRootIndex)
    (raw_term_eval M e initialInput) (raw_term_eval M e initialOutput)
    (raw_term_eval M e current).
Proof.
  intros. unfold termOpeningTraversalCopyStateTermAt, operationEx4,
    operationAnd3, RawTermOpeningTraversalCopyState.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank.
  setoid_rewrite raw_sat_termOpeningTraversalBundleTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite raw_sat_termShiftPairOffsetEmbeddingTermAt_iff.
  cbn [raw_term_eval scons].
  split; intros h hle;
    destruct (h hle) as
      (copiedSourceCode & copiedSourceStep & copiedTargetCode &
       copiedTargetStep & hresult);
    exists copiedSourceCode, copiedSourceStep,
      copiedTargetCode, copiedTargetStep.
  - repeat rewrite (raw_rankTraversal_eval_liftTerm_four M
      copiedTargetStep copiedTargetCode copiedSourceStep copiedSourceCode e)
      in hresult.
    exact hresult.
  - repeat rewrite (raw_rankTraversal_eval_liftTerm_four M
      copiedTargetStep copiedTargetCode copiedSourceStep copiedSourceCode e).
    exact hresult.
Qed.

Lemma raw_termOpeningTraversalCopyState_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep sourceBound offset
      initialSourceCode initialSourceStep initialTargetCode initialTargetStep
      initialRootIndex initialInput initialOutput,
  RawTermOpeningTraversalBundle M cutoff liftedReplacement
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep
    offset ->
  RawCodedTermOperationPairLookup M
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep
    initialRootIndex initialInput initialOutput ->
  RawTermOpeningTraversalCopyState M cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep sourceBound offset
    initialRootIndex initialInput initialOutput (raw_zero M).
Proof.
  intros M hPA cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep sourceBound offset
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep
    initialRootIndex initialInput initialOutput
    hinitialBundle hinitialRoot _.
  exists initialSourceCode, initialSourceStep,
    initialTargetCode, initialTargetStep.
  rewrite raw_assignmentTotality_add_zero_right by exact hPA.
  split; [exact hinitialBundle |]. split; [exact hinitialRoot |].
  exact (raw_termShiftPairOffsetEmbedding_zero M hPA offset
    sourceCode sourceStep targetCode targetStep
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep).
Qed.

Lemma raw_termOpeningTraversalCopyState_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep
      sourceBound sourceRootIndex sourceInput sourceOutput
      offset initialRootIndex initialInput initialOutput current,
  RawCodedTermOpeningTrace M cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep
    sourceBound sourceRootIndex sourceInput sourceOutput ->
  rawLt M initialRootIndex offset ->
  RawTermOpeningTraversalCopyState M cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep sourceBound offset
    initialRootIndex initialInput initialOutput current ->
  RawTermOpeningTraversalCopyState M cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep sourceBound offset
    initialRootIndex initialInput initialOutput (raw_succ M current).
Proof.
  intros M hPA cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep
    sourceBound sourceRootIndex sourceInput sourceOutput
    offset initialRootIndex initialInput initialOutput current
    hsource hinitialBelow hcurrent hsuccLe.
  destruct hsource as
    [hsourceDefined [htargetDefined [_ [_ hsourceRows]]]].
  assert (hcurrentBelow : rawLt M current sourceBound).
  { exact (raw_rank_lt_of_succ_le M hPA current sourceBound hsuccLe). }
  assert (hcurrentLe : rawLe M current sourceBound).
  { exact (raw_lt_to_le M current sourceBound hcurrentBelow). }
  destruct (hcurrent hcurrentLe) as
    (copiedSourceCode & copiedSourceStep & copiedTargetCode &
     copiedTargetStep & hcopiedBundle & hinitialRoot & hembed).
  destruct (hsourceDefined current hcurrentBelow)
    as [rowInput hrowInput].
  destruct (htargetDefined current hcurrentBelow)
    as [rowOutput hrowOutput].
  assert (hsourcePair : RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep
      current rowInput rowOutput).
  { split; assumption. }
  pose proof (hsourceRows current rowInput rowOutput
    hcurrentBelow hsourcePair) as hsourceRow.
  pose proof (raw_termOpeningTraversalRow_offset M hPA
    cutoff liftedReplacement offset current
    sourceCode sourceStep targetCode targetStep
    copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
    rowInput rowOutput hembed hsourceRow) as hcopiedRow.
  destruct (raw_termOpeningTraversalBundle_append M hPA
    cutoff liftedReplacement copiedSourceCode copiedSourceStep
    copiedTargetCode copiedTargetStep (raw_add M offset current)
    rowInput rowOutput hcopiedBundle hcopiedRow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        hnewBundle & hprefix & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep.
  split.
  - rewrite raw_add_succ by exact hPA. exact hnewBundle.
  - split.
    + apply (raw_termShiftPairLookup_prefix_extend M
        (raw_add M offset current)
        copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        initialRootIndex initialInput initialOutput hprefix).
      * exact (raw_lt_le_trans_pair M hPA
          initialRootIndex offset (raw_add M offset current)
          hinitialBelow (raw_proof_left_le_sum M offset current)).
      * exact hinitialRoot.
    + intros index input output hindex hlookup.
      destruct (raw_lt_succ_cases M hPA index current hindex)
        as [hindexOld | ->].
      * apply (raw_termShiftPairLookup_prefix_extend M
          (raw_add M offset current)
          copiedSourceCode copiedSourceStep copiedTargetCode copiedTargetStep
          newSourceCode newSourceStep newTargetCode newTargetStep
          (raw_add M offset index) input output hprefix).
        -- exact (raw_lt_add_left_fixedTruth M hPA offset
             index current hindexOld).
        -- exact (hembed index input output hindexOld hlookup).
      * destruct hlookup as [hlookupInput hlookupOutput].
        assert (hinputEq : input = rowInput).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            sourceCode sourceStep current input rowInput
            hlookupInput hrowInput).
        }
        assert (houtputEq : output = rowOutput).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            targetCode targetStep current output rowOutput
            hlookupOutput hrowOutput).
        }
        subst input. subst output. exact hnewRoot.
Qed.

Theorem raw_termOpeningTraversalCopyState_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep
      sourceBound sourceRootIndex sourceInput sourceOutput
      offset initialSourceCode initialSourceStep
      initialTargetCode initialTargetStep
      initialRootIndex initialInput initialOutput,
  RawCodedTermOpeningTrace M cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep
    sourceBound sourceRootIndex sourceInput sourceOutput ->
  RawTermOpeningTraversalBundle M cutoff liftedReplacement
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep
    offset ->
  rawLt M initialRootIndex offset ->
  RawCodedTermOperationPairLookup M
    initialSourceCode initialSourceStep initialTargetCode initialTargetStep
    initialRootIndex initialInput initialOutput ->
  forall current,
  RawTermOpeningTraversalCopyState M cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep sourceBound offset
    initialRootIndex initialInput initialOutput current.
Proof.
  intros M hPA cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep
    sourceBound sourceRootIndex sourceInput sourceOutput
    offset initialSourceCode initialSourceStep
    initialTargetCode initialTargetStep
    initialRootIndex initialInput initialOutput
    hsource hinitialBundle hinitialBelow hinitialRoot.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => cutoff
    | 1 => liftedReplacement
    | 2 => sourceCode
    | 3 => sourceStep
    | 4 => targetCode
    | 5 => targetStep
    | 6 => sourceBound
    | 7 => offset
    | 8 => initialRootIndex
    | 9 => initialInput
    | _ => initialOutput
    end).
  set (phi := termOpeningTraversalCopyStateTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 6)
    (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_termOpeningTraversalCopyStateTermAt_iff M
        (scons M (raw_zero M) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 6)
        (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exact (raw_termOpeningTraversalCopyState_zero M hPA
        cutoff liftedReplacement
        sourceCode sourceStep targetCode targetStep sourceBound
        offset initialSourceCode initialSourceStep
        initialTargetCode initialTargetStep
        initialRootIndex initialInput initialOutput
        hinitialBundle hinitialRoot).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_termOpeningTraversalCopyStateTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 6)
          (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_termOpeningTraversalCopyStateTermAt_iff M
        (scons M (raw_succ M current) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 6)
        (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_termOpeningTraversalCopyState_succ M hPA
        cutoff liftedReplacement
        sourceCode sourceStep targetCode targetStep
        sourceBound sourceRootIndex sourceInput sourceOutput
        offset initialRootIndex initialInput initialOutput current
        hsource hinitialBelow hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_termOpeningTraversalCopyStateTermAt_iff M
      (scons M current parameterEnv)
      (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 6)
      (tVar 7) (tVar 8) (tVar 9) (tVar 10) (tVar 11) (tVar 0))
    (hall current)) as hcurrent.
  unfold parameterEnv in hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

(** Concatenation retains the first child root and offsets every row of the
    second child.  Both child bounds may be nonstandard. *)
Theorem raw_termOpeningTraces_concatenate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement
      firstSourceCode firstSourceStep firstTargetCode firstTargetStep
      firstBound firstRootIndex firstInput firstOutput
      secondSourceCode secondSourceStep secondTargetCode secondTargetStep
      secondBound secondRootIndex secondInput secondOutput,
  RawCodedTermOpeningTrace M cutoff liftedReplacement
    firstSourceCode firstSourceStep firstTargetCode firstTargetStep
    firstBound firstRootIndex firstInput firstOutput ->
  RawCodedTermOpeningTrace M cutoff liftedReplacement
    secondSourceCode secondSourceStep secondTargetCode secondTargetStep
    secondBound secondRootIndex secondInput secondOutput ->
  exists newSourceCode newSourceStep newTargetCode newTargetStep : M,
    RawCodedTermOpeningTrace M cutoff liftedReplacement
      newSourceCode newSourceStep newTargetCode newTargetStep
      (raw_add M firstBound secondBound)
      (raw_add M firstBound secondRootIndex) secondInput secondOutput /\
    RawCodedTermOperationPairLookup M
      newSourceCode newSourceStep newTargetCode newTargetStep
      firstRootIndex firstInput firstOutput.
Proof.
  intros M hPA cutoff liftedReplacement
    firstSourceCode firstSourceStep firstTargetCode firstTargetStep
    firstBound firstRootIndex firstInput firstOutput
    secondSourceCode secondSourceStep secondTargetCode secondTargetStep
    secondBound secondRootIndex secondInput secondOutput
    hfirst hsecond.
  destruct hfirst as
    [hfirstSource [hfirstTarget [hfirstBelow [hfirstRoot hfirstRows]]]].
  assert (hfirstBundle : RawTermOpeningTraversalBundle M
      cutoff liftedReplacement
      firstSourceCode firstSourceStep firstTargetCode firstTargetStep
      firstBound).
  { repeat split; assumption. }
  pose proof (raw_termOpeningTraversalCopyState_all M hPA
    cutoff liftedReplacement
    secondSourceCode secondSourceStep secondTargetCode secondTargetStep
    secondBound secondRootIndex secondInput secondOutput
    firstBound firstSourceCode firstSourceStep firstTargetCode firstTargetStep
    firstRootIndex firstInput firstOutput
    hsecond hfirstBundle hfirstBelow hfirstRoot secondBound) as hguard.
  destruct (hguard (raw_rank_le_refl M hPA secondBound)) as
    (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
     hnewBundle & hfirstRetained & hembed).
  destruct hsecond as
    [hsecondSource [hsecondTarget [hsecondBelow [hsecondRoot hsecondRows]]]].
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep.
  split.
  - destruct hnewBundle as [hnewSource [hnewTarget hnewRows]].
    exact (conj hnewSource
      (conj hnewTarget
        (conj
          (raw_lt_add_left_fixedTruth M hPA firstBound
            secondRootIndex secondBound hsecondBelow)
          (conj
            (hembed secondRootIndex secondInput secondOutput
              hsecondBelow hsecondRoot)
            hnewRows)))).
  - exact hfirstRetained.
Qed.

(** ------------------------------------------------------------------
    Structural opening constructors. *)

Lemma raw_codedTermOpening_variable_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement index,
  exists output,
    RawCodedTermOpening M cutoff liftedReplacement
      (rawTermVarCode M index) output.
Proof.
  intros M hPA cutoff liftedReplacement index.
  destruct (raw_order_trichotomy M hPA index cutoff)
    as [-> | [hlow | hhigh]].
  - exists liftedReplacement.
    apply (raw_codedTermOpening_of_valid_tree M hPA cutoff
      liftedReplacement (RTOTVar M cutoff liftedReplacement)).
    cbn [RawTermOperationTreeValid].
    exists cutoff. split; [reflexivity |].
    right. left. split; reflexivity.
  - exists (rawTermVarCode M index).
    apply (raw_codedTermOpening_of_valid_tree M hPA cutoff
      liftedReplacement
      (RTOTVar M index (rawTermVarCode M index))).
    cbn [RawTermOperationTreeValid].
    exists index. split; [reflexivity |].
    left. split; [exact hlow | reflexivity].
  - destruct (raw_assignment_zero_or_successor M hPA index)
      as [hzero | [predecessor hsuccessor]].
    + subst index. exfalso.
      exact (raw_not_lt_zero M hPA cutoff hhigh).
    + subst index. exists (rawTermVarCode M predecessor).
      apply (raw_codedTermOpening_of_valid_tree M hPA cutoff
        liftedReplacement
        (RTOTVar M (raw_succ M predecessor)
          (rawTermVarCode M predecessor))).
      cbn [RawTermOperationTreeValid].
      exists (raw_succ M predecessor). split; [reflexivity |].
      right. right. exists predecessor.
      repeat split; try reflexivity. exact hhigh.
Qed.

Lemma raw_codedTermOpening_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement,
  RawCodedTermOpening M cutoff liftedReplacement
    (rawTermZeroCode M) (rawTermZeroCode M).
Proof.
  intros M hPA cutoff liftedReplacement.
  apply (raw_codedTermOpening_of_valid_tree M hPA cutoff
    liftedReplacement (RTOTZero M)).
  exact I.
Qed.

Lemma raw_codedTermOpening_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement inputChild outputChild,
  RawCodedTermOpening M cutoff liftedReplacement inputChild outputChild ->
  RawCodedTermOpening M cutoff liftedReplacement
    (rawTermSuccCode M inputChild) (rawTermSuccCode M outputChild).
Proof.
  intros M hPA cutoff liftedReplacement inputChild outputChild
    (sourceCode & sourceStep & targetCode & targetStep & bound &
     rootIndex & htrace).
  destruct htrace as
    [hsource [htarget [hrootBelow [hroot hrows]]]].
  assert (hbundle : RawTermOpeningTraversalBundle M cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep bound).
  { repeat split; assumption. }
  assert (hrow : RawCodedTermOpeningTraversalRow M cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep bound
      (rawTermSuccCode M inputChild) (rawTermSuccCode M outputChild)).
  {
    right. right. left.
    exists rootIndex, inputChild, outputChild.
    split; [exact hrootBelow |]. split; [exact hroot |].
    split; reflexivity.
  }
  destruct (raw_termOpeningTraversalBundle_append M hPA
    cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
    bound (rawTermSuccCode M inputChild) (rawTermSuccCode M outputChild)
    hbundle hrow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        hnewBundle & _ & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    (raw_succ M bound), bound.
  destruct hnewBundle as [hnewSource [hnewTarget hnewRows]].
  exact (conj hnewSource
    (conj hnewTarget
      (conj (raw_assignment_lt_self_succ M hPA bound)
        (conj hnewRoot hnewRows)))).
Qed.

Lemma raw_codedTermOpening_add : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement
      inputLeft outputLeft inputRight outputRight,
  RawCodedTermOpening M cutoff liftedReplacement inputLeft outputLeft ->
  RawCodedTermOpening M cutoff liftedReplacement inputRight outputRight ->
  RawCodedTermOpening M cutoff liftedReplacement
    (rawTermAddCode M inputLeft inputRight)
    (rawTermAddCode M outputLeft outputRight).
Proof.
  intros M hPA cutoff liftedReplacement
    inputLeft outputLeft inputRight outputRight
    (leftSourceCode & leftSourceStep & leftTargetCode & leftTargetStep &
     leftBound & leftRootIndex & hleft)
    (rightSourceCode & rightSourceStep & rightTargetCode & rightTargetStep &
     rightBound & rightRootIndex & hright).
  assert (hleftBelow : rawLt M leftRootIndex leftBound).
  { exact (proj1 (proj2 (proj2 hleft))). }
  destruct (raw_termOpeningTraces_concatenate M hPA
    cutoff liftedReplacement
    leftSourceCode leftSourceStep leftTargetCode leftTargetStep
    leftBound leftRootIndex inputLeft outputLeft
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightBound rightRootIndex inputRight outputRight hleft hright)
    as (sourceCode & sourceStep & targetCode & targetStep &
        hcombined & hleftRoot).
  destruct hcombined as
    [hsource [htarget [hrightBelow [hrightRoot hrows]]]].
  set (bound := raw_add M leftBound rightBound).
  assert (hbundle : RawTermOpeningTraversalBundle M cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep bound).
  { repeat split; assumption. }
  assert (hrow : RawCodedTermOpeningTraversalRow M cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep bound
      (rawTermAddCode M inputLeft inputRight)
      (rawTermAddCode M outputLeft outputRight)).
  {
    right. right. right. left.
    exists leftRootIndex, inputLeft, outputLeft,
      (raw_add M leftBound rightRootIndex), inputRight, outputRight.
    split.
    - exact (raw_lt_le_trans_pair M hPA leftRootIndex leftBound bound
        hleftBelow (raw_proof_left_le_sum M leftBound rightBound)).
    - split; [exact hleftRoot |]. split; [exact hrightBelow |].
      split; [exact hrightRoot |]. split; reflexivity.
  }
  destruct (raw_termOpeningTraversalBundle_append M hPA
    cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
    bound (rawTermAddCode M inputLeft inputRight)
    (rawTermAddCode M outputLeft outputRight) hbundle hrow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        hnewBundle & _ & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    (raw_succ M bound), bound.
  destruct hnewBundle as [hnewSource [hnewTarget hnewRows]].
  exact (conj hnewSource
    (conj hnewTarget
      (conj (raw_assignment_lt_self_succ M hPA bound)
        (conj hnewRoot hnewRows)))).
Qed.

Lemma raw_codedTermOpening_mul : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement
      inputLeft outputLeft inputRight outputRight,
  RawCodedTermOpening M cutoff liftedReplacement inputLeft outputLeft ->
  RawCodedTermOpening M cutoff liftedReplacement inputRight outputRight ->
  RawCodedTermOpening M cutoff liftedReplacement
    (rawTermMulCode M inputLeft inputRight)
    (rawTermMulCode M outputLeft outputRight).
Proof.
  intros M hPA cutoff liftedReplacement
    inputLeft outputLeft inputRight outputRight
    (leftSourceCode & leftSourceStep & leftTargetCode & leftTargetStep &
     leftBound & leftRootIndex & hleft)
    (rightSourceCode & rightSourceStep & rightTargetCode & rightTargetStep &
     rightBound & rightRootIndex & hright).
  assert (hleftBelow : rawLt M leftRootIndex leftBound).
  { exact (proj1 (proj2 (proj2 hleft))). }
  destruct (raw_termOpeningTraces_concatenate M hPA
    cutoff liftedReplacement
    leftSourceCode leftSourceStep leftTargetCode leftTargetStep
    leftBound leftRootIndex inputLeft outputLeft
    rightSourceCode rightSourceStep rightTargetCode rightTargetStep
    rightBound rightRootIndex inputRight outputRight hleft hright)
    as (sourceCode & sourceStep & targetCode & targetStep &
        hcombined & hleftRoot).
  destruct hcombined as
    [hsource [htarget [hrightBelow [hrightRoot hrows]]]].
  set (bound := raw_add M leftBound rightBound).
  assert (hbundle : RawTermOpeningTraversalBundle M cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep bound).
  { repeat split; assumption. }
  assert (hrow : RawCodedTermOpeningTraversalRow M cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep bound
      (rawTermMulCode M inputLeft inputRight)
      (rawTermMulCode M outputLeft outputRight)).
  {
    right. right. right. right.
    exists leftRootIndex, inputLeft, outputLeft,
      (raw_add M leftBound rightRootIndex), inputRight, outputRight.
    split.
    - exact (raw_lt_le_trans_pair M hPA leftRootIndex leftBound bound
        hleftBelow (raw_proof_left_le_sum M leftBound rightBound)).
    - split; [exact hleftRoot |]. split; [exact hrightBelow |].
      split; [exact hrightRoot |]. split; reflexivity.
  }
  destruct (raw_termOpeningTraversalBundle_append M hPA
    cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
    bound (rawTermMulCode M inputLeft inputRight)
    (rawTermMulCode M outputLeft outputRight) hbundle hrow)
    as (newSourceCode & newSourceStep & newTargetCode & newTargetStep &
        hnewBundle & _ & hnewRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep,
    (raw_succ M bound), bound.
  destruct hnewBundle as [hnewSource [hnewTarget hnewRows]].
  exact (conj hnewSource
    (conj hnewTarget
      (conj (raw_assignment_lt_self_succ M hPA bound)
        (conj hnewRoot hnewRows)))).
Qed.

(** ------------------------------------------------------------------
    PA-definable strong induction over a represented term traversal. *)

Definition RawCodedTermOpeningTotalBelow (M : RawPAModel)
    (cutoff liftedReplacement supportCode supportStep current : M) : Prop :=
  forall input : M,
    rawLt M input current ->
    rawTermCodeSupported M supportCode supportStep input ->
    exists output : M,
      RawCodedTermOpening M cutoff liftedReplacement input output.

Arguments RawCodedTermOpeningTotalBelow M
  cutoff liftedReplacement supportCode supportStep current : clear implicits.

Definition codedTermOpeningTotalBelowTermAt
    (cutoff liftedReplacement supportCode supportStep current : term)
    : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 current))
      (pImp
        (termCodeSupportedTermAt
          (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
        (pEx
          (codedTermOpeningTermAt
            (liftTerm 2 cutoff) (liftTerm 2 liftedReplacement)
            (tVar 1) (tVar 0))))).

Lemma raw_sat_codedTermOpeningTotalBelowTermAt_iff : forall
    (M : RawPAModel) e cutoff liftedReplacement
      supportCode supportStep current,
  raw_formula_sat M e
    (codedTermOpeningTotalBelowTermAt
      cutoff liftedReplacement supportCode supportStep current) <->
  RawCodedTermOpeningTotalBelow M
    (raw_term_eval M e cutoff) (raw_term_eval M e liftedReplacement)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold codedTermOpeningTotalBelowTermAt,
    RawCodedTermOpeningTotalBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_termCodeSupportedTermAt_iff.
  setoid_rewrite raw_sat_codedTermOpeningTermAt_iff.
  repeat setoid_rewrite raw_shiftTotality_eval_liftTerm_one.
  repeat setoid_rewrite raw_shiftTotality_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_codedTermOpeningTotalBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement supportCode supportStep,
  RawCodedTermOpeningTotalBelow M cutoff liftedReplacement
    supportCode supportStep (raw_zero M).
Proof.
  intros M hPA cutoff liftedReplacement supportCode supportStep
    input hinput _.
  exfalso. exact (raw_not_lt_zero M hPA input hinput).
Qed.

Lemma raw_codedTermOpeningTotalBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement limit supportCode supportStep current,
  RawTermSyntaxTraversal M limit supportCode supportStep ->
  rawLt M current limit ->
  RawCodedTermOpeningTotalBelow M cutoff liftedReplacement
    supportCode supportStep current ->
  RawCodedTermOpeningTotalBelow M cutoff liftedReplacement
    supportCode supportStep (raw_succ M current).
Proof.
  intros M hPA cutoff liftedReplacement limit supportCode supportStep
    current [_ hsyntaxRows] hcurrentBound hprefix input hinput hsupported.
  destruct (raw_lt_succ_cases M hPA input current hinput)
    as [hbefore | ->].
  - exact (hprefix input hbefore hsupported).
  - destruct (hsyntaxRows current hcurrentBound hsupported)
      as (left & right & hshape).
    destruct hshape as
      [hvar | [hzero | [hsucc | [hadd | hmul]]]].
    + subst current.
      exact (raw_codedTermOpening_variable_exists M hPA
        cutoff liftedReplacement left).
    + subst current. exists (rawTermZeroCode M).
      exact (raw_codedTermOpening_zero M hPA
        cutoff liftedReplacement).
    + destruct hsucc as [hcode [hchildSupported hchild]].
      subst current.
      destruct (hprefix left hchild hchildSupported)
        as [outputChild houtputChild].
      exists (rawTermSuccCode M outputChild).
      exact (raw_codedTermOpening_succ M hPA
        cutoff liftedReplacement left outputChild houtputChild).
    + destruct hadd as
        [hcode [hleftSupported [hrightSupported [hleft hright]]]].
      subst current.
      destruct (hprefix left hleft hleftSupported)
        as [outputLeft houtputLeft].
      destruct (hprefix right hright hrightSupported)
        as [outputRight houtputRight].
      exists (rawTermAddCode M outputLeft outputRight).
      exact (raw_codedTermOpening_add M hPA cutoff liftedReplacement
        left outputLeft right outputRight houtputLeft houtputRight).
    + destruct hmul as
        [hcode [hleftSupported [hrightSupported [hleft hright]]]].
      subst current.
      destruct (hprefix left hleft hleftSupported)
        as [outputLeft houtputLeft].
      destruct (hprefix right hright hrightSupported)
        as [outputRight houtputRight].
      exists (rawTermMulCode M outputLeft outputRight).
      exact (raw_codedTermOpening_mul M hPA cutoff liftedReplacement
        left outputLeft right outputRight houtputLeft houtputRight).
Qed.

Definition RawCodedTermOpeningTotalWithin (M : RawPAModel)
    (cutoff liftedReplacement limit supportCode supportStep current : M)
    : Prop :=
  rawLe M current limit ->
  RawCodedTermOpeningTotalBelow M cutoff liftedReplacement
    supportCode supportStep current.

Arguments RawCodedTermOpeningTotalWithin M
  cutoff liftedReplacement limit supportCode supportStep current
  : clear implicits.

Definition codedTermOpeningTotalWithinTermAt
    (cutoff liftedReplacement limit supportCode supportStep current : term)
    : formula :=
  pImp
    (Formula.leTermAt current limit)
    (codedTermOpeningTotalBelowTermAt
      cutoff liftedReplacement supportCode supportStep current).

Lemma raw_sat_codedTermOpeningTotalWithinTermAt_iff : forall
    (M : RawPAModel) e cutoff liftedReplacement limit
      supportCode supportStep current,
  raw_formula_sat M e
    (codedTermOpeningTotalWithinTermAt
      cutoff liftedReplacement limit supportCode supportStep current) <->
  RawCodedTermOpeningTotalWithin M
    (raw_term_eval M e cutoff) (raw_term_eval M e liftedReplacement)
    (raw_term_eval M e limit)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold codedTermOpeningTotalWithinTermAt,
    RawCodedTermOpeningTotalWithin.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank,
    raw_sat_codedTermOpeningTotalBelowTermAt_iff.
  reflexivity.
Qed.

Theorem raw_codedTermOpeningTotalWithin_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      cutoff liftedReplacement limit supportCode supportStep,
  RawTermSyntaxTraversal M limit supportCode supportStep ->
  forall current,
    RawCodedTermOpeningTotalWithin M cutoff liftedReplacement
      limit supportCode supportStep current.
Proof.
  intros M hPA cutoff liftedReplacement limit supportCode supportStep
    hsyntax.
  set (parameterEnv := scons M cutoff
    (scons M liftedReplacement (scons M limit
      (scons M supportCode (scons M supportStep
        (fun _ : nat => raw_zero M)))))).
  set (phi := codedTermOpeningTotalWithinTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_codedTermOpeningTotalWithinTermAt_iff M
        (scons M (raw_zero M) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons]. intros _.
      exact (raw_codedTermOpeningTotalBelow_zero M hPA
        cutoff liftedReplacement supportCode supportStep).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedTermOpeningTotalWithinTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2 (raw_sat_codedTermOpeningTotalWithinTermAt_iff M
        (scons M (raw_succ M current) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      intro hsuccBound.
      assert (hcurrentBound : rawLt M current limit).
      { exact (raw_rank_lt_of_succ_le M hPA current limit hsuccBound). }
      apply (raw_codedTermOpeningTotalBelow_succ M hPA
        cutoff liftedReplacement limit supportCode supportStep current
        hsyntax hcurrentBound).
      apply hcurrent.
      exact (raw_lt_to_le M current limit hcurrentBound).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedTermOpeningTotalWithinTermAt_iff M
      (scons M current parameterEnv)
      (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5) (tVar 0))
    (hall current)) as hcurrent.
  unfold parameterEnv in hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

(** Public exact totality theorem.  The output and every trace table may be
    nonstandard carrier values; the proof uses only the supplied represented
    source traversal. *)
Theorem raw_codedTermOpening_exists_of_syntax_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      input assignmentCode assignmentStep,
  RawTermSyntaxRealizable M input assignmentCode assignmentStep ->
  forall cutoff liftedReplacement,
    exists output,
      RawCodedTermOpening M cutoff liftedReplacement input output.
Proof.
  intros M hPA input assignmentCode assignmentStep
    (supportCode & supportStep & hsyntax & _ & hrootSupported)
    cutoff liftedReplacement.
  pose proof (raw_codedTermOpeningTotalWithin_all M hPA
    cutoff liftedReplacement (raw_succ M input)
    supportCode supportStep hsyntax (raw_succ M input)) as hall.
  specialize (hall (raw_rank_le_refl M hPA (raw_succ M input))).
  exact (hall input
    (raw_assignment_lt_self_succ M hPA input) hrootSupported).
Qed.

End PABoundedRawCodedTermOpeningTotality.
