(**
  Totality of [RawCodedFormulaBound] on model-internal formula syntax.

  A formula-syntax certificate is occurrence-indexed, whereas the public
  bound graph is indexed through the carrier formula code itself.  We bridge
  that mismatch by constructing fresh source and bound beta columns through
  every carrier stage.  Atomically adequate formula codes are normalized to
  themselves; all other codes receive the harmless bottom/zero row.  Since
  every recursive constructor payload is strictly below its enclosing code,
  normalized child rows are already available at the successor step.

  Equality atoms invoke the independently checked all-carrier term-bound
  theorem.  No carrier code is decoded into a metatheoretic Rocq formula or
  term.
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
  RawCodedFixedLevelTruthTotality RawCodedPAAxiomWitness
  RawCodedPAAxiomContextSelfShift RawCodedFormulaShiftTotality
  RawCodedFormulaOperationRankPreservation
  RawCodedFormulaBoundAllCarrierBoundary
  RawCodedFormulaBoundAllCarrierTotality.

Module PABoundedRawCodedFormulaBoundAtomicallyAdequateTotality.

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
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedFormulaOperationRankPreservation.
Import PABoundedRawCodedFormulaBoundAllCarrierBoundary.
Import PABoundedRawCodedFormulaBoundAllCarrierTotality.

(** ------------------------------------------------------------------
    The normalized prefix and its PA formula. *)

Definition RawCodedFormulaBoundPrefixRows (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep current : M) : Prop :=
  forall index input output : M,
    rawLt M index current ->
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep index input output ->
    RawCodedFormulaBoundTraversalRow M
      sourceCode sourceStep targetCode targetStep index input output.

Definition codedFormulaBoundPrefixRowsTermAt
    (sourceCode sourceStep targetCode targetStep current : term) : formula :=
  pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 3 current))
      (pImp
        (codedTermOperationPairLookupTermAt
          (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
          (liftTerm 3 targetCode) (liftTerm 3 targetStep)
          (tVar 2) (tVar 1) (tVar 0))
        (codedFormulaBoundTraversalRowTermAt
          (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
          (liftTerm 3 targetCode) (liftTerm 3 targetStep)
          (tVar 2) (tVar 1) (tVar 0)))))).

Lemma raw_sat_codedFormulaBoundPrefixRowsTermAt_iff : forall
    (M : RawPAModel) e sourceCode sourceStep targetCode targetStep current,
  raw_formula_sat M e
    (codedFormulaBoundPrefixRowsTermAt
      sourceCode sourceStep targetCode targetStep current) <->
  RawCodedFormulaBoundPrefixRows M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold codedFormulaBoundPrefixRowsTermAt,
    RawCodedFormulaBoundPrefixRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaBoundTraversalRowTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawCodedFormulaBoundPrefixNormalized (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep current : M) : Prop :=
  forall index : M,
    rawLt M index current ->
    RawCodedFormulaAtomicallyAdequate M index ->
    exists output : M,
      RawCodedTermOperationPairLookup M
        sourceCode sourceStep targetCode targetStep index index output.

Definition codedFormulaBoundPrefixNormalizedTermAt
    (sourceCode sourceStep targetCode targetStep current : term) : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 current))
      (pImp
        (codedFormulaAtomicallyAdequateTermAt (tVar 0))
        (pEx
          (codedTermOperationPairLookupTermAt
            (liftTerm 2 sourceCode) (liftTerm 2 sourceStep)
            (liftTerm 2 targetCode) (liftTerm 2 targetStep)
            (tVar 1) (tVar 1) (tVar 0))))).

Lemma raw_sat_codedFormulaBoundPrefixNormalizedTermAt_iff : forall
    (M : RawPAModel) e sourceCode sourceStep targetCode targetStep current,
  raw_formula_sat M e
    (codedFormulaBoundPrefixNormalizedTermAt
      sourceCode sourceStep targetCode targetStep current) <->
  RawCodedFormulaBoundPrefixNormalized M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold codedFormulaBoundPrefixNormalizedTermAt,
    RawCodedFormulaBoundPrefixNormalized.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  repeat setoid_rewrite raw_shiftTotality_eval_liftTerm_one.
  repeat setoid_rewrite raw_shiftTotality_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawCodedFormulaBoundPrefix (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep current : M) : Prop :=
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep current /\
  RawCodedAssignmentDefinedThrough M targetCode targetStep current /\
  RawCodedFormulaBoundPrefixRows M
    sourceCode sourceStep targetCode targetStep current /\
  RawCodedFormulaBoundPrefixNormalized M
    sourceCode sourceStep targetCode targetStep current.

Definition codedFormulaBoundPrefixTermAt
    (sourceCode sourceStep targetCode targetStep current : term) : formula :=
  operationAnd4
    (codedAssignmentDefinedThroughTermAt sourceCode sourceStep current)
    (codedAssignmentDefinedThroughTermAt targetCode targetStep current)
    (codedFormulaBoundPrefixRowsTermAt
      sourceCode sourceStep targetCode targetStep current)
    (codedFormulaBoundPrefixNormalizedTermAt
      sourceCode sourceStep targetCode targetStep current).

Lemma raw_sat_codedFormulaBoundPrefixTermAt_iff : forall
    (M : RawPAModel) e sourceCode sourceStep targetCode targetStep current,
  raw_formula_sat M e
    (codedFormulaBoundPrefixTermAt
      sourceCode sourceStep targetCode targetStep current) <->
  RawCodedFormulaBoundPrefix M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold codedFormulaBoundPrefixTermAt,
    RawCodedFormulaBoundPrefix, operationAnd4.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  rewrite raw_sat_codedFormulaBoundPrefixRowsTermAt_iff.
  rewrite raw_sat_codedFormulaBoundPrefixNormalizedTermAt_iff.
  reflexivity.
Qed.

Definition RawCodedFormulaBoundPrefixExists
    (M : RawPAModel) (current : M) : Prop :=
  exists sourceCode sourceStep targetCode targetStep : M,
    RawCodedFormulaBoundPrefix M
      sourceCode sourceStep targetCode targetStep current.

Definition codedFormulaBoundPrefixExistsTermAt (current : term) : formula :=
  operationEx4
    (codedFormulaBoundPrefixTermAt
      (tVar 3) (tVar 2) (tVar 1) (tVar 0) (liftTerm 4 current)).

Lemma raw_sat_codedFormulaBoundPrefixExistsTermAt_iff : forall
    (M : RawPAModel) e current,
  raw_formula_sat M e (codedFormulaBoundPrefixExistsTermAt current) <->
  RawCodedFormulaBoundPrefixExists M (raw_term_eval M e current).
Proof.
  intros. unfold codedFormulaBoundPrefixExistsTermAt,
    RawCodedFormulaBoundPrefixExists, operationEx4.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedFormulaBoundPrefixTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Prefix transport and one-row append. *)

Lemma raw_formulaBoundTraversalRow_prefix_extend : forall
    (M : RawPAModel), RawPASatisfies M -> forall bound current
      oldSourceCode oldSourceStep oldTargetCode oldTargetStep
      newSourceCode newSourceStep newTargetCode newTargetStep input output,
  RawTermShiftTablePrefixExtension M bound
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    newSourceCode newSourceStep newTargetCode newTargetStep ->
  rawLe M current bound ->
  RawCodedFormulaBoundTraversalRow M
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    current input output ->
  RawCodedFormulaBoundTraversalRow M
    newSourceCode newSourceStep newTargetCode newTargetStep
    current input output.
Proof.
  intros M hPA bound current oldSourceCode oldSourceStep
    oldTargetCode oldTargetStep newSourceCode newSourceStep
    newTargetCode newTargetStep input output hext hcurrent hrow.
  destruct hrow as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - left. exact heq.
  - right. left. exact hbot.
  - right. right. left.
    destruct himp as
      (leftIndex & inputLeft & leftBound &
       rightIndex & inputRight & rightBound &
       hleft & hleftLookup & hright & hrightLookup & hinput & houtput).
    exists leftIndex, inputLeft, leftBound,
      rightIndex, inputRight, rightBound.
    split; [exact hleft |]. split.
    + apply (raw_termShiftPairLookup_prefix_extend M bound
        oldSourceCode oldSourceStep oldTargetCode oldTargetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        leftIndex inputLeft leftBound hext).
      * exact (raw_lt_le_trans_pair M hPA
          leftIndex current bound hleft hcurrent).
      * exact hleftLookup.
    + split; [exact hright |]. split.
      * apply (raw_termShiftPairLookup_prefix_extend M bound
          oldSourceCode oldSourceStep oldTargetCode oldTargetStep
          newSourceCode newSourceStep newTargetCode newTargetStep
          rightIndex inputRight rightBound hext).
        -- exact (raw_lt_le_trans_pair M hPA
             rightIndex current bound hright hcurrent).
        -- exact hrightLookup.
      * split; assumption.
  - right. right. right. left.
    destruct hand as
      (leftIndex & inputLeft & leftBound &
       rightIndex & inputRight & rightBound &
       hleft & hleftLookup & hright & hrightLookup & hinput & houtput).
    exists leftIndex, inputLeft, leftBound,
      rightIndex, inputRight, rightBound.
    split; [exact hleft |]. split.
    + apply (raw_termShiftPairLookup_prefix_extend M bound
        oldSourceCode oldSourceStep oldTargetCode oldTargetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        leftIndex inputLeft leftBound hext).
      * exact (raw_lt_le_trans_pair M hPA
          leftIndex current bound hleft hcurrent).
      * exact hleftLookup.
    + split; [exact hright |]. split.
      * apply (raw_termShiftPairLookup_prefix_extend M bound
          oldSourceCode oldSourceStep oldTargetCode oldTargetStep
          newSourceCode newSourceStep newTargetCode newTargetStep
          rightIndex inputRight rightBound hext).
        -- exact (raw_lt_le_trans_pair M hPA
             rightIndex current bound hright hcurrent).
        -- exact hrightLookup.
      * split; assumption.
  - right. right. right. right. left.
    destruct hor as
      (leftIndex & inputLeft & leftBound &
       rightIndex & inputRight & rightBound &
       hleft & hleftLookup & hright & hrightLookup & hinput & houtput).
    exists leftIndex, inputLeft, leftBound,
      rightIndex, inputRight, rightBound.
    split; [exact hleft |]. split.
    + apply (raw_termShiftPairLookup_prefix_extend M bound
        oldSourceCode oldSourceStep oldTargetCode oldTargetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        leftIndex inputLeft leftBound hext).
      * exact (raw_lt_le_trans_pair M hPA
          leftIndex current bound hleft hcurrent).
      * exact hleftLookup.
    + split; [exact hright |]. split.
      * apply (raw_termShiftPairLookup_prefix_extend M bound
          oldSourceCode oldSourceStep oldTargetCode oldTargetStep
          newSourceCode newSourceStep newTargetCode newTargetStep
          rightIndex inputRight rightBound hext).
        -- exact (raw_lt_le_trans_pair M hPA
             rightIndex current bound hright hcurrent).
        -- exact hrightLookup.
      * split; assumption.
  - right. right. right. right. right. left.
    destruct hall as
      (childIndex & inputChild & childBound & hchild & hlookup &
       hinput & houtput).
    exists childIndex, inputChild, childBound.
    split; [exact hchild |]. split.
    + apply (raw_termShiftPairLookup_prefix_extend M bound
        oldSourceCode oldSourceStep oldTargetCode oldTargetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        childIndex inputChild childBound hext).
      * exact (raw_lt_le_trans_pair M hPA
          childIndex current bound hchild hcurrent).
      * exact hlookup.
    + split; assumption.
  - right. right. right. right. right. right.
    destruct hex as
      (childIndex & inputChild & childBound & hchild & hlookup &
       hinput & houtput).
    exists childIndex, inputChild, childBound.
    split; [exact hchild |]. split.
    + apply (raw_termShiftPairLookup_prefix_extend M bound
        oldSourceCode oldSourceStep oldTargetCode oldTargetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        childIndex inputChild childBound hext).
      * exact (raw_lt_le_trans_pair M hPA
          childIndex current bound hchild hcurrent).
      * exact hlookup.
    + split; assumption.
Qed.

(** This append lemma contains all beta-table bookkeeping.  Its last premise
    records exactly why the fresh source value is normalized at an adequate
    code. *)
Theorem raw_codedFormulaBoundPrefix_append : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sourceCode sourceStep targetCode targetStep current input output,
  RawCodedFormulaBoundPrefix M
    sourceCode sourceStep targetCode targetStep current ->
  RawCodedFormulaBoundTraversalRow M
    sourceCode sourceStep targetCode targetStep current input output ->
  (RawCodedFormulaAtomicallyAdequate M current -> input = current) ->
  RawCodedFormulaBoundPrefixExists M (raw_succ M current).
Proof.
  intros M hPA sourceCode sourceStep targetCode targetStep
    current input output
    (hsourceDefined & htargetDefined & hrows & hnormalized)
    hclosed hinputNormalized.
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    sourceCode sourceStep current input hsourceDefined)
    as (newSourceCode & newSourceStep & hnewSource & hsourcePrefix &
        hsourceRoot).
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    targetCode targetStep current output htargetDefined)
    as (newTargetCode & newTargetStep & hnewTarget & htargetPrefix &
        htargetRoot).
  exists newSourceCode, newSourceStep, newTargetCode, newTargetStep.
  split; [exact hnewSource |]. split; [exact hnewTarget |]. split.
  - intros index rowInput rowOutput hindex [hrowInput hrowOutput].
    destruct (raw_lt_succ_cases M hPA index current hindex)
      as [hbefore | ->].
    + destruct (hsourceDefined index hbefore) as [oldInput holdInput].
      destruct (htargetDefined index hbefore) as [oldOutput holdOutput].
      assert (hnewOld : RawCodedTermOperationPairLookup M
          newSourceCode newSourceStep newTargetCode newTargetStep
          index oldInput oldOutput).
      { split; [apply hsourcePrefix | apply htargetPrefix]; assumption. }
      assert (rowInput = oldInput) as -> by
        (eapply raw_codedAssignmentLookup_functional;
         [exact hPA | exact hrowInput | exact (proj1 hnewOld)]).
      assert (rowOutput = oldOutput) as -> by
        (eapply raw_codedAssignmentLookup_functional;
         [exact hPA | exact hrowOutput | exact (proj2 hnewOld)]).
      apply (raw_formulaBoundTraversalRow_prefix_extend M hPA
        current index sourceCode sourceStep targetCode targetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        oldInput oldOutput (conj hsourcePrefix htargetPrefix)).
      * exact (raw_lt_to_le M index current hbefore).
      * apply hrows; [exact hbefore |]. split; assumption.
    + assert (rowInput = input) as -> by
        (eapply raw_codedAssignmentLookup_functional;
         [exact hPA | exact hrowInput | exact hsourceRoot]).
      assert (rowOutput = output) as -> by
        (eapply raw_codedAssignmentLookup_functional;
         [exact hPA | exact hrowOutput | exact htargetRoot]).
      apply (raw_formulaBoundTraversalRow_prefix_extend M hPA
        current current sourceCode sourceStep targetCode targetStep
        newSourceCode newSourceStep newTargetCode newTargetStep
        input output (conj hsourcePrefix htargetPrefix)).
      * exact (raw_rank_le_refl M hPA current).
      * exact hclosed.
  - intros index hindex hadequate.
    destruct (raw_lt_succ_cases M hPA index current hindex)
      as [hbefore | ->].
    + destruct (hnormalized index hbefore hadequate)
        as [oldOutput [holdSource holdTarget]].
      exists oldOutput. split;
        [apply hsourcePrefix | apply htargetPrefix]; assumption.
    + exists output. split.
      * pose proof (hinputNormalized hadequate) as hinputEq.
        subst input. exact hsourceRoot.
      * exact htargetRoot.
Qed.

Lemma raw_codedFormulaBoundPrefix_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaBoundPrefixExists M (raw_zero M).
Proof.
  intros M hPA.
  exists (raw_zero M), (raw_zero M), (raw_zero M), (raw_zero M).
  repeat split.
  - exact (raw_codedZeroAssignment_defined_all M hPA (raw_zero M)).
  - exact (raw_codedZeroAssignment_defined_all M hPA (raw_zero M)).
  - intros index input output hindex _.
    exfalso. exact (raw_not_lt_zero M hPA index hindex).
  - intros index hindex _.
    exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

(** A child occurrence reuses the parent's occurrence table and atomic-term
    adequacy witness.  Only the root occurrence index changes. *)
Lemma raw_codedFormulaAtomicallyAdequate_child_at : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      formulaCode formulaStep bound rootIndex root childIndex child,
  RawCodedFormulaSyntaxTraversal M
    formulaCode formulaStep bound rootIndex root ->
  RawCodedFormulaAtomicTermAdequate M formulaCode formulaStep bound ->
  rawLt M childIndex rootIndex ->
  RawCodedAssignmentLookup M formulaCode formulaStep childIndex child ->
  RawCodedFormulaAtomicallyAdequate M child.
Proof.
  intros M hPA formulaCode formulaStep bound rootIndex root
    childIndex child
    (hdefined & hrootBound & hrootLookup & hrows) hatomic
    hchildIndex hchildLookup.
  exists formulaCode, formulaStep, bound, childIndex.
  split.
  - split; [exact hdefined |]. split.
    + exact (raw_assignment_lt_trans M hPA
        childIndex rootIndex bound hchildIndex hrootBound).
    + split; [exact hchildLookup | exact hrows].
  - exact hatomic.
Qed.

(** One syntax-code stage.  The case split is on the represented root row,
    never on a decoded Rocq formula. *)
Theorem raw_codedFormulaBoundPrefix_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedFormulaBoundPrefixExists M current ->
  RawCodedFormulaBoundPrefixExists M (raw_succ M current).
Proof.
  intros M hPA current
    (sourceCode & sourceStep & targetCode & targetStep & hprefix).
  destruct (classic (RawCodedFormulaAtomicallyAdequate M current))
    as [hcurrentAdequate | hcurrentInadequate].
  - destruct hcurrentAdequate as
      (formulaCode & formulaStep & syntaxBound & rootIndex &
       hsyntax & hatomicTerms).
    pose proof hsyntax as
      (hformulaDefined & hrootBound & hrootLookup & hsyntaxRows).
    pose proof (hsyntaxRows rootIndex current hrootBound hrootLookup)
      as hrootRow.
    destruct hrootRow as
      [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
    + destruct heq as [left [right hcode]].
      destruct (raw_codedAssignmentExistsThrough_all M hPA current)
        as (assignmentCode & assignmentStep & hassignment).
      destruct (hatomicTerms rootIndex current left right
        assignmentCode assignmentStep hrootBound hrootLookup hcode
        hassignment) as [hleftSyntax hrightSyntax].
      destruct (raw_codedTermBound_exists_of_syntax_realizable M hPA
        left assignmentCode assignmentStep hleftSyntax)
        as [leftBound hleftBound].
      destruct (raw_codedTermBound_exists_of_syntax_realizable M hPA
        right assignmentCode assignmentStep hrightSyntax)
        as [rightBound hrightBound].
      set (output := raw_add M leftBound rightBound).
      assert (hclosed : RawCodedFormulaBoundTraversalRow M
          sourceCode sourceStep targetCode targetStep
          current current output).
      { left. exists left, leftBound, right, rightBound.
        split; [exact hcode |]. split; [exact hleftBound |].
        split; [exact hrightBound |]. unfold output. reflexivity. }
      apply (raw_codedFormulaBoundPrefix_append M hPA
        sourceCode sourceStep targetCode targetStep
        current current output hprefix hclosed).
      intros _. reflexivity.
    + set (output := raw_zero M).
      assert (hclosed : RawCodedFormulaBoundTraversalRow M
          sourceCode sourceStep targetCode targetStep
          current current output).
      { right. left. unfold output. split; [exact hbot | reflexivity]. }
      apply (raw_codedFormulaBoundPrefix_append M hPA
        sourceCode sourceStep targetCode targetStep
        current current output hprefix hclosed).
      intros _. reflexivity.
    + destruct himp as
        (leftOccurrence & left & rightOccurrence & right &
         hleftOccurrence & hleftLookup &
         hrightOccurrence & hrightLookup & hcode).
      assert (hleftAdequate : RawCodedFormulaAtomicallyAdequate M left).
      { exact (raw_codedFormulaAtomicallyAdequate_child_at M hPA
          formulaCode formulaStep syntaxBound rootIndex current
          leftOccurrence left hsyntax hatomicTerms
          hleftOccurrence hleftLookup). }
      assert (hrightAdequate : RawCodedFormulaAtomicallyAdequate M right).
      { exact (raw_codedFormulaAtomicallyAdequate_child_at M hPA
          formulaCode formulaStep syntaxBound rootIndex current
          rightOccurrence right hsyntax hatomicTerms
          hrightOccurrence hrightLookup). }
      assert (hleftCode : rawLt M left current).
      { rewrite hcode. unfold rawFormulaImpCode.
        exact (raw_formulaOperation_binary_left_lt M hPA
          (rawNumeralValue M 2) left right). }
      assert (hrightCode : rawLt M right current).
      { rewrite hcode. unfold rawFormulaImpCode.
        exact (raw_formulaOperation_binary_right_lt M hPA
          (rawNumeralValue M 2) left right). }
      destruct hprefix as
        (hsourceDefined & htargetDefined & hrows & hnormalized).
      destruct (hnormalized left hleftCode hleftAdequate)
        as [leftBound hleftBound].
      destruct (hnormalized right hrightCode hrightAdequate)
        as [rightBound hrightBound].
      set (output := raw_add M leftBound rightBound).
      assert (hclosed : RawCodedFormulaBoundTraversalRow M
          sourceCode sourceStep targetCode targetStep
          current current output).
      { right. right. left.
        exists left, left, leftBound, right, right, rightBound.
        split; [exact hleftCode |]. split; [exact hleftBound |].
        split; [exact hrightCode |]. split; [exact hrightBound |].
        split; [exact hcode |]. unfold output. reflexivity. }
      apply (raw_codedFormulaBoundPrefix_append M hPA
        sourceCode sourceStep targetCode targetStep current current output).
      * repeat split; assumption.
      * exact hclosed.
      * intros _. reflexivity.
    + destruct hand as
        (leftOccurrence & left & rightOccurrence & right &
         hleftOccurrence & hleftLookup &
         hrightOccurrence & hrightLookup & hcode).
      assert (hleftAdequate : RawCodedFormulaAtomicallyAdequate M left).
      { exact (raw_codedFormulaAtomicallyAdequate_child_at M hPA
          formulaCode formulaStep syntaxBound rootIndex current
          leftOccurrence left hsyntax hatomicTerms
          hleftOccurrence hleftLookup). }
      assert (hrightAdequate : RawCodedFormulaAtomicallyAdequate M right).
      { exact (raw_codedFormulaAtomicallyAdequate_child_at M hPA
          formulaCode formulaStep syntaxBound rootIndex current
          rightOccurrence right hsyntax hatomicTerms
          hrightOccurrence hrightLookup). }
      assert (hleftCode : rawLt M left current).
      { rewrite hcode. unfold rawFormulaAndCode.
        exact (raw_formulaOperation_binary_left_lt M hPA
          (rawNumeralValue M 3) left right). }
      assert (hrightCode : rawLt M right current).
      { rewrite hcode. unfold rawFormulaAndCode.
        exact (raw_formulaOperation_binary_right_lt M hPA
          (rawNumeralValue M 3) left right). }
      destruct hprefix as
        (hsourceDefined & htargetDefined & hrows & hnormalized).
      destruct (hnormalized left hleftCode hleftAdequate)
        as [leftBound hleftBound].
      destruct (hnormalized right hrightCode hrightAdequate)
        as [rightBound hrightBound].
      set (output := raw_add M leftBound rightBound).
      assert (hclosed : RawCodedFormulaBoundTraversalRow M
          sourceCode sourceStep targetCode targetStep
          current current output).
      { right. right. right. left.
        exists left, left, leftBound, right, right, rightBound.
        split; [exact hleftCode |]. split; [exact hleftBound |].
        split; [exact hrightCode |]. split; [exact hrightBound |].
        split; [exact hcode |]. unfold output. reflexivity. }
      apply (raw_codedFormulaBoundPrefix_append M hPA
        sourceCode sourceStep targetCode targetStep current current output).
      * repeat split; assumption.
      * exact hclosed.
      * intros _. reflexivity.
    + destruct hor as
        (leftOccurrence & left & rightOccurrence & right &
         hleftOccurrence & hleftLookup &
         hrightOccurrence & hrightLookup & hcode).
      assert (hleftAdequate : RawCodedFormulaAtomicallyAdequate M left).
      { exact (raw_codedFormulaAtomicallyAdequate_child_at M hPA
          formulaCode formulaStep syntaxBound rootIndex current
          leftOccurrence left hsyntax hatomicTerms
          hleftOccurrence hleftLookup). }
      assert (hrightAdequate : RawCodedFormulaAtomicallyAdequate M right).
      { exact (raw_codedFormulaAtomicallyAdequate_child_at M hPA
          formulaCode formulaStep syntaxBound rootIndex current
          rightOccurrence right hsyntax hatomicTerms
          hrightOccurrence hrightLookup). }
      assert (hleftCode : rawLt M left current).
      { rewrite hcode. unfold rawFormulaOrCode.
        exact (raw_formulaOperation_binary_left_lt M hPA
          (rawNumeralValue M 4) left right). }
      assert (hrightCode : rawLt M right current).
      { rewrite hcode. unfold rawFormulaOrCode.
        exact (raw_formulaOperation_binary_right_lt M hPA
          (rawNumeralValue M 4) left right). }
      destruct hprefix as
        (hsourceDefined & htargetDefined & hrows & hnormalized).
      destruct (hnormalized left hleftCode hleftAdequate)
        as [leftBound hleftBound].
      destruct (hnormalized right hrightCode hrightAdequate)
        as [rightBound hrightBound].
      set (output := raw_add M leftBound rightBound).
      assert (hclosed : RawCodedFormulaBoundTraversalRow M
          sourceCode sourceStep targetCode targetStep
          current current output).
      { right. right. right. right. left.
        exists left, left, leftBound, right, right, rightBound.
        split; [exact hleftCode |]. split; [exact hleftBound |].
        split; [exact hrightCode |]. split; [exact hrightBound |].
        split; [exact hcode |]. unfold output. reflexivity. }
      apply (raw_codedFormulaBoundPrefix_append M hPA
        sourceCode sourceStep targetCode targetStep current current output).
      * repeat split; assumption.
      * exact hclosed.
      * intros _. reflexivity.
    + destruct hall as
        (childOccurrence & child & hchildOccurrence & hchildLookup & hcode).
      assert (hchildAdequate : RawCodedFormulaAtomicallyAdequate M child).
      { exact (raw_codedFormulaAtomicallyAdequate_child_at M hPA
          formulaCode formulaStep syntaxBound rootIndex current
          childOccurrence child hsyntax hatomicTerms
          hchildOccurrence hchildLookup). }
      assert (hchildCode : rawLt M child current).
      { rewrite hcode. unfold rawFormulaAllCode.
        exact (raw_formulaOperation_unary_child_lt M hPA
          (rawNumeralValue M 5) child). }
      destruct hprefix as
        (hsourceDefined & htargetDefined & hrows & hnormalized).
      destruct (hnormalized child hchildCode hchildAdequate)
        as [childBound hchildBound].
      set (output := childBound).
      assert (hclosed : RawCodedFormulaBoundTraversalRow M
          sourceCode sourceStep targetCode targetStep
          current current output).
      { right. right. right. right. right. left.
        exists child, child, childBound.
        split; [exact hchildCode |]. split; [exact hchildBound |].
        split; [exact hcode |]. unfold output. reflexivity. }
      apply (raw_codedFormulaBoundPrefix_append M hPA
        sourceCode sourceStep targetCode targetStep current current output).
      * repeat split; assumption.
      * exact hclosed.
      * intros _. reflexivity.
    + destruct hex as
        (childOccurrence & child & hchildOccurrence & hchildLookup & hcode).
      assert (hchildAdequate : RawCodedFormulaAtomicallyAdequate M child).
      { exact (raw_codedFormulaAtomicallyAdequate_child_at M hPA
          formulaCode formulaStep syntaxBound rootIndex current
          childOccurrence child hsyntax hatomicTerms
          hchildOccurrence hchildLookup). }
      assert (hchildCode : rawLt M child current).
      { rewrite hcode. unfold rawFormulaExCode.
        exact (raw_formulaOperation_unary_child_lt M hPA
          (rawNumeralValue M 6) child). }
      destruct hprefix as
        (hsourceDefined & htargetDefined & hrows & hnormalized).
      destruct (hnormalized child hchildCode hchildAdequate)
        as [childBound hchildBound].
      set (output := childBound).
      assert (hclosed : RawCodedFormulaBoundTraversalRow M
          sourceCode sourceStep targetCode targetStep
          current current output).
      { right. right. right. right. right. right.
        exists child, child, childBound.
        split; [exact hchildCode |]. split; [exact hchildBound |].
        split; [exact hcode |]. unfold output. reflexivity. }
      apply (raw_codedFormulaBoundPrefix_append M hPA
        sourceCode sourceStep targetCode targetStep current current output).
      * repeat split; assumption.
      * exact hclosed.
      * intros _. reflexivity.
  - (* Non-adequate codes receive the bottom/zero row. *)
    set (input := rawFormulaBotCode M).
    set (output := raw_zero M).
    destruct hprefix as
      (hsourceDefined & htargetDefined & hrows & hnormalized).
    assert (hclosed : RawCodedFormulaBoundTraversalRow M
        sourceCode sourceStep targetCode targetStep current input output).
    { right. left. unfold input, output. split; reflexivity. }
    apply (raw_codedFormulaBoundPrefix_append M hPA
      sourceCode sourceStep targetCode targetStep current input output).
    + repeat split; assumption.
    + exact hclosed.
    + intros hadequate. exfalso. exact (hcurrentInadequate hadequate).
Qed.

(** Genuine PA induction over all carrier stages. *)
Theorem raw_codedFormulaBoundPrefix_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall current,
  RawCodedFormulaBoundPrefixExists M current.
Proof.
  intros M hPA.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := codedFormulaBoundPrefixExistsTermAt (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_codedFormulaBoundPrefixExistsTermAt_iff M
        (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_codedFormulaBoundPrefix_zero M hPA).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedFormulaBoundPrefixExistsTermAt_iff M
          (scons M current parameterEnv) (tVar 0)) hcurrentSat)
        as hcurrent.
      apply (proj2
        (raw_sat_codedFormulaBoundPrefixExistsTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_codedFormulaBoundPrefix_succ M hPA current hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedFormulaBoundPrefixExistsTermAt_iff M
      (scons M current parameterEnv) (tVar 0)) (hall current)) as hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

(** The exact boundary proposition from
    [RawCodedFormulaBoundAllCarrierBoundary] is now discharged. *)
Theorem raw_codedFormulaBound_atomically_adequate_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaBoundAtomicallyAdequateTotal M.
Proof.
  intros M hPA input hadequate.
  destruct (raw_codedFormulaBoundPrefix_all M hPA (raw_succ M input))
    as (sourceCode & sourceStep & targetCode & targetStep &
        hsource & htarget & hrows & hnormalized).
  destruct (hnormalized input
    (raw_assignment_lt_self_succ M hPA input) hadequate)
    as [output hroot].
  exists output, sourceCode, sourceStep, targetCode, targetStep.
  split; [exact hsource |]. split; [exact htarget |].
  split; [exact hroot |]. exact hrows.
Qed.

End PABoundedRawCodedFormulaBoundAtomicallyAdequateTotality.
