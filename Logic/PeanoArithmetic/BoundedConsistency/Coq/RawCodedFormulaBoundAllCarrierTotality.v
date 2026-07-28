(**
  Carrier-level totality of the syntactic bound graphs.

  The tables used by [RawCodedTermBound] and [RawCodedFormulaBound] are
  indexed by syntax codes, not by occurrence numbers in a syntax witness.
  Consequently an occurrence traversal cannot simply be re-used.  This
  file builds fresh, normalized source and bound columns by genuine PA
  induction.  At a supported/adequate code the source column contains that
  code itself; at every other code it contains the harmless zero-term or
  bottom-formula row.  Thus recursive constructor payloads can be looked up
  at their own (strictly smaller) carrier codes.

  The first half carries out this construction for term bounds.  It is kept
  as a public theorem because equality atoms in the formula construction
  need exactly this nonstandard, represented-syntax totality result.
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
  RawCodedPAAxiomWitness RawCodedPAAxiomContextSelfShift
  RawCodedFormulaShiftTotality
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedFormulaOperationRankPreservation
  RawCodedFormulaBoundAllCarrierBoundary.

Module PABoundedRawCodedFormulaBoundAllCarrierTotality.

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
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedFormulaOperationRankPreservation.
Import PABoundedRawCodedFormulaBoundAllCarrierBoundary.

(** ------------------------------------------------------------------
    A normalized term-bound prefix. *)

Definition RawCodedTermBoundPrefixRows (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep current : M) : Prop :=
  forall index input output : M,
    rawLt M index current ->
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep index input output ->
    RawCodedTermBoundTraversalRow M
      sourceCode sourceStep targetCode targetStep index input output.

Definition codedTermBoundPrefixRowsTermAt
    (sourceCode sourceStep targetCode targetStep current : term) : formula :=
  pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 3 current))
      (pImp
        (codedTermOperationPairLookupTermAt
          (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
          (liftTerm 3 targetCode) (liftTerm 3 targetStep)
          (tVar 2) (tVar 1) (tVar 0))
        (codedTermBoundTraversalRowTermAt
          (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
          (liftTerm 3 targetCode) (liftTerm 3 targetStep)
          (tVar 2) (tVar 1) (tVar 0)))))).

Lemma raw_sat_codedTermBoundPrefixRowsTermAt_iff : forall
    (M : RawPAModel) e sourceCode sourceStep targetCode targetStep current,
  raw_formula_sat M e
    (codedTermBoundPrefixRowsTermAt
      sourceCode sourceStep targetCode targetStep current) <->
  RawCodedTermBoundPrefixRows M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold codedTermBoundPrefixRowsTermAt,
    RawCodedTermBoundPrefixRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite raw_sat_codedTermBoundTraversalRowTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** On represented term codes the source column is normalized to the index
    itself.  This is the crucial invariant that turns the numeric ordering
    of constructor codes into recursive table lookups. *)
Definition RawCodedTermBoundPrefixNormalized (M : RawPAModel)
    (supportCode supportStep sourceCode sourceStep
      targetCode targetStep current : M) : Prop :=
  forall index : M,
    rawLt M index current ->
    rawTermCodeSupported M supportCode supportStep index ->
    exists output : M,
      RawCodedTermOperationPairLookup M
        sourceCode sourceStep targetCode targetStep index index output.

Definition codedTermBoundPrefixNormalizedTermAt
    (supportCode supportStep sourceCode sourceStep
      targetCode targetStep current : term) : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 current))
      (pImp
        (termCodeSupportedTermAt
          (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
        (pEx
          (codedTermOperationPairLookupTermAt
            (liftTerm 2 sourceCode) (liftTerm 2 sourceStep)
            (liftTerm 2 targetCode) (liftTerm 2 targetStep)
            (tVar 1) (tVar 1) (tVar 0))))).

Lemma raw_sat_codedTermBoundPrefixNormalizedTermAt_iff : forall
    (M : RawPAModel) e supportCode supportStep sourceCode sourceStep
      targetCode targetStep current,
  raw_formula_sat M e
    (codedTermBoundPrefixNormalizedTermAt
      supportCode supportStep sourceCode sourceStep
      targetCode targetStep current) <->
  RawCodedTermBoundPrefixNormalized M
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold codedTermBoundPrefixNormalizedTermAt,
    RawCodedTermBoundPrefixNormalized.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_termCodeSupportedTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  repeat setoid_rewrite raw_shiftTotality_eval_liftTerm_one.
  repeat setoid_rewrite raw_shiftTotality_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition RawCodedTermBoundPrefix (M : RawPAModel)
    (supportCode supportStep sourceCode sourceStep
      targetCode targetStep current : M) : Prop :=
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep current /\
  RawCodedAssignmentDefinedThrough M targetCode targetStep current /\
  RawCodedTermBoundPrefixRows M
    sourceCode sourceStep targetCode targetStep current /\
  RawCodedTermBoundPrefixNormalized M
    supportCode supportStep sourceCode sourceStep
    targetCode targetStep current.

Definition codedTermBoundPrefixTermAt
    (supportCode supportStep sourceCode sourceStep
      targetCode targetStep current : term) : formula :=
  operationAnd4
    (codedAssignmentDefinedThroughTermAt sourceCode sourceStep current)
    (codedAssignmentDefinedThroughTermAt targetCode targetStep current)
    (codedTermBoundPrefixRowsTermAt
      sourceCode sourceStep targetCode targetStep current)
    (codedTermBoundPrefixNormalizedTermAt
      supportCode supportStep sourceCode sourceStep
      targetCode targetStep current).

Lemma raw_sat_codedTermBoundPrefixTermAt_iff : forall
    (M : RawPAModel) e supportCode supportStep sourceCode sourceStep
      targetCode targetStep current,
  raw_formula_sat M e
    (codedTermBoundPrefixTermAt supportCode supportStep
      sourceCode sourceStep targetCode targetStep current) <->
  RawCodedTermBoundPrefix M
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold codedTermBoundPrefixTermAt, RawCodedTermBoundPrefix,
    operationAnd4.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  rewrite raw_sat_codedTermBoundPrefixRowsTermAt_iff.
  rewrite raw_sat_codedTermBoundPrefixNormalizedTermAt_iff.
  reflexivity.
Qed.

Definition RawCodedTermBoundPrefixExists (M : RawPAModel)
    (supportCode supportStep current : M) : Prop :=
  exists sourceCode sourceStep targetCode targetStep : M,
    RawCodedTermBoundPrefix M supportCode supportStep
      sourceCode sourceStep targetCode targetStep current.

Definition codedTermBoundPrefixExistsTermAt
    (supportCode supportStep current : term) : formula :=
  operationEx4
    (codedTermBoundPrefixTermAt
      (liftTerm 4 supportCode) (liftTerm 4 supportStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)
      (liftTerm 4 current)).

Lemma raw_sat_codedTermBoundPrefixExistsTermAt_iff : forall
    (M : RawPAModel) e supportCode supportStep current,
  raw_formula_sat M e
    (codedTermBoundPrefixExistsTermAt supportCode supportStep current) <->
  RawCodedTermBoundPrefixExists M
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold codedTermBoundPrefixExistsTermAt,
    RawCodedTermBoundPrefixExists, operationEx4.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedTermBoundPrefixTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Prefix extension preserves every already closed term-bound row. *)
Lemma raw_termBoundTraversalRow_prefix_extend : forall
    (M : RawPAModel), RawPASatisfies M -> forall bound current
      oldSourceCode oldSourceStep oldTargetCode oldTargetStep
      newSourceCode newSourceStep newTargetCode newTargetStep input output,
  RawTermShiftTablePrefixExtension M bound
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    newSourceCode newSourceStep newTargetCode newTargetStep ->
  rawLe M current bound ->
  RawCodedTermBoundTraversalRow M
    oldSourceCode oldSourceStep oldTargetCode oldTargetStep
    current input output ->
  RawCodedTermBoundTraversalRow M
    newSourceCode newSourceStep newTargetCode newTargetStep
    current input output.
Proof.
  intros M hPA bound current oldSourceCode oldSourceStep
    oldTargetCode oldTargetStep newSourceCode newSourceStep
    newTargetCode newTargetStep input output hext hcurrent hrow.
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - left. exact hvar.
  - right. left. exact hzero.
  - right. right. left.
    destruct hsucc as
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
  - right. right. right. left.
    destruct hadd as
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
  - right. right. right. right.
    destruct hmul as
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
Qed.

Lemma raw_codedTermBoundPrefix_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall supportCode supportStep,
  RawCodedTermBoundPrefixExists M supportCode supportStep (raw_zero M).
Proof.
  intros M hPA supportCode supportStep.
  exists (raw_zero M), (raw_zero M), (raw_zero M), (raw_zero M).
  repeat split.
  - exact (raw_codedZeroAssignment_defined_all M hPA (raw_zero M)).
  - exact (raw_codedZeroAssignment_defined_all M hPA (raw_zero M)).
  - intros index input output hindex _.
    exfalso. exact (raw_not_lt_zero M hPA index hindex).
  - intros index hindex _.
    exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

(** One carrier successor appends either the represented constructor row or
    the default zero row.  No metatheoretic decoding is involved. *)
Theorem raw_codedTermBoundPrefix_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      limit supportCode supportStep current,
  RawTermSyntaxTraversal M limit supportCode supportStep ->
  rawLt M current limit ->
  RawCodedTermBoundPrefixExists M supportCode supportStep current ->
  RawCodedTermBoundPrefixExists M
    supportCode supportStep (raw_succ M current).
Proof.
  intros M hPA limit supportCode supportStep current
    [hsupportDefined hsyntaxRows] hcurrentLimit
    (sourceCode & sourceStep & targetCode & targetStep &
     hsourceDefined & htargetDefined & hrows & hnormalized).
  destruct (classic (rawTermCodeSupported M supportCode supportStep current))
    as [hsupported | hunsupported].
  - destruct (hsyntaxRows current hcurrentLimit hsupported)
      as (left & right & hshape).
    destruct hshape as
      [hvar | [hzero | [hsucc | [hadd | hmul]]]].
    + set (newOutput := raw_succ M left).
      assert (hclosed : RawCodedTermBoundTraversalRow M
          sourceCode sourceStep targetCode targetStep
          current current newOutput).
      { left. exists left. unfold newOutput. split;
          [exact hvar | reflexivity]. }
      destruct (raw_codedAssignmentAppend_defined_exists M hPA
        sourceCode sourceStep current current hsourceDefined)
        as (newSourceCode & newSourceStep & hnewSource & hsourcePrefix &
            hsourceRoot).
      destruct (raw_codedAssignmentAppend_defined_exists M hPA
        targetCode targetStep current newOutput htargetDefined)
        as (newTargetCode & newTargetStep & hnewTarget & htargetPrefix &
            htargetRoot).
      exists newSourceCode, newSourceStep, newTargetCode, newTargetStep.
      repeat split; try assumption.
      * intros index input output hindex hlookup.
        destruct (raw_lt_succ_cases M hPA index current hindex)
          as [hbefore | ->].
        -- destruct hlookup as [hinput houtput].
           destruct (hsourceDefined index hbefore) as [oldInput holdInput].
           destruct (htargetDefined index hbefore) as [oldOutput holdOutput].
           assert (hnewOld : RawCodedTermOperationPairLookup M
               newSourceCode newSourceStep newTargetCode newTargetStep
               index oldInput oldOutput).
           { split; [apply hsourcePrefix | apply htargetPrefix]; assumption. }
           assert (input = oldInput) as ->.
           { exact (raw_codedAssignmentLookup_functional M hPA
               newSourceCode newSourceStep index input oldInput
               hinput (proj1 hnewOld)). }
           assert (output = oldOutput) as ->.
           { exact (raw_codedAssignmentLookup_functional M hPA
               newTargetCode newTargetStep index output oldOutput
               houtput (proj2 hnewOld)). }
           apply (raw_termBoundTraversalRow_prefix_extend M hPA
             current index sourceCode sourceStep targetCode targetStep
             newSourceCode newSourceStep newTargetCode newTargetStep
             oldInput oldOutput (conj hsourcePrefix htargetPrefix)).
           ++ exact (raw_lt_to_le M index current hbefore).
           ++ apply hrows; [exact hbefore |]. split; assumption.
        -- destruct hlookup as [hinput houtput].
           assert (input = current) as ->.
           { exact (raw_codedAssignmentLookup_functional M hPA
               newSourceCode newSourceStep current input current
               hinput hsourceRoot). }
           assert (output = newOutput) as ->.
           { exact (raw_codedAssignmentLookup_functional M hPA
               newTargetCode newTargetStep current output newOutput
               houtput htargetRoot). }
           apply (raw_termBoundTraversalRow_prefix_extend M hPA
             current current sourceCode sourceStep targetCode targetStep
             newSourceCode newSourceStep newTargetCode newTargetStep
             current newOutput (conj hsourcePrefix htargetPrefix)).
           ++ exact (raw_rank_le_refl M hPA current).
           ++ exact hclosed.
      * intros index hindex hindexSupported.
        destruct (raw_lt_succ_cases M hPA index current hindex)
          as [hbefore | ->].
        -- destruct (hnormalized index hbefore hindexSupported)
             as [oldOutput hold].
           exists oldOutput. destruct hold as [holdSource holdTarget].
           split; [apply hsourcePrefix | apply htargetPrefix]; assumption.
        -- exists newOutput. split; assumption.
    + set (newOutput := raw_zero M).
      assert (hclosed : RawCodedTermBoundTraversalRow M
          sourceCode sourceStep targetCode targetStep
          current current newOutput).
      { right. left. unfold newOutput. split;
          [exact hzero | reflexivity]. }
      (* The remaining constructor branches share the same append proof;
         [all: ...] below runs it after constructing [hclosed]. *)
      destruct (raw_codedAssignmentAppend_defined_exists M hPA
        sourceCode sourceStep current current hsourceDefined)
        as (newSourceCode & newSourceStep & hnewSource & hsourcePrefix &
            hsourceRoot).
      destruct (raw_codedAssignmentAppend_defined_exists M hPA
        targetCode targetStep current newOutput htargetDefined)
        as (newTargetCode & newTargetStep & hnewTarget & htargetPrefix &
            htargetRoot).
      exists newSourceCode, newSourceStep, newTargetCode, newTargetStep.
      repeat split; try assumption.
      * intros index input output hindex hlookup.
        destruct (raw_lt_succ_cases M hPA index current hindex)
          as [hbefore | ->].
        -- destruct hlookup as [hinput houtput].
           destruct (hsourceDefined index hbefore) as [oldInput holdInput].
           destruct (htargetDefined index hbefore) as [oldOutput holdOutput].
           assert (hnewOld : RawCodedTermOperationPairLookup M
               newSourceCode newSourceStep newTargetCode newTargetStep
               index oldInput oldOutput).
           { split; [apply hsourcePrefix | apply htargetPrefix]; assumption. }
           assert (input = oldInput) as ->.
           { exact (raw_codedAssignmentLookup_functional M hPA
               newSourceCode newSourceStep index input oldInput
               hinput (proj1 hnewOld)). }
           assert (output = oldOutput) as ->.
           { exact (raw_codedAssignmentLookup_functional M hPA
               newTargetCode newTargetStep index output oldOutput
               houtput (proj2 hnewOld)). }
           apply (raw_termBoundTraversalRow_prefix_extend M hPA
             current index sourceCode sourceStep targetCode targetStep
             newSourceCode newSourceStep newTargetCode newTargetStep
             oldInput oldOutput (conj hsourcePrefix htargetPrefix));
             [exact (raw_lt_to_le M index current hbefore) |
              apply hrows; [exact hbefore |]; split; assumption].
        -- destruct hlookup as [hinput houtput].
           assert (input = current) as ->.
           { exact (raw_codedAssignmentLookup_functional M hPA
               newSourceCode newSourceStep current input current
               hinput hsourceRoot). }
           assert (output = newOutput) as ->.
           { exact (raw_codedAssignmentLookup_functional M hPA
               newTargetCode newTargetStep current output newOutput
               houtput htargetRoot). }
           apply (raw_termBoundTraversalRow_prefix_extend M hPA
             current current sourceCode sourceStep targetCode targetStep
             newSourceCode newSourceStep newTargetCode newTargetStep
             current newOutput (conj hsourcePrefix htargetPrefix));
             [exact (raw_rank_le_refl M hPA current) | exact hclosed].
      * intros index hindex hindexSupported.
        destruct (raw_lt_succ_cases M hPA index current hindex)
          as [hbefore | ->].
        -- destruct (hnormalized index hbefore hindexSupported)
             as [oldOutput [holdSource holdTarget]].
           exists oldOutput. split;
             [apply hsourcePrefix | apply htargetPrefix]; assumption.
        -- exists newOutput. split; assumption.
    + destruct hsucc as [hcode [hleftSupported hleft]]. subst current.
      destruct (hnormalized left hleft hleftSupported)
        as [childBound hchildLookup].
      set (newOutput := childBound).
      assert (hclosed : RawCodedTermBoundTraversalRow M
          sourceCode sourceStep targetCode targetStep
          (rawTermSuccCode M left) (rawTermSuccCode M left) newOutput).
      { right. right. left. exists left, left, childBound.
        split; [exact hleft |]. split; [exact hchildLookup |].
        unfold newOutput. split; reflexivity. }
      (* Re-enter the common append proof through the local helper below. *)
      set (rowCode := rawTermSuccCode M left).
      destruct (raw_codedAssignmentAppend_defined_exists M hPA
        sourceCode sourceStep rowCode rowCode hsourceDefined)
        as (newSourceCode & newSourceStep & hnewSource & hsourcePrefix &
            hsourceRoot).
      destruct (raw_codedAssignmentAppend_defined_exists M hPA
        targetCode targetStep rowCode newOutput htargetDefined)
        as (newTargetCode & newTargetStep & hnewTarget & htargetPrefix &
            htargetRoot).
      exists newSourceCode, newSourceStep, newTargetCode, newTargetStep.
      repeat split; try assumption.
      * intros index input output hindex hlookup.
        destruct (raw_lt_succ_cases M hPA index rowCode hindex)
          as [hbefore | ->].
        -- destruct hlookup as [hinput houtput].
           destruct (hsourceDefined index hbefore) as [oldInput holdInput].
           destruct (htargetDefined index hbefore) as [oldOutput holdOutput].
           assert (hnewOld : RawCodedTermOperationPairLookup M
               newSourceCode newSourceStep newTargetCode newTargetStep
               index oldInput oldOutput).
           { split; [apply hsourcePrefix | apply htargetPrefix]; assumption. }
           assert (input = oldInput) as -> by
             (eapply raw_codedAssignmentLookup_functional;
              [exact hPA | exact hinput | exact (proj1 hnewOld)]).
           assert (output = oldOutput) as -> by
             (eapply raw_codedAssignmentLookup_functional;
              [exact hPA | exact houtput | exact (proj2 hnewOld)]).
           apply (raw_termBoundTraversalRow_prefix_extend M hPA
             rowCode index sourceCode sourceStep targetCode targetStep
             newSourceCode newSourceStep newTargetCode newTargetStep
             oldInput oldOutput (conj hsourcePrefix htargetPrefix));
             [exact (raw_lt_to_le M index rowCode hbefore) |
              apply hrows; [exact hbefore |]; split; assumption].
        -- destruct hlookup as [hinput houtput].
           assert (input = rowCode) as -> by
             (eapply raw_codedAssignmentLookup_functional;
              [exact hPA | exact hinput | exact hsourceRoot]).
           assert (output = newOutput) as -> by
             (eapply raw_codedAssignmentLookup_functional;
              [exact hPA | exact houtput | exact htargetRoot]).
           apply (raw_termBoundTraversalRow_prefix_extend M hPA
             rowCode rowCode sourceCode sourceStep targetCode targetStep
             newSourceCode newSourceStep newTargetCode newTargetStep
             rowCode newOutput (conj hsourcePrefix htargetPrefix));
             [exact (raw_rank_le_refl M hPA rowCode) | exact hclosed].
      * intros index hindex hindexSupported.
        destruct (raw_lt_succ_cases M hPA index rowCode hindex)
          as [hbefore | ->].
        -- destruct (hnormalized index hbefore hindexSupported)
             as [oldOutput [holdSource holdTarget]].
           exists oldOutput. split;
             [apply hsourcePrefix | apply htargetPrefix]; assumption.
        -- exists newOutput. split; assumption.
    + destruct hadd as
        [hcode [hleftSupported [hrightSupported [hleft hright]]]].
      subst current.
      destruct (hnormalized left hleft hleftSupported)
        as [leftBound hleftLookup].
      destruct (hnormalized right hright hrightSupported)
        as [rightBound hrightLookup].
      set (newOutput := raw_add M leftBound rightBound).
      assert (hclosed : RawCodedTermBoundTraversalRow M
          sourceCode sourceStep targetCode targetStep
          (rawTermAddCode M left right) (rawTermAddCode M left right)
          newOutput).
      { right. right. right. left.
        exists left, left, leftBound, right, right, rightBound.
        split; [exact hleft |]. split; [exact hleftLookup |].
        split; [exact hright |]. split; [exact hrightLookup |].
        unfold newOutput. split; reflexivity. }
      set (rowCode := rawTermAddCode M left right).
      destruct (raw_codedAssignmentAppend_defined_exists M hPA
        sourceCode sourceStep rowCode rowCode hsourceDefined)
        as (newSourceCode & newSourceStep & hnewSource & hsourcePrefix &
            hsourceRoot).
      destruct (raw_codedAssignmentAppend_defined_exists M hPA
        targetCode targetStep rowCode newOutput htargetDefined)
        as (newTargetCode & newTargetStep & hnewTarget & htargetPrefix &
            htargetRoot).
      exists newSourceCode, newSourceStep, newTargetCode, newTargetStep.
      repeat split; try assumption.
      * intros index input output hindex [hinput houtput].
        destruct (raw_lt_succ_cases M hPA index rowCode hindex)
          as [hbefore | ->].
        -- destruct (hsourceDefined index hbefore) as [oldInput holdInput].
           destruct (htargetDefined index hbefore) as [oldOutput holdOutput].
           assert (hnewOld : RawCodedTermOperationPairLookup M
               newSourceCode newSourceStep newTargetCode newTargetStep
               index oldInput oldOutput).
           { split; [apply hsourcePrefix | apply htargetPrefix]; assumption. }
           assert (input = oldInput) as -> by
             (eapply raw_codedAssignmentLookup_functional;
              [exact hPA | exact hinput | exact (proj1 hnewOld)]).
           assert (output = oldOutput) as -> by
             (eapply raw_codedAssignmentLookup_functional;
              [exact hPA | exact houtput | exact (proj2 hnewOld)]).
           apply (raw_termBoundTraversalRow_prefix_extend M hPA
             rowCode index sourceCode sourceStep targetCode targetStep
             newSourceCode newSourceStep newTargetCode newTargetStep
             oldInput oldOutput (conj hsourcePrefix htargetPrefix));
             [exact (raw_lt_to_le M index rowCode hbefore) |
              apply hrows; [exact hbefore |]; split; assumption].
        -- assert (input = rowCode) as -> by
             (eapply raw_codedAssignmentLookup_functional;
              [exact hPA | exact hinput | exact hsourceRoot]).
           assert (output = newOutput) as -> by
             (eapply raw_codedAssignmentLookup_functional;
              [exact hPA | exact houtput | exact htargetRoot]).
           apply (raw_termBoundTraversalRow_prefix_extend M hPA
             rowCode rowCode sourceCode sourceStep targetCode targetStep
             newSourceCode newSourceStep newTargetCode newTargetStep
             rowCode newOutput (conj hsourcePrefix htargetPrefix));
             [exact (raw_rank_le_refl M hPA rowCode) | exact hclosed].
      * intros index hindex hindexSupported.
        destruct (raw_lt_succ_cases M hPA index rowCode hindex)
          as [hbefore | ->].
        -- destruct (hnormalized index hbefore hindexSupported)
             as [oldOutput [holdSource holdTarget]].
           exists oldOutput. split;
             [apply hsourcePrefix | apply htargetPrefix]; assumption.
        -- exists newOutput. split; assumption.
    + destruct hmul as
        [hcode [hleftSupported [hrightSupported [hleft hright]]]].
      subst current.
      destruct (hnormalized left hleft hleftSupported)
        as [leftBound hleftLookup].
      destruct (hnormalized right hright hrightSupported)
        as [rightBound hrightLookup].
      set (newOutput := raw_add M leftBound rightBound).
      assert (hclosed : RawCodedTermBoundTraversalRow M
          sourceCode sourceStep targetCode targetStep
          (rawTermMulCode M left right) (rawTermMulCode M left right)
          newOutput).
      { right. right. right. right.
        exists left, left, leftBound, right, right, rightBound.
        split; [exact hleft |]. split; [exact hleftLookup |].
        split; [exact hright |]. split; [exact hrightLookup |].
        unfold newOutput. split; reflexivity. }
      set (rowCode := rawTermMulCode M left right).
      destruct (raw_codedAssignmentAppend_defined_exists M hPA
        sourceCode sourceStep rowCode rowCode hsourceDefined)
        as (newSourceCode & newSourceStep & hnewSource & hsourcePrefix &
            hsourceRoot).
      destruct (raw_codedAssignmentAppend_defined_exists M hPA
        targetCode targetStep rowCode newOutput htargetDefined)
        as (newTargetCode & newTargetStep & hnewTarget & htargetPrefix &
            htargetRoot).
      exists newSourceCode, newSourceStep, newTargetCode, newTargetStep.
      repeat split; try assumption.
      * intros index input output hindex [hinput houtput].
        destruct (raw_lt_succ_cases M hPA index rowCode hindex)
          as [hbefore | ->].
        -- destruct (hsourceDefined index hbefore) as [oldInput holdInput].
           destruct (htargetDefined index hbefore) as [oldOutput holdOutput].
           assert (hnewOld : RawCodedTermOperationPairLookup M
               newSourceCode newSourceStep newTargetCode newTargetStep
               index oldInput oldOutput).
           { split; [apply hsourcePrefix | apply htargetPrefix]; assumption. }
           assert (input = oldInput) as -> by
             (eapply raw_codedAssignmentLookup_functional;
              [exact hPA | exact hinput | exact (proj1 hnewOld)]).
           assert (output = oldOutput) as -> by
             (eapply raw_codedAssignmentLookup_functional;
              [exact hPA | exact houtput | exact (proj2 hnewOld)]).
           apply (raw_termBoundTraversalRow_prefix_extend M hPA
             rowCode index sourceCode sourceStep targetCode targetStep
             newSourceCode newSourceStep newTargetCode newTargetStep
             oldInput oldOutput (conj hsourcePrefix htargetPrefix));
             [exact (raw_lt_to_le M index rowCode hbefore) |
              apply hrows; [exact hbefore |]; split; assumption].
        -- assert (input = rowCode) as -> by
             (eapply raw_codedAssignmentLookup_functional;
              [exact hPA | exact hinput | exact hsourceRoot]).
           assert (output = newOutput) as -> by
             (eapply raw_codedAssignmentLookup_functional;
              [exact hPA | exact houtput | exact htargetRoot]).
           apply (raw_termBoundTraversalRow_prefix_extend M hPA
             rowCode rowCode sourceCode sourceStep targetCode targetStep
             newSourceCode newSourceStep newTargetCode newTargetStep
             rowCode newOutput (conj hsourcePrefix htargetPrefix));
             [exact (raw_rank_le_refl M hPA rowCode) | exact hclosed].
      * intros index hindex hindexSupported.
        destruct (raw_lt_succ_cases M hPA index rowCode hindex)
          as [hbefore | ->].
        -- destruct (hnormalized index hbefore hindexSupported)
             as [oldOutput [holdSource holdTarget]].
           exists oldOutput. split;
             [apply hsourcePrefix | apply htargetPrefix]; assumption.
        -- exists newOutput. split; assumption.
  - (* Unsupported carrier codes receive the harmless zero-term row. *)
    set (newInput := rawTermZeroCode M).
    set (newOutput := raw_zero M).
    assert (hclosed : RawCodedTermBoundTraversalRow M
        sourceCode sourceStep targetCode targetStep
        current newInput newOutput).
    { right. left. unfold newInput, newOutput. split; reflexivity. }
    destruct (raw_codedAssignmentAppend_defined_exists M hPA
      sourceCode sourceStep current newInput hsourceDefined)
      as (newSourceCode & newSourceStep & hnewSource & hsourcePrefix &
          hsourceRoot).
    destruct (raw_codedAssignmentAppend_defined_exists M hPA
      targetCode targetStep current newOutput htargetDefined)
      as (newTargetCode & newTargetStep & hnewTarget & htargetPrefix &
          htargetRoot).
    exists newSourceCode, newSourceStep, newTargetCode, newTargetStep.
    repeat split; try assumption.
    + intros index input output hindex [hinput houtput].
      destruct (raw_lt_succ_cases M hPA index current hindex)
        as [hbefore | ->].
      * destruct (hsourceDefined index hbefore) as [oldInput holdInput].
        destruct (htargetDefined index hbefore) as [oldOutput holdOutput].
        assert (hnewOld : RawCodedTermOperationPairLookup M
            newSourceCode newSourceStep newTargetCode newTargetStep
            index oldInput oldOutput).
        { split; [apply hsourcePrefix | apply htargetPrefix]; assumption. }
        assert (input = oldInput) as -> by
          (eapply raw_codedAssignmentLookup_functional;
           [exact hPA | exact hinput | exact (proj1 hnewOld)]).
        assert (output = oldOutput) as -> by
          (eapply raw_codedAssignmentLookup_functional;
           [exact hPA | exact houtput | exact (proj2 hnewOld)]).
        apply (raw_termBoundTraversalRow_prefix_extend M hPA
          current index sourceCode sourceStep targetCode targetStep
          newSourceCode newSourceStep newTargetCode newTargetStep
          oldInput oldOutput (conj hsourcePrefix htargetPrefix));
          [exact (raw_lt_to_le M index current hbefore) |
           apply hrows; [exact hbefore |]; split; assumption].
      * assert (input = newInput) as -> by
          (eapply raw_codedAssignmentLookup_functional;
           [exact hPA | exact hinput | exact hsourceRoot]).
        assert (output = newOutput) as -> by
          (eapply raw_codedAssignmentLookup_functional;
           [exact hPA | exact houtput | exact htargetRoot]).
        apply (raw_termBoundTraversalRow_prefix_extend M hPA
          current current sourceCode sourceStep targetCode targetStep
          newSourceCode newSourceStep newTargetCode newTargetStep
          newInput newOutput (conj hsourcePrefix htargetPrefix));
          [exact (raw_rank_le_refl M hPA current) | exact hclosed].
    + intros index hindex hindexSupported.
      destruct (raw_lt_succ_cases M hPA index current hindex)
        as [hbefore | ->].
      * destruct (hnormalized index hbefore hindexSupported)
          as [oldOutput [holdSource holdTarget]].
        exists oldOutput. split;
          [apply hsourcePrefix | apply htargetPrefix]; assumption.
      * exfalso. exact (hunsupported hindexSupported).
Qed.

Definition RawCodedTermBoundPrefixWithin (M : RawPAModel)
    (limit supportCode supportStep current : M) : Prop :=
  rawLe M current limit ->
  RawCodedTermBoundPrefixExists M supportCode supportStep current.

Definition codedTermBoundPrefixWithinTermAt
    (limit supportCode supportStep current : term) : formula :=
  pImp (Formula.leTermAt current limit)
    (codedTermBoundPrefixExistsTermAt supportCode supportStep current).

Lemma raw_sat_codedTermBoundPrefixWithinTermAt_iff : forall
    (M : RawPAModel) e limit supportCode supportStep current,
  raw_formula_sat M e
    (codedTermBoundPrefixWithinTermAt
      limit supportCode supportStep current) <->
  RawCodedTermBoundPrefixWithin M
    (raw_term_eval M e limit)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold codedTermBoundPrefixWithinTermAt,
    RawCodedTermBoundPrefixWithin.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank.
  rewrite raw_sat_codedTermBoundPrefixExistsTermAt_iff.
  reflexivity.
Qed.

Theorem raw_codedTermBoundPrefixWithin_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      limit supportCode supportStep,
  RawTermSyntaxTraversal M limit supportCode supportStep ->
  forall current,
    RawCodedTermBoundPrefixWithin M
      limit supportCode supportStep current.
Proof.
  intros M hPA limit supportCode supportStep hsyntax.
  set (parameterEnv := scons M limit
    (scons M supportCode (scons M supportStep
      (fun _ : nat => raw_zero M)))).
  set (phi := codedTermBoundPrefixWithinTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_codedTermBoundPrefixWithinTermAt_iff M
        (scons M (raw_zero M) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons]. intros _.
      exact (raw_codedTermBoundPrefix_zero M hPA supportCode supportStep).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedTermBoundPrefixWithinTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 0)) hcurrentSat)
        as hcurrent.
      apply (proj2
        (raw_sat_codedTermBoundPrefixWithinTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      intro hsuccLimit.
      assert (hcurrentLimit : rawLt M current limit).
      { exact (raw_rank_lt_of_succ_le M hPA current limit hsuccLimit). }
      apply (raw_codedTermBoundPrefix_succ M hPA
        limit supportCode supportStep current hsyntax hcurrentLimit).
      apply hcurrent. exact (raw_lt_to_le M current limit hcurrentLimit).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedTermBoundPrefixWithinTermAt_iff M
      (scons M current parameterEnv)
      (tVar 1) (tVar 2) (tVar 3) (tVar 0)) (hall current)) as hraw.
  unfold parameterEnv in hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

Theorem raw_codedTermBound_exists_of_syntax_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      input assignmentCode assignmentStep,
  RawTermSyntaxRealizable M input assignmentCode assignmentStep ->
  exists output : M, RawCodedTermBound M input output.
Proof.
  intros M hPA input assignmentCode assignmentStep
    (supportCode & supportStep & hsyntax & _ & hrootSupported).
  pose proof (raw_codedTermBoundPrefixWithin_all M hPA
    (raw_succ M input) supportCode supportStep hsyntax
    (raw_succ M input)) as hprefixExists.
  specialize (hprefixExists
    (raw_rank_le_refl M hPA (raw_succ M input))).
  destruct hprefixExists as
    (sourceCode & sourceStep & targetCode & targetStep &
     hsource & htarget & hrows & hnormalized).
  destruct (hnormalized input
    (raw_assignment_lt_self_succ M hPA input) hrootSupported)
    as [output hroot].
  exists output, sourceCode, sourceStep, targetCode, targetStep.
  split; [exact hsource |]. split; [exact htarget |].
  split; [exact hroot |]. exact hrows.
Qed.

End PABoundedRawCodedFormulaBoundAllCarrierTotality.
