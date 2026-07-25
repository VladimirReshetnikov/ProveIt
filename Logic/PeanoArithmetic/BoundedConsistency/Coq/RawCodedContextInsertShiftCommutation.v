(**
  Commutation of context insertion with unit de Bruijn shift.

  A proof constructor below a binder needs the square

<<
       source  -- insert head at depth -->  target
         |                                   |
       shift                               shift
         |                                   |
         v                                   v
    shiftedSource -- insert shiftedHead --> shiftedTarget
>>

  for carrier-valued depths and possibly nonstandard context lengths.  The
  proof therefore cannot recurse in Rocq over either number.  We first prove
  exact semantic inversions by dropping the first row of beta-coded context
  tables.  The final depth induction is then performed by PA's represented
  induction theorem.

  [RawCodedAssignmentShiftTailThrough] is intentionally one-directional.
  Whenever an inversion starts from a lookup in the new table, we recover the
  corresponding old lookup from traversal definedness and use beta
  functionality to identify the values.  This avoids adding an unjustified
  inverse axiom for arbitrary, unconstrained table suffixes.
*)

From Stdlib Require Import List Arith Lia Classical_Prop.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAdditionLaws PolynomialPairInjectivity
  RawCodedSyntaxConstructors RawCodedSyntaxConstructorSeparation
  RawCodedAssignment RawCodedAssignmentShiftTail RawCodedProofDescent
  RawCodedFormulaOperations RawCodedContextLists RawCodedContextStructure
  RawCodedContextFunctionality RawCodedContextShift RawCodedContextInsert.

Import ListNotations.

Module PABoundedRawCodedContextInsertShiftCommutation.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAdditionLaws.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentShiftTail.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextFunctionality.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedContextInsert.

(** Strict order is preserved by successor.  The repository already has
    the converse direction; this short forward form is convenient when a
    dropped table row changes index [k] into [S k]. *)
Lemma raw_contextInsertShift_succ_lt_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  rawLt M left right ->
  rawLt M (raw_succ M left) (raw_succ M right).
Proof.
  intros M hPA left right hlt.
  apply raw_lt_succ_of_le; [exact hPA |].
  exact (raw_succ_le_of_lt_pair M hPA left right hlt).
Qed.

(** Drop row zero from a complete traversal whose length is a successor.
    Both synchronized beta tables are shifted by the PAHF tail theorem.  The
    returned lookup of the old head at zero is retained for the surrounding
    shift/insertion rule. *)
Lemma raw_contextListTraversal_succ_tail_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      root bound tailCode tailStep headCode headStep,
  RawContextListTraversal M root (raw_succ M bound)
    tailCode tailStep headCode headStep ->
  exists head tail newTailCode newTailStep newHeadCode newHeadStep : M,
    root = rawListNode M head tail /\
    RawCodedAssignmentLookup M headCode headStep (raw_zero M) head /\
    RawCodedAssignmentShiftTailThrough M
      tailCode tailStep newTailCode newTailStep bound /\
    RawCodedAssignmentShiftTailThrough M
      headCode headStep newHeadCode newHeadStep bound /\
    RawContextListTraversal M tail bound
      newTailCode newTailStep newHeadCode newHeadStep.
Proof.
  intros M hPA root bound tailCode tailStep headCode headStep
    htraversal.
  destruct htraversal as [hroot [hend [hheadDefined hrows]]].
  assert (hzeroLive : rawLt M (raw_zero M) (raw_succ M bound)).
  { exact (raw_lt_zero_succ M hPA bound). }
  destruct (hrows (raw_zero M) hzeroLive) as
    (current & tail & head & hcurrent & htail & hhead & hnode).
  assert (hcurrentRoot : current = root).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      tailCode tailStep (raw_zero M) current root hcurrent hroot).
  }
  subst current.
  destruct (raw_codedAssignmentShiftTail_exists M hPA
    tailCode tailStep bound) as
    (newTailCode & newTailStep & htailShift).
  destruct (raw_codedAssignmentShiftTail_exists M hPA
    headCode headStep bound) as
    (newHeadCode & newHeadStep & hheadShift).
  exists head, tail, newTailCode, newTailStep,
    newHeadCode, newHeadStep.
  split; [symmetry; exact hcurrentRoot |].
  split; [exact hhead |].
  split; [exact htailShift |].
  split; [exact hheadShift |].
  repeat split.
  - exact (htailShift (raw_zero M)
      (raw_proof_zero_le M hPA bound) tail htail).
  - apply (htailShift bound (raw_context_le_refl M hPA bound)
      (raw_zero M)).
    exact hend.
  - intros index hindex.
    assert (hsuccIndex : rawLt M (raw_succ M index)
        (raw_succ M bound)).
    {
      exact (raw_contextInsertShift_succ_lt_succ M hPA
        index bound hindex).
    }
    destruct (hheadDefined (raw_succ M index) hsuccIndex)
      as [value hvalue].
    exists value.
    exact (hheadShift index (raw_lt_to_le M index bound hindex)
      value hvalue).
  - intros index hindex.
    assert (hsuccIndex : rawLt M (raw_succ M index)
        (raw_succ M bound)).
    {
      exact (raw_contextInsertShift_succ_lt_succ M hPA
        index bound hindex).
    }
    destruct (hrows (raw_succ M index) hsuccIndex) as
      (oldCurrent & oldNext & oldHead &
        holdCurrent & holdNext & holdHead & holdNode).
    exists oldCurrent, oldNext, oldHead.
    repeat split; try assumption.
    + exact (htailShift index
        (raw_lt_to_le M index bound hindex)
        oldCurrent holdCurrent).
    + exact (htailShift (raw_succ M index)
        (raw_succ_le_of_lt_pair M hPA index bound hindex)
        oldNext holdNext).
    + exact (hheadShift index
        (raw_lt_to_le M index bound hindex)
        oldHead holdHead).
Qed.

(** Invert a context shift whose source is visibly a cons.  The target is
    forced to have a first row as well, and dropping row zero from both
    traversals gives the shift relation between their tails. *)
Lemma raw_contextShift_cons_invert : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      sourceHead sourceTail shiftedRoot,
  RawContextShift M
    (rawListNode M sourceHead sourceTail) shiftedRoot ->
  exists shiftedHead shiftedTail : M,
    shiftedRoot = rawListNode M shiftedHead shiftedTail /\
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      sourceHead shiftedHead /\
    RawContextShift M sourceTail shiftedTail.
Proof.
  intros M hPA sourceHead sourceTail shiftedRoot
    (bound & sourceTailCode & sourceTailStep & sourceHeadCode &
      sourceHeadStep & targetTailCode & targetTailStep &
      targetHeadCode & targetHeadStep &
      [hsourceTraversal [htargetTraversal hrows]]).
  destruct (raw_assignment_zero_or_successor M hPA bound)
    as [-> | [predecessor ->]].
  - pose proof hsourceTraversal as hsourceFacts.
    destruct hsourceFacts as [hroot [hend _]].
    assert (hnodeZero :
        rawListNode M sourceHead sourceTail = raw_zero M).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        sourceTailCode sourceTailStep (raw_zero M)
        (rawListNode M sourceHead sourceTail) (raw_zero M)
        hroot hend).
    }
    exfalso.
    exact (raw_context_zero_neq_listNode M hPA
      sourceHead sourceTail (eq_sym hnodeZero)).
  - destruct (raw_contextListTraversal_succ_tail_exists M hPA
      (rawListNode M sourceHead sourceTail) predecessor
      sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
      hsourceTraversal) as
      (rowSourceHead & rowSourceTail &
        newSourceTailCode & newSourceTailStep &
        newSourceHeadCode & newSourceHeadStep &
        hsourceRoot & hsourceHeadZero &
        hsourceTailShift & hsourceHeadShift & hsourceTailTraversal).
    destruct (rawListNode_injective M hPA
      sourceHead sourceTail rowSourceHead rowSourceTail hsourceRoot)
      as [hsourceHeadEq hsourceTailEq].
    subst rowSourceHead. subst rowSourceTail.
    destruct (raw_contextListTraversal_succ_tail_exists M hPA
      shiftedRoot predecessor
      targetTailCode targetTailStep targetHeadCode targetHeadStep
      htargetTraversal) as
      (shiftedHead & shiftedTail &
        newTargetTailCode & newTargetTailStep &
        newTargetHeadCode & newTargetHeadStep &
        htargetRoot & htargetHeadZero &
        htargetTailShift & htargetHeadShift & htargetTailTraversal).
    assert (hheadFormulaShift : RawCodedFormulaShift M
        (raw_zero M) (rawNumeralValue M 1)
        sourceHead shiftedHead).
    {
      exact (hrows (raw_zero M)
        (raw_lt_zero_succ M hPA predecessor)
        sourceHead shiftedHead hsourceHeadZero htargetHeadZero).
    }
    exists shiftedHead, shiftedTail.
    split; [exact htargetRoot |].
    split; [exact hheadFormulaShift |].
    exists predecessor,
      newSourceTailCode, newSourceTailStep,
      newSourceHeadCode, newSourceHeadStep,
      newTargetTailCode, newTargetTailStep,
      newTargetHeadCode, newTargetHeadStep.
    split; [exact hsourceTailTraversal |].
    split; [exact htargetTailTraversal |].
    intros index hindex sourceFormula targetFormula
      hsourceNew htargetNew.
    assert (hsuccIndex : rawLt M (raw_succ M index)
        (raw_succ M predecessor)).
    {
      exact (raw_contextInsertShift_succ_lt_succ M hPA
        index predecessor hindex).
    }
    destruct ((proj1 (proj2 (proj2 hsourceTraversal)))
      (raw_succ M index) hsuccIndex)
      as [oldSourceFormula hsourceOld].
    destruct ((proj1 (proj2 (proj2 htargetTraversal)))
      (raw_succ M index) hsuccIndex)
      as [oldTargetFormula htargetOld].
    assert (hsourceMapped : RawCodedAssignmentLookup M
        newSourceHeadCode newSourceHeadStep index oldSourceFormula).
    {
      exact (hsourceHeadShift index
        (raw_lt_to_le M index predecessor hindex)
        oldSourceFormula hsourceOld).
    }
    assert (htargetMapped : RawCodedAssignmentLookup M
        newTargetHeadCode newTargetHeadStep index oldTargetFormula).
    {
      exact (htargetHeadShift index
        (raw_lt_to_le M index predecessor hindex)
        oldTargetFormula htargetOld).
    }
    assert (hsourceEq : sourceFormula = oldSourceFormula).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        newSourceHeadCode newSourceHeadStep index
        sourceFormula oldSourceFormula hsourceNew hsourceMapped).
    }
    assert (htargetEq : targetFormula = oldTargetFormula).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        newTargetHeadCode newTargetHeadStep index
        targetFormula oldTargetFormula htargetNew htargetMapped).
    }
    rewrite hsourceEq, htargetEq.
    exact (hrows (raw_succ M index) hsuccIndex
      oldSourceFormula oldTargetFormula hsourceOld htargetOld).
Qed.

(** Successor-depth insertion exposes the same leading formula on source
    and target.  Dropping that common row decrements the carrier-valued depth
    and produces another complete insertion certificate. *)
Lemma raw_contextInsertAt_succ_invert : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      head depth source target,
  RawContextInsertAt M head (raw_succ M depth) source target ->
  exists extra sourceTail targetTail : M,
    source = rawListNode M extra sourceTail /\
    target = rawListNode M extra targetTail /\
    RawContextInsertAt M head depth sourceTail targetTail.
Proof.
  intros M hPA head depth source target
    (bound & sourceTailCode & sourceTailStep & sourceHeadCode &
      sourceHeadStep & targetTailCode & targetTailStep &
      targetHeadCode & targetHeadStep &
      [hsourceTraversal [htargetTraversal
        [hdepth [hlow [hheadRow hhigh]]]]]).
  assert (hdepthBelow : rawLt M depth bound).
  {
    exact (raw_lt_succ_succ_inv M hPA depth bound hdepth).
  }
  destruct (raw_assignment_zero_or_successor M hPA bound)
    as [-> | [predecessor ->]].
  - exfalso. exact (raw_not_lt_zero M hPA depth hdepthBelow).
  - destruct (raw_contextListTraversal_succ_tail_exists M hPA
      source predecessor
      sourceTailCode sourceTailStep sourceHeadCode sourceHeadStep
      hsourceTraversal) as
      (sourceFirst & sourceTail &
        newSourceTailCode & newSourceTailStep &
        newSourceHeadCode & newSourceHeadStep &
        hsourceRoot & hsourceHeadZero &
        hsourceTailShift & hsourceHeadShift & hsourceTailTraversal).
    destruct (raw_contextListTraversal_succ_tail_exists M hPA
      target (raw_succ M predecessor)
      targetTailCode targetTailStep targetHeadCode targetHeadStep
      htargetTraversal) as
      (targetFirst & targetTail &
        newTargetTailCode & newTargetTailStep &
        newTargetHeadCode & newTargetHeadStep &
        htargetRoot & htargetHeadZero &
        htargetTailShift & htargetHeadShift & htargetTailTraversal).
    assert (hfirstEq : targetFirst = sourceFirst).
    {
      exact (hlow (raw_zero M) (raw_lt_zero_succ M hPA depth)
        sourceFirst hsourceHeadZero targetFirst htargetHeadZero).
    }
    exists sourceFirst, sourceTail, targetTail.
    split; [exact hsourceRoot |].
    split.
    + rewrite <- hfirstEq. exact htargetRoot.
    + exists predecessor,
        newSourceTailCode, newSourceTailStep,
        newSourceHeadCode, newSourceHeadStep,
        newTargetTailCode, newTargetTailStep,
        newTargetHeadCode, newTargetHeadStep.
      split; [exact hsourceTailTraversal |].
      split; [exact htargetTailTraversal |].
      split; [exact hdepthBelow |].
      split.
      * intros index hindex sourceFormula hsourceNew
          targetFormula htargetNew.
        assert (hindexPred : rawLt M index predecessor).
        {
          exact (raw_lt_of_lt_of_lt_succ M hPA
            index depth predecessor hindex hdepthBelow).
        }
        assert (hsuccIndexPred : rawLt M (raw_succ M index)
            (raw_succ M predecessor)).
        {
          exact (raw_contextInsertShift_succ_lt_succ M hPA
            index predecessor hindexPred).
        }
        assert (hsuccIndexTarget : rawLt M (raw_succ M index)
            (raw_succ M (raw_succ M predecessor))).
        {
          exact (raw_assignment_lt_trans M hPA
            (raw_succ M index) (raw_succ M predecessor)
            (raw_succ M (raw_succ M predecessor))
            hsuccIndexPred
            (raw_assignment_lt_self_succ M hPA
              (raw_succ M predecessor))).
        }
        destruct ((proj1 (proj2 (proj2 hsourceTraversal)))
          (raw_succ M index) hsuccIndexPred)
          as [oldSourceFormula hsourceOld].
        destruct ((proj1 (proj2 (proj2 htargetTraversal)))
          (raw_succ M index) hsuccIndexTarget)
          as [oldTargetFormula htargetOld].
        assert (hsourceMapped : RawCodedAssignmentLookup M
            newSourceHeadCode newSourceHeadStep index oldSourceFormula).
        {
          exact (hsourceHeadShift index
            (raw_lt_to_le M index predecessor hindexPred)
            oldSourceFormula hsourceOld).
        }
        assert (htargetMapped : RawCodedAssignmentLookup M
            newTargetHeadCode newTargetHeadStep index oldTargetFormula).
        {
          exact (htargetHeadShift index
            (raw_lt_to_le M index (raw_succ M predecessor)
              (raw_assignment_lt_trans M hPA index predecessor
                (raw_succ M predecessor) hindexPred
                (raw_assignment_lt_self_succ M hPA predecessor)))
            oldTargetFormula htargetOld).
        }
        assert (hsourceEq : sourceFormula = oldSourceFormula).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            newSourceHeadCode newSourceHeadStep index
            sourceFormula oldSourceFormula hsourceNew hsourceMapped).
        }
        assert (htargetEq : targetFormula = oldTargetFormula).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            newTargetHeadCode newTargetHeadStep index
            targetFormula oldTargetFormula htargetNew htargetMapped).
        }
        rewrite hsourceEq, htargetEq.
        exact (hlow (raw_succ M index)
          (raw_contextInsertShift_succ_lt_succ M hPA
            index depth hindex)
          oldSourceFormula hsourceOld oldTargetFormula htargetOld).
      * split.
        -- intros targetFormula htargetNew.
           assert (hsuccDepthTarget :
               rawLt M (raw_succ M depth)
                 (raw_succ M (raw_succ M predecessor))).
           {
             exact (raw_contextInsertShift_succ_lt_succ M hPA
               depth (raw_succ M predecessor) hdepthBelow).
           }
           destruct ((proj1 (proj2 (proj2 htargetTraversal)))
             (raw_succ M depth) hsuccDepthTarget)
             as [oldTargetFormula htargetOld].
           assert (htargetMapped : RawCodedAssignmentLookup M
               newTargetHeadCode newTargetHeadStep depth
               oldTargetFormula).
           {
             exact (htargetHeadShift depth
               (raw_lt_to_le M depth (raw_succ M predecessor)
                 hdepthBelow)
               oldTargetFormula htargetOld).
           }
           assert (htargetEq : targetFormula = oldTargetFormula).
           {
             exact (raw_codedAssignmentLookup_functional M hPA
               newTargetHeadCode newTargetHeadStep depth
               targetFormula oldTargetFormula htargetNew htargetMapped).
           }
           rewrite htargetEq.
           exact (hheadRow oldTargetFormula htargetOld).
        -- intros index hindex sourceFormula hsourceNew
             targetFormula htargetNew.
           assert (hsuccIndexPred : rawLt M (raw_succ M index)
               (raw_succ M predecessor)).
           {
             exact (raw_contextInsertShift_succ_lt_succ M hPA
               index predecessor hindex).
           }
           assert (hdoubleSuccIndex :
               rawLt M (raw_succ M (raw_succ M index))
                 (raw_succ M (raw_succ M predecessor))).
           {
             exact (raw_contextInsertShift_succ_lt_succ M hPA
               (raw_succ M index) (raw_succ M predecessor)
               hsuccIndexPred).
           }
           destruct ((proj1 (proj2 (proj2 hsourceTraversal)))
             (raw_succ M index) hsuccIndexPred)
             as [oldSourceFormula hsourceOld].
           destruct ((proj1 (proj2 (proj2 htargetTraversal)))
             (raw_succ M (raw_succ M index)) hdoubleSuccIndex)
             as [oldTargetFormula htargetOld].
           assert (hsourceMapped : RawCodedAssignmentLookup M
               newSourceHeadCode newSourceHeadStep index
               oldSourceFormula).
           {
             exact (hsourceHeadShift index
               (raw_lt_to_le M index predecessor hindex)
               oldSourceFormula hsourceOld).
           }
           assert (htargetMapped : RawCodedAssignmentLookup M
               newTargetHeadCode newTargetHeadStep (raw_succ M index)
               oldTargetFormula).
           {
             exact (htargetHeadShift (raw_succ M index)
               (raw_lt_to_le M (raw_succ M index)
                 (raw_succ M predecessor) hsuccIndexPred)
               oldTargetFormula htargetOld).
           }
           assert (hsourceEq : sourceFormula = oldSourceFormula).
           {
             exact (raw_codedAssignmentLookup_functional M hPA
               newSourceHeadCode newSourceHeadStep index
               sourceFormula oldSourceFormula hsourceNew hsourceMapped).
           }
           assert (htargetEq : targetFormula = oldTargetFormula).
           {
             exact (raw_codedAssignmentLookup_functional M hPA
               newTargetHeadCode newTargetHeadStep (raw_succ M index)
               targetFormula oldTargetFormula htargetNew htargetMapped).
           }
           destruct (hhigh (raw_succ M index) hsuccIndexPred
             oldSourceFormula hsourceOld oldTargetFormula htargetOld)
             as [hbelow | heq].
           ++ left.
              exact (raw_lt_succ_succ_inv M hPA
                index depth hbelow).
           ++ right. rewrite hsourceEq, htargetEq. exact heq.
Qed.

(** At depth zero, dropping the inserted head from [target] gives a context
    that shifts directly to [shiftedSource].  It need not be identified with
    [source] by an external decoder: insertion rows, traversal coherence, and
    the given source shift provide the required pointwise shift certificate. *)
Lemma raw_contextInsertAt_zero_shift_tail : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      head source target shiftedSource,
  RawContextInsertAt M head (raw_zero M) source target ->
  RawContextShift M source shiftedSource ->
  exists targetTail : M,
    target = rawListNode M head targetTail /\
    RawContextShift M targetTail shiftedSource.
Proof.
  intros M hPA head source target shiftedSource
    (insertBound & insertSourceTailCode & insertSourceTailStep &
      insertSourceHeadCode & insertSourceHeadStep &
      insertTargetTailCode & insertTargetTailStep &
      insertTargetHeadCode & insertTargetHeadStep &
      [hinsertSource [hinsertTarget
        [hinsertDepth [hinsertLow [hinsertHead hinsertHigh]]]]])
    (shiftBound & shiftSourceTailCode & shiftSourceTailStep &
      shiftSourceHeadCode & shiftSourceHeadStep &
      shiftedTailCode & shiftedTailStep &
      shiftedHeadCode & shiftedHeadStep &
      [hshiftSource [hshiftedSource hshiftRows]]).
  destruct (raw_contextListTraversals_coherent M hPA source
    insertBound
      insertSourceTailCode insertSourceTailStep
      insertSourceHeadCode insertSourceHeadStep
    shiftBound
      shiftSourceTailCode shiftSourceTailStep
      shiftSourceHeadCode shiftSourceHeadStep
    hinsertSource hshiftSource)
    as [hbound [_ hsourceHeadsAgree]].
  subst shiftBound.
  destruct (raw_contextListTraversal_succ_tail_exists M hPA
    target insertBound
    insertTargetTailCode insertTargetTailStep
    insertTargetHeadCode insertTargetHeadStep hinsertTarget) as
    (targetFirst & targetTail &
      newTargetTailCode & newTargetTailStep &
      newTargetHeadCode & newTargetHeadStep &
      htargetRoot & htargetHeadZero &
      htargetTailShift & htargetHeadShift & htargetTailTraversal).
  assert (htargetFirst : targetFirst = head).
  { exact (hinsertHead targetFirst htargetHeadZero). }
  exists targetTail.
  split.
  - rewrite <- htargetFirst. exact htargetRoot.
  - exists insertBound,
      newTargetTailCode, newTargetTailStep,
      newTargetHeadCode, newTargetHeadStep,
      shiftedTailCode, shiftedTailStep,
      shiftedHeadCode, shiftedHeadStep.
    split; [exact htargetTailTraversal |].
    split; [exact hshiftedSource |].
    intros index hindex targetFormula shiftedFormula
      htargetNew hshiftedLookup.
    assert (hsuccIndex : rawLt M (raw_succ M index)
        (raw_succ M insertBound)).
    {
      exact (raw_contextInsertShift_succ_lt_succ M hPA
        index insertBound hindex).
    }
    destruct ((proj1 (proj2 (proj2 hinsertTarget)))
      (raw_succ M index) hsuccIndex)
      as [oldTargetFormula htargetOld].
    assert (htargetMapped : RawCodedAssignmentLookup M
        newTargetHeadCode newTargetHeadStep index oldTargetFormula).
    {
      exact (htargetHeadShift index
        (raw_lt_to_le M index insertBound hindex)
        oldTargetFormula htargetOld).
    }
    assert (htargetEq : targetFormula = oldTargetFormula).
    {
      exact (raw_codedAssignmentLookup_functional M hPA
        newTargetHeadCode newTargetHeadStep index
        targetFormula oldTargetFormula htargetNew htargetMapped).
    }
    destruct ((proj1 (proj2 (proj2 hinsertSource))) index hindex)
      as [insertSourceFormula hinsertSourceLookup].
    destruct (hinsertHigh index hindex
      insertSourceFormula hinsertSourceLookup
      oldTargetFormula htargetOld)
      as [himpossible | htargetSource].
    { exfalso. exact (raw_not_lt_zero M hPA index himpossible). }
    destruct ((proj1 (proj2 (proj2 hshiftSource))) index hindex)
      as [shiftSourceFormula hshiftSourceLookup].
    assert (hsourceEq : insertSourceFormula = shiftSourceFormula).
    {
      exact (hsourceHeadsAgree index hindex
        insertSourceFormula shiftSourceFormula
        hinsertSourceLookup hshiftSourceLookup).
    }
    rewrite htargetEq, htargetSource, hsourceEq.
    exact (hshiftRows index hindex
      shiftSourceFormula shiftedFormula
      hshiftSourceLookup hshiftedLookup).
Qed.

(** ------------------------------------------------------------------
    The represented commuting-square invariant. *)

Definition RawContextInsertShiftCommutesAt (M : RawPAModel)
    (depth : M) : Prop :=
  forall head shiftedHead source target shiftedSource : M,
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1) head shiftedHead ->
    RawContextInsertAt M head depth source target ->
    RawContextShift M source shiftedSource ->
    exists shiftedTarget : M,
      RawContextShift M target shiftedTarget /\
      RawContextInsertAt M shiftedHead depth
        shiftedSource shiftedTarget.

Arguments RawContextInsertShiftCommutesAt M depth : clear implicits.

(** Binder order: head, shifted head, source, target, shifted source. *)
Definition contextInsertShiftAll5 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll body)))).

Definition contextInsertShiftImp3
    (first second third conclusion : formula) : formula :=
  pImp first (pImp second (pImp third conclusion)).

Definition contextInsertShiftCommutesAtTermAt (depth : term) : formula :=
  contextInsertShiftAll5
    (contextInsertShiftImp3
      (codedFormulaShiftTermAt
        tZero (Term.numeral 1) (tVar 4) (tVar 3))
      (contextInsertAtTermAt
        (tVar 4) (liftTerm 5 depth) (tVar 2) (tVar 1))
      (contextShiftTermAt (tVar 2) (tVar 0))
      (pEx
        (pAnd
          (** Under the existential, old [target] is variable two. *)
          (contextShiftTermAt (tVar 2) (tVar 0))
          (** The shifted head/source move to variables four/one. *)
          (contextInsertAtTermAt
            (tVar 4) (liftTerm 6 depth) (tVar 1) (tVar 0))))).

Lemma raw_contextInsertShift_eval_liftTerm_five : forall
    (M : RawPAModel) a b c d f (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d (scons M f e)))))
    (liftTerm 5 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 5) with (S (S (S (S (S index))))) by lia.
  reflexivity.
Qed.

Lemma raw_contextInsertShift_eval_liftTerm_six : forall
    (M : RawPAModel) a b c d f g (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c
      (scons M d (scons M f (scons M g e))))))
    (liftTerm 6 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 6) with (S (S (S (S (S (S index)))))) by lia.
  reflexivity.
Qed.

Lemma raw_sat_contextInsertShiftCommutesAtTermAt_iff : forall
    (M : RawPAModel) e depth,
  raw_formula_sat M e (contextInsertShiftCommutesAtTermAt depth) <->
  RawContextInsertShiftCommutesAt M (raw_term_eval M e depth).
Proof.
  intros M e depth.
  unfold contextInsertShiftCommutesAtTermAt,
    contextInsertShiftAll5, contextInsertShiftImp3,
    RawContextInsertShiftCommutesAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedFormulaShiftTermAt_iff.
  setoid_rewrite raw_sat_contextInsertAtTermAt_iff.
  setoid_rewrite raw_sat_contextShiftTermAt_iff.
  repeat setoid_rewrite raw_contextInsertShift_eval_liftTerm_five.
  repeat setoid_rewrite raw_contextInsertShift_eval_liftTerm_six.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_contextInsertShiftCommutesAt_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawContextInsertShiftCommutesAt M (raw_zero M).
Proof.
  intros M hPA head shiftedHead source target shiftedSource
    hheadShift hinsertion hsourceShift.
  destruct (raw_contextInsertAt_zero_shift_tail M hPA
    head source target shiftedSource hinsertion hsourceShift)
    as [targetTail [htargetRoot htailShift]].
  exists (rawListNode M shiftedHead shiftedSource).
  split.
  - rewrite htargetRoot.
    exact (raw_contextShift_cons M hPA
      targetTail shiftedSource head shiftedHead
      htailShift hheadShift).
  - exact (raw_contextInsertAt_zero M hPA shiftedSource shiftedHead
      (raw_contextShift_target_realizable M source shiftedSource
        hsourceShift)).
Qed.

Lemma raw_contextInsertShiftCommutesAt_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall depth,
  RawContextInsertShiftCommutesAt M depth ->
  RawContextInsertShiftCommutesAt M (raw_succ M depth).
Proof.
  intros M hPA depth hinduction
    head shiftedHead source target shiftedSource
    hheadShift hinsertion hsourceShift.
  destruct (raw_contextInsertAt_succ_invert M hPA
    head depth source target hinsertion) as
    (extra & sourceTail & targetTail &
      hsourceRoot & htargetRoot & htailInsertion).
  rewrite hsourceRoot in hsourceShift.
  destruct (raw_contextShift_cons_invert M hPA
    extra sourceTail shiftedSource hsourceShift) as
    (shiftedExtra & shiftedSourceTail &
      hshiftedSourceRoot & hextraShift & hsourceTailShift).
  destruct (hinduction head shiftedHead sourceTail targetTail
    shiftedSourceTail hheadShift htailInsertion hsourceTailShift) as
    (shiftedTargetTail & htargetTailShift & htailShiftedInsertion).
  exists (rawListNode M shiftedExtra shiftedTargetTail).
  split.
  - rewrite htargetRoot.
    exact (raw_contextShift_cons M hPA
      targetTail shiftedTargetTail extra shiftedExtra
      htargetTailShift hextraShift).
  - rewrite hshiftedSourceRoot.
    exact (raw_contextInsertAt_cons M hPA
      shiftedHead depth shiftedSourceTail shiftedTargetTail shiftedExtra
      htailShiftedInsertion).
Qed.

(** PA induction, rather than Rocq recursion, reaches every carrier element
    of an arbitrary model of PA, including nonstandard insertion depths. *)
Theorem raw_contextInsertShiftCommutesAt_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall depth,
  RawContextInsertShiftCommutesAt M depth.
Proof.
  intros M hPA.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := contextInsertShiftCommutesAtTermAt (tVar 0)).
  assert (hall : forall depth,
      raw_formula_sat M (scons M depth parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_contextInsertShiftCommutesAtTermAt_iff M
          (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_contextInsertShiftCommutesAt_zero M hPA).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_contextInsertShiftCommutesAtTermAt_iff M
          (scons M current parameterEnv) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_contextInsertShiftCommutesAtTermAt_iff M
          (scons M (raw_succ M current) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_contextInsertShiftCommutesAt_succ
        M hPA current hcurrent).
  }
  intro depth. unfold phi in hall.
  pose proof (proj1
    (raw_sat_contextInsertShiftCommutesAtTermAt_iff M
      (scons M depth parameterEnv) (tVar 0))
    (hall depth)) as hdepth.
  cbn [raw_term_eval scons] in hdepth. exact hdepth.
Qed.

(** Public commuting square in the premise order used by proof-rule
    reconstruction. *)
Corollary raw_contextInsertAt_shift_commutes : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      head shiftedHead depth source target shiftedSource,
  RawContextInsertAt M head depth source target ->
  RawContextShift M source shiftedSource ->
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1) head shiftedHead ->
  exists shiftedTarget : M,
    RawContextShift M target shiftedTarget /\
    RawContextInsertAt M shiftedHead depth
      shiftedSource shiftedTarget.
Proof.
  intros M hPA head shiftedHead depth source target shiftedSource
    hinsertion hsourceShift hheadShift.
  exact (raw_contextInsertShiftCommutesAt_all M hPA depth
    head shiftedHead source target shiftedSource
    hheadShift hinsertion hsourceShift).
Qed.

End PABoundedRawCodedContextInsertShiftCommutation.
