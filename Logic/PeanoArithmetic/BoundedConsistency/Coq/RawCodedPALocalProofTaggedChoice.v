(** Represented elimination of a disjunction tagged by exclusive formulas. *)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedContextLists
  RawCodedProofAssumptionLeaf
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofContextInsertUnconditional.

Module PABoundedRawCodedPALocalProofTaggedChoice.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.

(** Select the left payload when the right tag is contradictory.  Adequacy
    of the complete right branch is exactly what permits transport of the
    tag-negation proof beneath that branch assumption. *)
Theorem raw_codedPALocalProofOf_taggedChoice_left : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context leftTag left rightTag right choiceRoot notRightRoot,
  RawContextListRealizable M context ->
  RawCodedFormulaAtomicallyAdequate M
    (rawFormulaAndCode M rightTag right) ->
  RawCodedPALocalProofOf M context
    (rawFormulaOrCode M
      (rawFormulaAndCode M leftTag left)
      (rawFormulaAndCode M rightTag right)) choiceRoot ->
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M rightTag (rawFormulaBotCode M)) notRightRoot ->
  exists root, RawCodedPALocalProofOf M context left root.
Proof.
  intros M hPA context leftTag left rightTag right
    choiceRoot notRightRoot hcontext hrightAdequate hchoice hnotRight.
  pose proof (raw_codedPALocalProofOf_assumption M hPA context
    (rawFormulaAndCode M leftTag left) hcontext) as hleftBranch.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA
    (rawListNode M (rawFormulaAndCode M leftTag left) context)
    leftTag left
    (rawProofAssumptionRoot M
      (rawListNode M (rawFormulaAndCode M leftTag left) context)
      (rawFormulaAndCode M leftTag left)) hleftBranch) as hleft.
  pose proof (raw_codedPALocalProofOf_assumption M hPA context
    (rawFormulaAndCode M rightTag right) hcontext) as hrightBranch.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA
    (rawListNode M (rawFormulaAndCode M rightTag right) context)
    rightTag right
    (rawProofAssumptionRoot M
      (rawListNode M (rawFormulaAndCode M rightTag right) context)
      (rawFormulaAndCode M rightTag right)) hrightBranch) as hrightTag.
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    context (rawFormulaAndCode M rightTag right)
    (rawFormulaImpCode M rightTag (rawFormulaBotCode M))
    notRightRoot hrightAdequate hcontext hnotRight)
    as [liftedNotRightRoot hliftedNotRight].
  lazymatch type of hrightTag with
  | RawCodedPALocalProofOf _ _ _ ?rightTagRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA
        (rawListNode M (rawFormulaAndCode M rightTag right) context)
        rightTag (rawFormulaBotCode M)
        liftedNotRightRoot rightTagRoot hliftedNotRight hrightTag)
        as hbottom
  end.
  lazymatch type of hbottom with
  | RawCodedPALocalProofOf _ _ _ ?bottomRoot =>
      pose proof (raw_codedPALocalProofOf_botE M hPA
        (rawListNode M (rawFormulaAndCode M rightTag right) context)
        bottomRoot hbottom left) as hright
  end.
  lazymatch type of hleft with
  | RawCodedPALocalProofOf _ _ _ ?leftRoot =>
      lazymatch type of hright with
      | RawCodedPALocalProofOf _ _ _ ?rightRoot =>
          eexists;
          exact (raw_codedPALocalProofOf_orE M hPA context
            (rawFormulaAndCode M leftTag left)
            (rawFormulaAndCode M rightTag right) left
            choiceRoot leftRoot rightRoot hchoice hleft hright)
      end
  end.
Qed.

(** Symmetric selector for the right payload. *)
Theorem raw_codedPALocalProofOf_taggedChoice_right : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context leftTag left rightTag right choiceRoot notLeftRoot,
  RawContextListRealizable M context ->
  RawCodedFormulaAtomicallyAdequate M
    (rawFormulaAndCode M leftTag left) ->
  RawCodedPALocalProofOf M context
    (rawFormulaOrCode M
      (rawFormulaAndCode M leftTag left)
      (rawFormulaAndCode M rightTag right)) choiceRoot ->
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M leftTag (rawFormulaBotCode M)) notLeftRoot ->
  exists root, RawCodedPALocalProofOf M context right root.
Proof.
  intros M hPA context leftTag left rightTag right
    choiceRoot notLeftRoot hcontext hleftAdequate hchoice hnotLeft.
  pose proof (raw_codedPALocalProofOf_assumption M hPA context
    (rawFormulaAndCode M leftTag left) hcontext) as hleftBranch.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA
    (rawListNode M (rawFormulaAndCode M leftTag left) context)
    leftTag left
    (rawProofAssumptionRoot M
      (rawListNode M (rawFormulaAndCode M leftTag left) context)
      (rawFormulaAndCode M leftTag left)) hleftBranch) as hleftTag.
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    context (rawFormulaAndCode M leftTag left)
    (rawFormulaImpCode M leftTag (rawFormulaBotCode M))
    notLeftRoot hleftAdequate hcontext hnotLeft)
    as [liftedNotLeftRoot hliftedNotLeft].
  lazymatch type of hleftTag with
  | RawCodedPALocalProofOf _ _ _ ?leftTagRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA
        (rawListNode M (rawFormulaAndCode M leftTag left) context)
        leftTag (rawFormulaBotCode M)
        liftedNotLeftRoot leftTagRoot hliftedNotLeft hleftTag)
        as hbottom
  end.
  lazymatch type of hbottom with
  | RawCodedPALocalProofOf _ _ _ ?bottomRoot =>
      pose proof (raw_codedPALocalProofOf_botE M hPA
        (rawListNode M (rawFormulaAndCode M leftTag left) context)
        bottomRoot hbottom right) as hleft
  end.
  pose proof (raw_codedPALocalProofOf_assumption M hPA context
    (rawFormulaAndCode M rightTag right) hcontext) as hrightBranch.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA
    (rawListNode M (rawFormulaAndCode M rightTag right) context)
    rightTag right
    (rawProofAssumptionRoot M
      (rawListNode M (rawFormulaAndCode M rightTag right) context)
      (rawFormulaAndCode M rightTag right)) hrightBranch) as hright.
  lazymatch type of hleft with
  | RawCodedPALocalProofOf _ _ _ ?leftRoot =>
      lazymatch type of hright with
      | RawCodedPALocalProofOf _ _ _ ?rightRoot =>
          eexists;
          exact (raw_codedPALocalProofOf_orE M hPA context
            (rawFormulaAndCode M leftTag left)
            (rawFormulaAndCode M rightTag right) right
            choiceRoot leftRoot rightRoot hchoice hleft hright)
      end
  end.
Qed.

End PABoundedRawCodedPALocalProofTaggedChoice.
