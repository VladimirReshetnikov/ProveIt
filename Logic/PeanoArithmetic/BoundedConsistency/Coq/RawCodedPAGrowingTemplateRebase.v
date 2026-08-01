(** Unary rebasing for a proof over a growing witnessed PA tail.

    This module is kept above concrete traversal clients in the dependency
    graph.  A producer and its caller may independently choose finite batches
    of PA-axiom witnesses; completed-context merge supplies a common target,
    while prefix-preserving transport keeps temporary assumptions intact.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextInsert
  RawCodedFixedLevelTruthTotality
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedLtSuccCasesProofCompilation
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport.

Module PABoundedRawCodedPAGrowingTemplateRebase.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextInsert.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.

(** Insert a finite suffix below an already present template prefix.  Prefix
    insertion alone cannot express this operation: [prefix ++ suffix] places
    the new assumptions next to the represented PA tail, not at the head of
    the context.  We instead insert each translated formula at the concrete
    depth [length prefix].  The represented context-insertion induction then
    transports the entire proof, including binder rules, at that depth.

    This lemma is translation-generic and assumes atomic adequacy only for
    the combined visible context.  It is useful whenever a producer was
    compiled under a small temporary context and a caller later retains more
    assumptions beneath it. *)
Theorem raw_codedPALocalProof_templateSuffix : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    baseContext prefix suffix conclusion root,
  RawContextListRealizable M baseContext ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (prefix ++ suffix) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    conclusion root ->
  exists suffixedRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (prefix ++ suffix))
      conclusion suffixedRoot.
Proof.
  intros M hPA translation baseContext prefix suffix.
  induction suffix as [|head tail ih] in prefix |- *;
    intros conclusion root hbase hadequate hproof.
  - rewrite app_nil_r. exists root. exact hproof.
  - assert (hinsertion : RawContextInsertAt M
        (rawTemplateFormula translation head)
        (rawNumeralValue M (length prefix))
        (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateContextCodeOnTail translation baseContext
          (prefix ++ [head]))).
    {
      clear conclusion root hadequate hproof tail ih.
      induction prefix as [|prefixHead prefixTail prefixIH].
      - cbn [length rawTemplateContextCodeOnTail].
        exact (raw_contextInsertAt_zero M hPA baseContext
          (rawTemplateFormula translation head) hbase).
      - cbn [length rawTemplateContextCodeOnTail].
        change (RawContextInsertAt M
          (rawTemplateFormula translation head)
          (raw_succ M (rawNumeralValue M (length prefixTail)))
          (rawListNode M (rawTemplateFormula translation prefixHead)
            (rawTemplateContextCodeOnTail translation baseContext
              prefixTail))
          (rawListNode M (rawTemplateFormula translation prefixHead)
            (rawTemplateContextCodeOnTail translation baseContext
              (prefixTail ++ [head])))).
        exact (raw_contextInsertAt_cons M hPA
          (rawTemplateFormula translation head)
          (rawNumeralValue M (length prefixTail))
          (rawTemplateContextCodeOnTail translation baseContext prefixTail)
          (rawTemplateContextCodeOnTail translation baseContext
            (prefixTail ++ [head]))
          (rawTemplateFormula translation prefixHead) prefixIH).
    }
    assert (hheadAdequate : RawCodedFormulaAtomicallyAdequate M
        (rawTemplateFormula translation head)).
    {
      apply hadequate.
      apply in_or_app. right. left. reflexivity.
    }
    destruct
      (raw_codedPALocalProofContextInsertAt M hPA root
        (rawTemplateFormula translation head)
        (rawNumeralValue M (length prefix))
        (rawTemplateContextCodeOnTail translation baseContext prefix)
        (rawTemplateContextCodeOnTail translation baseContext
          (prefix ++ [head])) conclusion
        hheadAdequate hinsertion hproof)
      as [headRoot hheadProof].
    assert (hremainingAdequate :
        RawCodedTemplatePrefixAtomicallyAdequate M translation
          ((prefix ++ [head]) ++ tail)).
    {
      intros formula hformula.
      apply hadequate.
      apply in_app_or in hformula.
      destruct hformula as [hprefixHead | htail].
      - apply in_app_or in hprefixHead.
        destruct hprefixHead as [hprefix | hhead].
        + apply in_or_app. left. exact hprefix.
        + cbn in hhead. destruct hhead as [hformula | hfalse].
          * subst formula. apply in_or_app. right. left. reflexivity.
          * contradiction.
      - apply in_or_app. right. right. exact htail.
    }
    destruct
      (ih (prefix ++ [head]) conclusion headRoot hbase
        hremainingAdequate hheadProof)
      as [suffixedRoot hsuffixed].
    exists suffixedRoot.
    assert (hshape : (prefix ++ [head]) ++ tail =
        prefix ++ head :: tail).
    {
      rewrite <- app_assoc. reflexivity.
    }
    rewrite hshape in hsuffixed.
    exact hsuffixed.
Qed.

(** Rebase one growing proof onto an arbitrary witnessed caller tail.  No
    relation between the producer's original source and the new caller is
    required: only the witnessed target actually selected by the producer
    needs to be merged. *)
Theorem raw_codedPAGrowingTemplateLocalProofAt_rebase : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    producerSourceWitnessList producerSourceContext prefix conclusion
    baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    producerSourceWitnessList producerSourceContext prefix conclusion ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    baseWitnessList baseContext prefix conclusion.
Proof.
  intros M hPA translation
    producerSourceWitnessList producerSourceContext prefix conclusion
    baseWitnessList baseContext hbase
    (producerWitnessList & producerContext & root &
      hproducerWitnessed & _hproducerSourceIncluded & hproof).
  destruct
    (raw_codedPAAxiomWitnessContext_prefixMerge M hPA
      producerWitnessList producerContext baseWitnessList baseContext
      hproducerWitnessed hbase)
    as (targetWitnessList & targetContext & htargetWitnessed &
      _hproducerWitnessIncluded & hproducerIncluded &
      _hbaseWitnessIncluded & hbaseIncluded & _hbaseTransport).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation producerWitnessList producerContext
      targetWitnessList targetContext prefix conclusion root
      hproducerWitnessed htargetWitnessed hproducerIncluded hproof)
    as [transportedRoot htransported].
  exists targetWitnessList, targetContext, transportedRoot.
  split; [exact htargetWitnessed |].
  split; [exact hbaseIncluded | exact htransported].
Qed.

End PABoundedRawCodedPAGrowingTemplateRebase.
