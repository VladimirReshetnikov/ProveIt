(**
  Close guarded Boolean predecessor laws and produce the two diagonal pairs.

  The constructor-specific work has already been reduced to direct-child
  admissibility.  Here that admissibility proof is synchronized with the
  projected local exclusivity theorem and its selected Sigma/Pi evidence,
  then all branch assumptions are discharged in their real binder order.
  A fixed PA proof of the corresponding guarded cell finally removes the
  predecessor premise and leaves the exact And/And or Or/Or collision pair.

  No theorem in this file assumes the historical unconditional predecessor
  exclusivity formula.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextShift
  RawCodedProofAllIConstructor
  RawCodedProofImpIConstructor
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPAAxiomContextSelfShift
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedPALocalProofTripleUniversalIntroduction
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedTemplateTripleUniversalOpening
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedDynamicTruthLocalExclusiveTemplateDirectInputs
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation
  RawCodedDynamicTruthBooleanGuardedBranchExclusivity
  RawCodedDynamicTruthBooleanDirectChildAdmissibilityProofCompilation
  RawCodedDynamicTruthNativeLocalGuardedNonImpPairCompilation.

Module PABoundedRawCodedDynamicTruthBooleanGuardedDiagonalCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedPALocalProofTripleUniversalIntroduction.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedTemplateTripleUniversalOpening.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import
  PABoundedRawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation.
Import PABoundedRawCodedDynamicTruthBooleanGuardedBranchExclusivity.
Import
  PABoundedRawCodedDynamicTruthBooleanDirectChildAdmissibilityProofCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedNonImpPairCompilation.

(** The Boolean predecessor uses exactly the same carrier coordinates as
    the implication predecessor.  Aliasing them makes the agreement with
    the already projected local law and evidence roots explicit. *)
Definition coqDynamicTruthBooleanGuardedLevelTerm : TemplateTerm :=
  coqDynamicTruthImpGuardedLevelTerm.
Definition coqDynamicTruthBooleanGuardedParentTerm : TemplateTerm :=
  coqDynamicTruthImpGuardedParentTerm.
Definition coqDynamicTruthBooleanGuardedLeftTerm : TemplateTerm :=
  coqDynamicTruthImpGuardedLeftTerm.
Definition coqDynamicTruthBooleanGuardedRightTerm : TemplateTerm :=
  coqDynamicTruthImpGuardedRightTerm.
Definition coqDynamicTruthBooleanGuardedChildTerm : TemplateTerm :=
  coqDynamicTruthImpGuardedChildTerm.
Definition coqDynamicTruthBooleanGuardedAssignmentCodeTerm : TemplateTerm :=
  coqDynamicTruthImpGuardedAssignmentCodeTerm.
Definition coqDynamicTruthBooleanGuardedAssignmentStepTerm : TemplateTerm :=
  coqDynamicTruthImpGuardedAssignmentStepTerm.

Definition coqDynamicTruthBooleanGuardedShapeTemplate
    (constructor : DynamicTruthBooleanConstructor) : TemplateFormula :=
  coqDynamicTruthBooleanGuardedChildShapeTemplate constructor
    coqDynamicTruthBooleanGuardedLevelTerm
    coqDynamicTruthBooleanGuardedParentTerm
    coqDynamicTruthBooleanGuardedLeftTerm
    coqDynamicTruthBooleanGuardedRightTerm
    coqDynamicTruthBooleanGuardedChildTerm.

Definition coqDynamicTruthBooleanGuardedDirectChildTemplate
    (constructor : DynamicTruthBooleanConstructor) : TemplateFormula :=
  coqDynamicTruthBooleanGuardedChildGuardTemplate constructor
    coqDynamicTruthBooleanGuardedLevelTerm
    coqDynamicTruthBooleanGuardedParentTerm
    coqDynamicTruthBooleanGuardedLeftTerm
    coqDynamicTruthBooleanGuardedRightTerm
    coqDynamicTruthBooleanGuardedChildTerm.

Definition coqDynamicTruthBooleanGuardedConstructorBodyTemplate
    (constructor : DynamicTruthBooleanConstructor) : TemplateFormula :=
  tfImp (coqDynamicTruthBooleanGuardedShapeTemplate constructor)
    (tfImp (coqDynamicTruthBooleanGuardedDirectChildTemplate constructor)
      tfBot).

Definition coqDynamicTruthBooleanGuardedPredecessorBodyTemplate
    (constructor : DynamicTruthBooleanConstructor) : TemplateFormula :=
  tfImp (embedPAFormula dynamicTruthPredecessorSigmaStateMemberBodyFormula)
    (tfImp
      (embedPAFormula dynamicTruthPredecessorPiStateMemberBodyFormula)
      (tfAll (tfAll
        (coqDynamicTruthBooleanGuardedConstructorBodyTemplate
          constructor)))).

Definition coqDynamicTruthBooleanGuardedPredecessorFormulaTemplate
    (constructor : DynamicTruthBooleanConstructor) : TemplateFormula :=
  tfAll (tfAll (tfAll
    (coqDynamicTruthBooleanGuardedPredecessorBodyTemplate constructor))).

Lemma coqDynamicTruthBooleanGuardedPredecessorFormulaTemplate_eq_embedPA :
    forall constructor,
  coqDynamicTruthBooleanGuardedPredecessorFormulaTemplate constructor =
  embedPAFormula
    (dynamicTruthBooleanGuardedPredecessorStateExclusivityFormula
      constructor).
Proof.
  intro constructor. destruct constructor; vm_compute; reflexivity.
Qed.

Definition coqDynamicTruthBooleanGuardedLocalAdmissibleTemplate
    : TemplateFormula :=
  coqDynamicTruthImpGuardedLocalAdmissibleTemplate.
Definition coqDynamicTruthBooleanGuardedLocalSigmaEvidenceTemplate
    : TemplateFormula :=
  coqDynamicTruthImpGuardedLocalSigmaEvidenceTemplate.
Definition coqDynamicTruthBooleanGuardedLocalPiEvidenceTemplate
    : TemplateFormula :=
  coqDynamicTruthImpGuardedLocalPiEvidenceTemplate.
Definition coqDynamicTruthBooleanGuardedLocalExclusiveBodyTemplate
    : TemplateFormula :=
  coqDynamicTruthImpGuardedLocalExclusiveBodyTemplate.

Lemma coqDynamicTruthBooleanGuardedLocalExclusiveBodyTemplate_shape :
  coqDynamicTruthBooleanGuardedLocalExclusiveBodyTemplate =
  tfImp coqDynamicTruthBooleanGuardedLocalAdmissibleTemplate
    (tfImp coqDynamicTruthBooleanGuardedLocalSigmaEvidenceTemplate
      (tfImp coqDynamicTruthBooleanGuardedLocalPiEvidenceTemplate tfBot)).
Proof.
  exact coqDynamicTruthImpGuardedLocalExclusiveBodyTemplate_shape.
Qed.

Definition coqDynamicTruthBooleanGuardedChildAdmissibleConcreteTemplate
    (constructor : DynamicTruthBooleanConstructor) : TemplateFormula :=
  coqDynamicTruthBooleanGuardedChildAdmissibleTemplate constructor
    coqDynamicTruthBooleanGuardedLevelTerm
    coqDynamicTruthBooleanGuardedParentTerm
    coqDynamicTruthBooleanGuardedLeftTerm
    coqDynamicTruthBooleanGuardedRightTerm
    coqDynamicTruthBooleanGuardedChildTerm
    coqDynamicTruthBooleanGuardedAssignmentCodeTerm
    coqDynamicTruthBooleanGuardedAssignmentStepTerm.

Lemma
    coqDynamicTruthBooleanGuardedChildAdmissibleConcreteTemplate_eq_local :
    forall constructor,
  coqDynamicTruthBooleanGuardedChildAdmissibleConcreteTemplate constructor =
  coqDynamicTruthBooleanGuardedLocalAdmissibleTemplate.
Proof.
  intro constructor.
  unfold coqDynamicTruthBooleanGuardedChildAdmissibleConcreteTemplate,
    coqDynamicTruthBooleanGuardedLocalAdmissibleTemplate.
  rewrite coqDynamicTruthBooleanGuardedChildAdmissibleTemplate_eq_imp.
  apply coqDynamicTruthImpGuardedChildAdmissibleConcreteTemplate_eq_local.
Qed.

Definition coqDynamicTruthBooleanGuardedDeepPrefix
    (constructor : DynamicTruthBooleanConstructor)
    (callerPrefix : TemplateContext) : TemplateContext :=
  [coqDynamicTruthBooleanGuardedDirectChildTemplate constructor;
   coqDynamicTruthBooleanGuardedShapeTemplate constructor] ++
  templateContextShiftMany 2
    (coqDynamicTruthPredecessorStateTemplateContext ++
      templateContextShiftMany 3 callerPrefix).

(** Exact roots available in the deepest honest Boolean branch. *)
Record RawDynamicTruthBooleanGuardedBranchRootsAt
    (constructor : DynamicTruthBooleanConstructor)
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (baseContext : M) (callerPrefix : TemplateContext) : Prop := {
  rawDynamicTruthBooleanGuardedBranch_source : exists sourceRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthBooleanGuardedDeepPrefix
          constructor callerPrefix))
      (rawTemplateFormula translation
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate)))) sourceRoot;
  rawDynamicTruthBooleanGuardedBranch_parentAtomic : exists atomicRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthBooleanGuardedDeepPrefix
          constructor callerPrefix))
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanDirectChildAtomicPremiseTemplate constructor
          coqDynamicTruthBooleanGuardedLevelTerm
          coqDynamicTruthBooleanGuardedParentTerm
          coqDynamicTruthBooleanGuardedLeftTerm
          coqDynamicTruthBooleanGuardedRightTerm
          coqDynamicTruthBooleanGuardedChildTerm)) atomicRoot;
  rawDynamicTruthBooleanGuardedBranch_parentDomain : exists domainRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthBooleanGuardedDeepPrefix
          constructor callerPrefix))
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanDirectChildDomainPremiseTemplate constructor
          coqDynamicTruthBooleanGuardedLevelTerm
          coqDynamicTruthBooleanGuardedParentTerm
          coqDynamicTruthBooleanGuardedLeftTerm
          coqDynamicTruthBooleanGuardedRightTerm
          coqDynamicTruthBooleanGuardedChildTerm)) domainRoot;
  rawDynamicTruthBooleanGuardedBranch_sigmaEvidence : exists sigmaRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthBooleanGuardedDeepPrefix
          constructor callerPrefix))
      (rawTemplateFormula translation
        coqDynamicTruthBooleanGuardedLocalSigmaEvidenceTemplate) sigmaRoot;
  rawDynamicTruthBooleanGuardedBranch_piEvidence : exists piRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqDynamicTruthBooleanGuardedDeepPrefix
          constructor callerPrefix))
      (rawTemplateFormula translation
        coqDynamicTruthBooleanGuardedLocalPiEvidenceTemplate) piRoot
}.

Arguments RawDynamicTruthBooleanGuardedBranchRootsAt
  constructor M translation baseContext callerPrefix : clear implicits.

(** Close a single guarded Boolean predecessor.  The output base may grow
    only by a finite standard PA-axiom prefix selected while proving child
    admissibility; every incoming root is transported to that same base. *)
Theorem
    raw_dynamicTruthBooleanGuardedPredecessorRoot_of_branch_roots_under_template_prefix :
  forall constructor (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext callerPrefix,
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix) ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawDynamicTruthBooleanGuardedBranchRootsAt constructor M translation
    baseContext callerPrefix ->
  exists targetWitnessList targetContext predecessorRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        targetContext callerPrefix)
      (rawDynamicTruthBooleanGuardedPredecessorStateExclusivityCode
        M constructor) predecessorRoot.
Proof.
  intros constructor M hPA translation hagreement
    baseWitnessList baseContext callerPrefix hdeepAdequate hbase hroots.
  destruct hroots as
    [(sourceRoot & hsource) (parentAtomicRoot & hparentAtomic)
      (parentDomainRoot & hparentDomain)
      (sigmaRoot & hsigma) (piRoot & hpi)].
  assert (hshapeIn :
      In (coqDynamicTruthBooleanGuardedShapeTemplate constructor)
        (coqDynamicTruthBooleanGuardedDeepPrefix
          constructor callerPrefix)).
  {
    unfold coqDynamicTruthBooleanGuardedDeepPrefix.
    cbn. auto.
  }
  assert (hguardIn :
      In (coqDynamicTruthBooleanGuardedDirectChildTemplate constructor)
        (coqDynamicTruthBooleanGuardedDeepPrefix
          constructor callerPrefix)).
  {
    unfold coqDynamicTruthBooleanGuardedDeepPrefix.
    cbn. auto.
  }
  destruct
    (raw_codedPALocalProofOf_dynamicTruthBooleanGuardedChildAdmissible_of_parent_roots_on_witnessed_extension_under_prefix
      constructor M hPA translation hagreement
      baseWitnessList baseContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
      coqDynamicTruthBooleanGuardedLevelTerm
      coqDynamicTruthBooleanGuardedParentTerm
      coqDynamicTruthBooleanGuardedLeftTerm
      coqDynamicTruthBooleanGuardedRightTerm
      coqDynamicTruthBooleanGuardedChildTerm
      coqDynamicTruthBooleanGuardedAssignmentCodeTerm
      coqDynamicTruthBooleanGuardedAssignmentStepTerm
      parentAtomicRoot parentDomainRoot
      hdeepAdequate hbase hshapeIn hguardIn
      hparentAtomic hparentDomain)
    as (targetWitnessList & targetContext & admissibleRoot &
      htargetWitnessed & hincluded & hadmissible).
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation targetContext
      (coqDynamicTruthBooleanGuardedDeepPrefix
        constructor callerPrefix))
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanGuardedChildAdmissibleConcreteTemplate
        constructor)) admissibleRoot) in hadmissible.
  rewrite
    coqDynamicTruthBooleanGuardedChildAdmissibleConcreteTemplate_eq_local
    in hadmissible.
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
      (rawTemplateFormula translation
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate))))
      sourceRoot hbase htargetWitnessed hincluded hsource)
    as [transportedSourceRoot htransportedSource].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
      (rawTemplateFormula translation
        coqDynamicTruthBooleanGuardedLocalSigmaEvidenceTemplate)
      sigmaRoot hbase htargetWitnessed hincluded hsigma)
    as [transportedSigmaRoot htransportedSigma].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
      (rawTemplateFormula translation
        coqDynamicTruthBooleanGuardedLocalPiEvidenceTemplate)
      piRoot hbase htargetWitnessed hincluded hpi)
    as [transportedPiRoot htransportedPi].
  pose proof (raw_template_all3_elimination_chain M translation
    coqDynamicTruthLocalExclusiveBodyTemplate
    coqDynamicTruthBooleanGuardedChildTerm
    coqDynamicTruthBooleanGuardedAssignmentCodeTerm
    coqDynamicTruthBooleanGuardedAssignmentStepTerm) as hchain.
  destruct
    (raw_codedPALocalProofOf_universal_elimination_chain
      M hPA
      (rawTemplateContextCodeOnTail translation targetContext
        (coqDynamicTruthBooleanGuardedDeepPrefix
          constructor callerPrefix))
      (rawTemplateFormula translation
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate))))
      (rawTemplateFormula translation
        coqDynamicTruthBooleanGuardedLocalExclusiveBodyTemplate)
      hchain transportedSourceRoot htransportedSource)
    as [openedRoot hopened].
  rewrite coqDynamicTruthBooleanGuardedLocalExclusiveBodyTemplate_shape,
    !rawTemplateFormula_imp, rawTemplateFormula_bot in hopened.
  destruct (raw_codedPALocalProofOf_impE3 M hPA
    (rawTemplateContextCodeOnTail translation targetContext
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix))
    (rawTemplateFormula translation
      coqDynamicTruthBooleanGuardedLocalAdmissibleTemplate)
    (rawTemplateFormula translation
      coqDynamicTruthBooleanGuardedLocalSigmaEvidenceTemplate)
    (rawTemplateFormula translation
      coqDynamicTruthBooleanGuardedLocalPiEvidenceTemplate)
    (rawFormulaBotCode M)
    openedRoot admissibleRoot transportedSigmaRoot transportedPiRoot
    hopened hadmissible htransportedSigma htransportedPi)
    as [bottomRoot hbottom].

  (** Discharge direct-child and constructor-shape assumptions, then close
      the two constructor witnesses in their successive shifted contexts. *)
  set (prefix3 := templateContextShiftMany 3 callerPrefix).
  set (statePrefix :=
    coqDynamicTruthPredecessorStateTemplateContext ++ prefix3).
  set (statePrefix1 := templateContextShift statePrefix).
  set (statePrefix2 := templateContextShift statePrefix1).
  set (stateContext0 := rawTemplateContextCodeOnTail translation
    targetContext statePrefix).
  set (stateContext1 := rawTemplateContextCodeOnTail translation
    targetContext statePrefix1).
  set (stateContext2 := rawTemplateContextCodeOnTail translation
    targetContext statePrefix2).
  assert (hbottomAtHeads : RawCodedPALocalProofOf M
      (rawListNode M
        (rawTemplateFormula translation
          (coqDynamicTruthBooleanGuardedDirectChildTemplate constructor))
        (rawListNode M
          (rawTemplateFormula translation
            (coqDynamicTruthBooleanGuardedShapeTemplate constructor))
          stateContext2))
      (rawFormulaBotCode M) bottomRoot).
  {
    unfold coqDynamicTruthBooleanGuardedDeepPrefix in hbottom.
    unfold stateContext2, statePrefix2, statePrefix1, statePrefix, prefix3.
    cbn [List.app rawTemplateContextCodeOnTail
      templateContextShiftMany] in hbottom |- *.
    exact hbottom.
  }
  set (guardImpRoot := rawProofImpIRoot M
    (rawListNode M
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanGuardedShapeTemplate constructor))
      stateContext2)
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanGuardedDirectChildTemplate constructor))
    (rawFormulaBotCode M) bottomRoot).
  assert (hguardImp : RawCodedPALocalProofOf M
      (rawListNode M
        (rawTemplateFormula translation
          (coqDynamicTruthBooleanGuardedShapeTemplate constructor))
        stateContext2)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (coqDynamicTruthBooleanGuardedDirectChildTemplate constructor))
        (rawFormulaBotCode M)) guardImpRoot).
  {
    unfold guardImpRoot.
    exact (raw_codedPALocalProofOf_impI M hPA
      (rawListNode M
        (rawTemplateFormula translation
          (coqDynamicTruthBooleanGuardedShapeTemplate constructor))
        stateContext2)
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanGuardedDirectChildTemplate constructor))
      (rawFormulaBotCode M) bottomRoot hbottomAtHeads).
  }
  set (constructorBodyRoot := rawProofImpIRoot M stateContext2
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanGuardedShapeTemplate constructor))
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanGuardedDirectChildTemplate constructor))
      (rawFormulaBotCode M)) guardImpRoot).
  assert (hconstructorBody : RawCodedPALocalProofOf M stateContext2
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (coqDynamicTruthBooleanGuardedShapeTemplate constructor))
        (rawFormulaImpCode M
          (rawTemplateFormula translation
            (coqDynamicTruthBooleanGuardedDirectChildTemplate constructor))
          (rawFormulaBotCode M))) constructorBodyRoot).
  {
    unfold constructorBodyRoot.
    exact (raw_codedPALocalProofOf_impI M hPA stateContext2
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanGuardedShapeTemplate constructor))
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (coqDynamicTruthBooleanGuardedDirectChildTemplate constructor))
        (rawFormulaBotCode M)) guardImpRoot hguardImp).
  }
  assert (hconstructorTemplate : RawCodedPALocalProofOf M stateContext2
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanGuardedConstructorBodyTemplate constructor))
      constructorBodyRoot).
  {
    unfold coqDynamicTruthBooleanGuardedConstructorBodyTemplate.
    rewrite !rawTemplateFormula_imp, rawTemplateFormula_bot.
    exact hconstructorBody.
  }
  assert (hstateShift01 : RawContextShift M stateContext0 stateContext1).
  {
    unfold stateContext0, stateContext1, statePrefix1.
    exact (raw_templateContextOnTail_shift M hPA translation
      targetContext statePrefix
      (raw_codedPAAxiomWitnessContext_selfShift M hPA
        targetWitnessList targetContext htargetWitnessed)).
  }
  assert (hstateShift12 : RawContextShift M stateContext1 stateContext2).
  {
    unfold stateContext1, stateContext2, statePrefix2.
    exact (raw_templateContextOnTail_shift M hPA translation
      targetContext statePrefix1
      (raw_codedPAAxiomWitnessContext_selfShift M hPA
        targetWitnessList targetContext htargetWitnessed)).
  }
  pose proof (raw_codedPALocalProofOf_close2_between M hPA
    stateContext0 stateContext1 stateContext2
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanGuardedConstructorBodyTemplate constructor))
    constructorBodyRoot hstateShift01 hstateShift12
    hconstructorTemplate) as hall2.
  set (all2Root := rawPALocalProofClose2BetweenRoot M
    stateContext0 stateContext1
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanGuardedConstructorBodyTemplate constructor))
    constructorBodyRoot).
  set (outer3Context := rawTemplateContextCodeOnTail translation
    targetContext prefix3).
  assert (hall2AtStates : RawCodedPALocalProofOf M
      (rawListNode M
        (rawTemplateFormula translation
          (embedPAFormula
            dynamicTruthPredecessorPiStateMemberBodyFormula))
        (rawListNode M
          (rawTemplateFormula translation
            (embedPAFormula
              dynamicTruthPredecessorSigmaStateMemberBodyFormula))
          outer3Context))
      (rawFormulaAllCode M (rawFormulaAllCode M
        (rawTemplateFormula translation
          (coqDynamicTruthBooleanGuardedConstructorBodyTemplate
            constructor))))
      all2Root).
  {
    unfold stateContext0, statePrefix,
      coqDynamicTruthPredecessorStateTemplateContext, outer3Context.
    cbn [List.app rawTemplateContextCodeOnTail].
    exact hall2.
  }
  set (piImpRoot := rawProofImpIRoot M
    (rawListNode M
      (rawTemplateFormula translation
        (embedPAFormula
          dynamicTruthPredecessorSigmaStateMemberBodyFormula))
      outer3Context)
    (rawTemplateFormula translation
      (embedPAFormula dynamicTruthPredecessorPiStateMemberBodyFormula))
    (rawFormulaAllCode M (rawFormulaAllCode M
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanGuardedConstructorBodyTemplate
          constructor))))
    all2Root).
  assert (hpiImp : RawCodedPALocalProofOf M
      (rawListNode M
        (rawTemplateFormula translation
          (embedPAFormula
            dynamicTruthPredecessorSigmaStateMemberBodyFormula))
        outer3Context)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (embedPAFormula dynamicTruthPredecessorPiStateMemberBodyFormula))
        (rawFormulaAllCode M (rawFormulaAllCode M
          (rawTemplateFormula translation
            (coqDynamicTruthBooleanGuardedConstructorBodyTemplate
              constructor)))))
      piImpRoot).
  {
    unfold piImpRoot.
    exact (raw_codedPALocalProofOf_impI M hPA
      (rawListNode M
        (rawTemplateFormula translation
          (embedPAFormula
            dynamicTruthPredecessorSigmaStateMemberBodyFormula))
        outer3Context)
      (rawTemplateFormula translation
        (embedPAFormula dynamicTruthPredecessorPiStateMemberBodyFormula))
      (rawFormulaAllCode M (rawFormulaAllCode M
        (rawTemplateFormula translation
          (coqDynamicTruthBooleanGuardedConstructorBodyTemplate
            constructor))))
      all2Root hall2AtStates).
  }
  set (stateBodyRoot := rawProofImpIRoot M outer3Context
    (rawTemplateFormula translation
      (embedPAFormula
        dynamicTruthPredecessorSigmaStateMemberBodyFormula))
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        (embedPAFormula dynamicTruthPredecessorPiStateMemberBodyFormula))
      (rawFormulaAllCode M (rawFormulaAllCode M
        (rawTemplateFormula translation
          (coqDynamicTruthBooleanGuardedConstructorBodyTemplate
            constructor)))))
    piImpRoot).
  assert (hstateBody : RawCodedPALocalProofOf M outer3Context
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (embedPAFormula
            dynamicTruthPredecessorSigmaStateMemberBodyFormula))
        (rawFormulaImpCode M
          (rawTemplateFormula translation
            (embedPAFormula
              dynamicTruthPredecessorPiStateMemberBodyFormula))
          (rawFormulaAllCode M (rawFormulaAllCode M
            (rawTemplateFormula translation
              (coqDynamicTruthBooleanGuardedConstructorBodyTemplate
                constructor))))))
      stateBodyRoot).
  {
    unfold stateBodyRoot.
    exact (raw_codedPALocalProofOf_impI M hPA outer3Context
      (rawTemplateFormula translation
        (embedPAFormula
          dynamicTruthPredecessorSigmaStateMemberBodyFormula))
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (embedPAFormula dynamicTruthPredecessorPiStateMemberBodyFormula))
        (rawFormulaAllCode M (rawFormulaAllCode M
          (rawTemplateFormula translation
            (coqDynamicTruthBooleanGuardedConstructorBodyTemplate
              constructor)))))
      piImpRoot hpiImp).
  }
  assert (hstateTemplate : RawCodedPALocalProofOf M outer3Context
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanGuardedPredecessorBodyTemplate constructor))
      stateBodyRoot).
  {
    unfold coqDynamicTruthBooleanGuardedPredecessorBodyTemplate.
    rewrite !rawTemplateFormula_imp, !rawTemplateFormula_all.
    exact hstateBody.
  }

  (** Close the three predecessor variables across the actual successive
      caller-prefix contexts. *)
  set (outerContext0 := rawTemplateContextCodeOnTail translation
    targetContext callerPrefix).
  set (outerContext1 := rawTemplateContextCodeOnTail translation
    targetContext (templateContextShift callerPrefix)).
  set (outerContext2 := rawTemplateContextCodeOnTail translation
    targetContext (templateContextShift (templateContextShift
      callerPrefix))).
  assert (houterShift01 : RawContextShift M outerContext0 outerContext1).
  {
    unfold outerContext0, outerContext1.
    exact (raw_templateContextOnTail_shift M hPA translation
      targetContext callerPrefix
      (raw_codedPAAxiomWitnessContext_selfShift M hPA
        targetWitnessList targetContext htargetWitnessed)).
  }
  assert (houterShift12 : RawContextShift M outerContext1 outerContext2).
  {
    unfold outerContext1, outerContext2.
    exact (raw_templateContextOnTail_shift M hPA translation
      targetContext (templateContextShift callerPrefix)
      (raw_codedPAAxiomWitnessContext_selfShift M hPA
        targetWitnessList targetContext htargetWitnessed)).
  }
  assert (houterShift23 : RawContextShift M outerContext2 outer3Context).
  {
    unfold outerContext2, outer3Context, prefix3.
    cbn [templateContextShiftMany].
    exact (raw_templateContextOnTail_shift M hPA translation
      targetContext
      (templateContextShift (templateContextShift callerPrefix))
      (raw_codedPAAxiomWitnessContext_selfShift M hPA
        targetWitnessList targetContext htargetWitnessed)).
  }
  pose proof (raw_codedPALocalProofOf_close3_between M hPA
    outerContext0 outerContext1 outerContext2 outer3Context
    (rawTemplateFormula translation
      (coqDynamicTruthBooleanGuardedPredecessorBodyTemplate constructor))
    stateBodyRoot houterShift01 houterShift12 houterShift23
    hstateTemplate) as hclosed.
  exists targetWitnessList, targetContext,
    (rawPALocalProofClose3BetweenRoot M
      outerContext0 outerContext1 outerContext2
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanGuardedPredecessorBodyTemplate constructor))
      stateBodyRoot).
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  assert (hclosedTemplate : RawCodedPALocalProofOf M outerContext0
      (rawTemplateFormula translation
        (coqDynamicTruthBooleanGuardedPredecessorFormulaTemplate
          constructor))
      (rawPALocalProofClose3BetweenRoot M
        outerContext0 outerContext1 outerContext2
        (rawTemplateFormula translation
          (coqDynamicTruthBooleanGuardedPredecessorBodyTemplate constructor))
        stateBodyRoot)).
  {
    unfold coqDynamicTruthBooleanGuardedPredecessorFormulaTemplate.
    rewrite !rawTemplateFormula_all.
    exact hclosed.
  }
  rewrite
    coqDynamicTruthBooleanGuardedPredecessorFormulaTemplate_eq_embedPA
    in hclosedTemplate.
  rewrite (rawTemplateFormula_embedPA hagreement
    (dynamicTruthBooleanGuardedPredecessorStateExclusivityFormula
      constructor)) in hclosedTemplate.
  rewrite <-
    rawDynamicTruthBooleanGuardedPredecessorStateExclusivityCode_eq_quoted
    in hclosedTemplate by exact hPA.
  unfold outerContext0 in hclosedTemplate.
  exact hclosedTemplate.
Qed.

(** Compile the fixed guarded cell after closing its predecessor, retain an
    arbitrary caller prefix, transport the predecessor through the cell's
    standard-axiom extension, and apply one modus ponens.  Keeping this form
    prefix-general is essential in the strong-step shell: its restricted-
    proof and endpoint-rule assumptions are still live when the guarded
    predecessor is constructed. *)
Theorem
    raw_dynamicTruthBooleanGuardedDiagonalPair_on_witnessed_extension_under_caller_prefix :
  forall constructor (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext callerPrefix,
  RawCodedTemplatePrefixAtomicallyAdequate M translation callerPrefix ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix) ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawDynamicTruthBooleanGuardedBranchRootsAt constructor M translation
    baseContext callerPrefix ->
  exists targetWitnessList targetContext pairRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext callerPrefix)
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M constructor)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M constructor)
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros constructor M hPA translation hagreement
    baseWitnessList baseContext callerPrefix hcallerAdequate hadequate
    hbase hroots.
  destruct
    (raw_dynamicTruthBooleanGuardedPredecessorRoot_of_branch_roots_under_template_prefix
      constructor M hPA translation hagreement
      baseWitnessList baseContext callerPrefix hadequate hbase hroots)
    as (predecessorWitnessList & predecessorContext & predecessorRoot &
      hpredecessorWitnessed & hbasePredecessorIncluded & hpredecessor).
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
      M hPA translation hagreement
      predecessorWitnessList predecessorContext
      (dynamicTruthBooleanGuardedConditionalCellFormula constructor)
      hpredecessorWitnessed
      (PA_proves_dynamicTruthBooleanGuardedConditionalCellFormula
        constructor))
    as (cellWitnesses & cellRoot & hcellWitnessed & hcell).
  set (targetWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      cellWitnesses predecessorWitnessList).
  set (targetContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      cellWitnesses predecessorContext).
  assert (hcellNative : RawCodedPALocalProofOf M targetContext
      (rawDynamicTruthBooleanGuardedConditionalCellCode M constructor)
      cellRoot).
  {
    unfold targetContext.
    rewrite (rawTemplateFormula_embedPA hagreement) in hcell.
    rewrite <- rawDynamicTruthBooleanGuardedConditionalCellCode_eq_quoted
      in hcell by exact hPA.
    exact hcell.
  }
  pose proof
    (raw_codedPAAxiomWitnessContext_context_realizable M
      targetWitnessList targetContext hcellWitnessed)
    as htargetRealizable.
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    targetContext callerPrefix
    (rawDynamicTruthBooleanGuardedConditionalCellCode M constructor)
    cellRoot htargetRealizable hcallerAdequate hcellNative)
    as [prefixedCellRoot hprefixedCell].
  assert (hpredecessorTargetIncluded :
      RawContextListIncluded M predecessorContext targetContext).
  {
    unfold targetContext.
    apply raw_standardPAAxiomWitnessPrefixContextCode_target_included.
    exact hPA.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation predecessorWitnessList predecessorContext
      targetWitnessList targetContext callerPrefix
      (rawDynamicTruthBooleanGuardedPredecessorStateExclusivityCode
        M constructor)
      predecessorRoot hpredecessorWitnessed hcellWitnessed
      hpredecessorTargetIncluded hpredecessor)
    as [transportedPredecessorRoot htransportedPredecessor].
  destruct
    (raw_dynamicTruthBooleanGuarded_pair constructor M hPA
      (rawTemplateContextCodeOnTail translation targetContext callerPrefix)
      prefixedCellRoot transportedPredecessorRoot hprefixedCell
      htransportedPredecessor) as [pairRoot hpair].
  exists targetWitnessList, targetContext, pairRoot.
  split; [exact hcellWitnessed |].
  split.
  - intros member hmember.
    exact (hpredecessorTargetIncluded member
      (hbasePredecessorIncluded member hmember)).
  - exact hpair.
Qed.

(** Empty-prefix compatibility endpoint used by the existing local matrix. *)
Theorem raw_dynamicTruthBooleanGuardedDiagonalPair_on_witnessed_extension :
  forall constructor (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext,
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (coqDynamicTruthBooleanGuardedDeepPrefix constructor []) ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawDynamicTruthBooleanGuardedBranchRootsAt constructor M translation
    baseContext [] ->
  exists targetWitnessList targetContext pairRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M targetContext
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M constructor)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M constructor)
          (rawFormulaBotCode M))) pairRoot.
Proof.
  intros constructor M hPA translation hagreement
    baseWitnessList baseContext hadequate hbase hroots.
  destruct
    (raw_dynamicTruthBooleanGuardedDiagonalPair_on_witnessed_extension_under_caller_prefix
      constructor M hPA translation hagreement
      baseWitnessList baseContext []
      (fun formula hin => False_rect _ (in_nil hin))
      hadequate hbase hroots)
    as (targetWitnessList & targetContext & pairRoot &
      htargetWitnessed & hincluded & hpair).
  exists targetWitnessList, targetContext, pairRoot.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  cbn [rawTemplateContextCodeOnTail] in hpair.
  exact hpair.
Qed.

(** Exact two-root endpoint consumed by the predecessor-free matrix.  Each
    constructor may select its own finite standard-axiom extension; the
    completed witnessed-context merge transports both pairs to one literal
    context before the record is formed. *)
Theorem
    raw_dynamicTruthLocalBooleanDiagonalPairRootsAt_of_guarded_branch_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (coqDynamicTruthBooleanGuardedDeepPrefix DTBooleanAnd []) ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (coqDynamicTruthBooleanGuardedDeepPrefix DTBooleanOr []) ->
  RawDynamicTruthBooleanGuardedBranchRootsAt DTBooleanAnd M translation
    baseContext [] ->
  RawDynamicTruthBooleanGuardedBranchRootsAt DTBooleanOr M translation
    baseContext [] ->
  exists targetWitnessList targetContext,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawDynamicTruthLocalBooleanDiagonalPairRootsAt M targetContext.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    hbase handAdequate horAdequate handRoots horRoots.
  destruct
    (raw_dynamicTruthBooleanGuardedDiagonalPair_on_witnessed_extension
      DTBooleanAnd M hPA translation hagreement
      baseWitnessList baseContext handAdequate hbase handRoots)
    as (andWitnessList & andContext & andRoot &
      handWitnessed & hbaseAndIncluded & hand).
  destruct
    (raw_dynamicTruthBooleanGuardedDiagonalPair_on_witnessed_extension
      DTBooleanOr M hPA translation hagreement
      baseWitnessList baseContext horAdequate hbase horRoots)
    as (orWitnessList & orContext & orRoot &
      horWitnessed & hbaseOrIncluded & hor).
  destruct
    (raw_codedPALocalProof_twoWitnessedContexts_commonContext_with_inclusions_complete
      M hPA
      andWitnessList andContext
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanAnd)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanAnd)
          (rawFormulaBotCode M))) andRoot
      orWitnessList orContext
      (rawFormulaImpCode M
        (rawDynamicTruthBooleanSigmaEx8BranchCode M DTBooleanOr)
        (rawFormulaImpCode M
          (rawDynamicTruthBooleanPiEx8BranchCode M DTBooleanOr)
          (rawFormulaBotCode M))) orRoot
      handWitnessed hand horWitnessed hor)
    as (targetWitnessList & targetContext &
      transportedAndRoot & transportedOrRoot & htargetWitnessed &
      handIncluded & horIncluded & htransportedAnd & htransportedOr).
  exists targetWitnessList, targetContext.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (handIncluded member (hbaseAndIncluded member hmember)).
  - split.
    + cbn [rawDynamicTruthBooleanSigmaEx8BranchCode
        rawDynamicTruthBooleanPiEx8BranchCode] in htransportedAnd.
      exists transportedAndRoot. exact htransportedAnd.
    + cbn [rawDynamicTruthBooleanSigmaEx8BranchCode
        rawDynamicTruthBooleanPiEx8BranchCode] in htransportedOr.
      exists transportedOrRoot. exact htransportedOr.
Qed.

End PABoundedRawCodedDynamicTruthBooleanGuardedDiagonalCompilation.
