(**
  Compile guarded implication predecessor exclusivity in its real branch.

  The outer predecessor clause introduces three variables and assumes the
  synchronized Sigma and Pi states.  The implication branch then introduces
  its left and right codes and assumes both the constructor equation and the
  direct-child disjunction.  Only in this five-binder context do the parent
  endpoint invariants imply admissibility of the common child.

  This file fixes that binder layout as finite template syntax and joins the
  guarded child-admissibility compiler with the preceding local exclusivity
  law.  Every proof root is transported to the same retained standard-axiom
  extension before implication or universal introduction is performed.
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
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedTemplateTripleUniversalOpening
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedAssignmentUniversalDefinednessProofCompilation
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthLocalExclusiveTemplateDirectInputs
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthImpGuardedBranchExclusivity
  RawCodedDynamicTruthImpDirectChildAdmissibilityProofCompilation
  RawCodedDynamicTruthImpGuardedChildAdmissibilityCompilation.

Module
  PABoundedRawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation.

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
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedTemplateTripleUniversalOpening.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedAssignmentUniversalDefinednessProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedDynamicTruthImpGuardedBranchExclusivity.
Import
  PABoundedRawCodedDynamicTruthImpDirectChildAdmissibilityProofCompilation.
Import
  PABoundedRawCodedDynamicTruthImpGuardedChildAdmissibilityCompilation.

(** Concrete coordinates below all five predecessor/constructor binders. *)
Definition coqDynamicTruthImpGuardedLevelTerm : TemplateTerm :=
  coqDynamicTruthUpperLevelTerm.
Definition coqDynamicTruthImpGuardedParentTerm : TemplateTerm := ttVar 7.
Definition coqDynamicTruthImpGuardedLeftTerm : TemplateTerm := ttVar 1.
Definition coqDynamicTruthImpGuardedRightTerm : TemplateTerm := ttVar 0.
Definition coqDynamicTruthImpGuardedChildTerm : TemplateTerm := ttVar 2.
Definition coqDynamicTruthImpGuardedAssignmentCodeTerm : TemplateTerm :=
  ttVar 6.
Definition coqDynamicTruthImpGuardedAssignmentStepTerm : TemplateTerm :=
  ttVar 5.

Definition coqDynamicTruthImpGuardedShapeTemplate : TemplateFormula :=
  coqDynamicTruthImpGuardedChildShapeTemplate
    coqDynamicTruthImpGuardedLevelTerm
    coqDynamicTruthImpGuardedParentTerm
    coqDynamicTruthImpGuardedLeftTerm
    coqDynamicTruthImpGuardedRightTerm
    coqDynamicTruthImpGuardedChildTerm.

Definition coqDynamicTruthImpGuardedDirectChildTemplate : TemplateFormula :=
  coqDynamicTruthImpGuardedChildGuardTemplate
    coqDynamicTruthImpGuardedLevelTerm
    coqDynamicTruthImpGuardedParentTerm
    coqDynamicTruthImpGuardedLeftTerm
    coqDynamicTruthImpGuardedRightTerm
    coqDynamicTruthImpGuardedChildTerm.

Definition coqDynamicTruthImpGuardedConstructorBodyTemplate
    : TemplateFormula :=
  tfImp coqDynamicTruthImpGuardedShapeTemplate
    (tfImp coqDynamicTruthImpGuardedDirectChildTemplate tfBot).

Definition coqDynamicTruthImpGuardedPredecessorBodyTemplate
    : TemplateFormula :=
  tfImp (embedPAFormula dynamicTruthPredecessorSigmaStateMemberBodyFormula)
    (tfImp
      (embedPAFormula dynamicTruthPredecessorPiStateMemberBodyFormula)
      (tfAll (tfAll coqDynamicTruthImpGuardedConstructorBodyTemplate))).

Definition coqDynamicTruthImpGuardedPredecessorFormulaTemplate
    : TemplateFormula :=
  tfAll (tfAll (tfAll
    coqDynamicTruthImpGuardedPredecessorBodyTemplate)).

(** The explicit template is definitionally the guarded PA formula. *)
Lemma coqDynamicTruthImpGuardedPredecessorFormulaTemplate_eq_embedPA :
  coqDynamicTruthImpGuardedPredecessorFormulaTemplate =
  embedPAFormula
    dynamicTruthImpGuardedPredecessorStateExclusivityFormula.
Proof.
  unfold coqDynamicTruthImpGuardedPredecessorFormulaTemplate,
    coqDynamicTruthImpGuardedPredecessorBodyTemplate,
    coqDynamicTruthImpGuardedConstructorBodyTemplate,
    coqDynamicTruthImpGuardedShapeTemplate,
    coqDynamicTruthImpGuardedDirectChildTemplate,
    coqDynamicTruthImpGuardedChildShapeTemplate,
    coqDynamicTruthImpGuardedChildGuardTemplate,
    coqDynamicTruthImpGuardedLevelTerm,
    coqDynamicTruthImpGuardedParentTerm,
    coqDynamicTruthImpGuardedLeftTerm,
    coqDynamicTruthImpGuardedRightTerm,
    coqDynamicTruthImpGuardedChildTerm,
    coqDynamicTruthImpDirectChildShapePremiseTemplate,
    coqDynamicTruthImpDirectChildGuardPremiseTemplate,
    coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate,
    templateUniversalOpenManyOrBot,
    dynamicTruthImpDirectChildAdmissibilityCoreFormula,
    dynamicTruthImpDirectChildAdmissibilityCoreBodyFormula,
    dynamicTruthImpGuardedPredecessorStateExclusivityFormula,
    dynamicTruthImpGuardedPredecessorStateExclusivityBodyFormula,
    dynamicTruthImpGuardedConstructorBodyFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst
    templateImpAntecedent templateImpConsequent].
  reflexivity.
Qed.

(** Open the carried local law at child [#2] and assignment [#6,#5]. *)
Definition coqDynamicTruthImpGuardedLocalAdmissibleTemplate
    : TemplateFormula :=
  templateAll3Open coqDynamicTruthLocalAdmissibleTemplate
    coqDynamicTruthImpGuardedChildTerm
    coqDynamicTruthImpGuardedAssignmentCodeTerm
    coqDynamicTruthImpGuardedAssignmentStepTerm.

Definition coqDynamicTruthImpGuardedLocalSigmaEvidenceTemplate
    : TemplateFormula :=
  templateAll3Open coqDynamicTruthLocalSigmaEvidenceTemplate
    coqDynamicTruthImpGuardedChildTerm
    coqDynamicTruthImpGuardedAssignmentCodeTerm
    coqDynamicTruthImpGuardedAssignmentStepTerm.

Definition coqDynamicTruthImpGuardedLocalPiEvidenceTemplate
    : TemplateFormula :=
  templateAll3Open coqDynamicTruthLocalPiEvidenceTemplate
    coqDynamicTruthImpGuardedChildTerm
    coqDynamicTruthImpGuardedAssignmentCodeTerm
    coqDynamicTruthImpGuardedAssignmentStepTerm.

Definition coqDynamicTruthImpGuardedLocalExclusiveBodyTemplate
    : TemplateFormula :=
  templateAll3Open coqDynamicTruthLocalExclusiveBodyTemplate
    coqDynamicTruthImpGuardedChildTerm
    coqDynamicTruthImpGuardedAssignmentCodeTerm
    coqDynamicTruthImpGuardedAssignmentStepTerm.

Lemma coqDynamicTruthImpGuardedLocalExclusiveBodyTemplate_shape :
  coqDynamicTruthImpGuardedLocalExclusiveBodyTemplate =
  tfImp coqDynamicTruthImpGuardedLocalAdmissibleTemplate
    (tfImp coqDynamicTruthImpGuardedLocalSigmaEvidenceTemplate
      (tfImp coqDynamicTruthImpGuardedLocalPiEvidenceTemplate tfBot)).
Proof. reflexivity. Qed.

Definition coqDynamicTruthImpGuardedChildAdmissibleConcreteTemplate
    : TemplateFormula :=
  coqDynamicTruthImpGuardedChildAdmissibleTemplate
    coqDynamicTruthImpGuardedLevelTerm
    coqDynamicTruthImpGuardedParentTerm
    coqDynamicTruthImpGuardedLeftTerm
    coqDynamicTruthImpGuardedRightTerm
    coqDynamicTruthImpGuardedChildTerm
    coqDynamicTruthImpGuardedAssignmentCodeTerm
    coqDynamicTruthImpGuardedAssignmentStepTerm.

Lemma coqDynamicTruthImpGuardedChildAdmissibleConcreteTemplate_eq_local :
  coqDynamicTruthImpGuardedChildAdmissibleConcreteTemplate =
  coqDynamicTruthImpGuardedLocalAdmissibleTemplate.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** Deepest branch prefix: guard is the raw context head, followed by shape,
    then the twice-shifted predecessor states and thrice-shifted caller. *)
Definition coqDynamicTruthImpGuardedDeepPrefix
    (callerPrefix : TemplateContext) : TemplateContext :=
  [coqDynamicTruthImpGuardedDirectChildTemplate;
   coqDynamicTruthImpGuardedShapeTemplate] ++
  templateContextShiftMany 2
    (coqDynamicTruthPredecessorStateTemplateContext ++
      templateContextShiftMany 3 callerPrefix).

(** Two universal introductions across their actual successive contexts.
    This small raw-code kernel complements the existing three-binder helper
    and is independent of the guarded implication application below. *)
Definition rawPALocalProofClose2BetweenRoot
    (M : RawPAModel) (context0 context1 body child : M) : M :=
  rawProofAllIRoot M context0 (rawFormulaAllCode M body)
    (rawProofAllIRoot M context1 body child).

Arguments rawPALocalProofClose2BetweenRoot
  M context0 context1 body child : clear implicits.

Theorem raw_codedPALocalProofOf_close2_between : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context0 context1 context2 body child,
  RawContextShift M context0 context1 ->
  RawContextShift M context1 context2 ->
  RawCodedPALocalProofOf M context2 body child ->
  RawCodedPALocalProofOf M context0
    (rawFormulaAllCode M (rawFormulaAllCode M body))
    (rawPALocalProofClose2BetweenRoot M
      context0 context1 body child).
Proof.
  intros M hPA context0 context1 context2 body child
    hshift01 hshift12 [hcoverage hendpoint].
  pose proof (raw_proofAllI_ruleCoverage M hPA
    context1 context2 body child hshift12 hcoverage hendpoint)
    as hcoverage1.
  pose proof (raw_proofAllI_endpoint M context1 body child)
    as hendpoint1.
  split.
  - exact (raw_proofAllI_ruleCoverage M hPA
      context0 context1 (rawFormulaAllCode M body)
      (rawProofAllIRoot M context1 body child)
      hshift01 hcoverage1 hendpoint1).
  - exact (raw_proofAllI_endpoint M context0
      (rawFormulaAllCode M body)
      (rawProofAllIRoot M context1 body child)).
Qed.

(** End-to-end guarded closure from branch-local parent and row roots.  The
    caller supplies the projected local law, both selected evidence rows,
    and the parent endpoint invariants in the deepest honest context. *)
Theorem
    raw_dynamicTruthImpGuardedPredecessorStateExclusivityRoot_of_branch_roots_under_template_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext callerPrefix
      sourceRoot parentAtomicRoot parentDomainRoot sigmaRoot piRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (coqDynamicTruthImpGuardedDeepPrefix callerPrefix) ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
    (rawTemplateFormula translation
      (tfAll (tfAll (tfAll
        coqDynamicTruthLocalExclusiveBodyTemplate)))) sourceRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
    (rawTemplateFormula translation
      (coqDynamicTruthImpDirectChildAtomicPremiseTemplate
        coqDynamicTruthImpGuardedLevelTerm
        coqDynamicTruthImpGuardedParentTerm
        coqDynamicTruthImpGuardedLeftTerm
        coqDynamicTruthImpGuardedRightTerm
        coqDynamicTruthImpGuardedChildTerm)) parentAtomicRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
    (rawTemplateFormula translation
      (coqDynamicTruthImpDirectChildDomainPremiseTemplate
        coqDynamicTruthImpGuardedLevelTerm
        coqDynamicTruthImpGuardedParentTerm
        coqDynamicTruthImpGuardedLeftTerm
        coqDynamicTruthImpGuardedRightTerm
        coqDynamicTruthImpGuardedChildTerm)) parentDomainRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
    (rawTemplateFormula translation
      coqDynamicTruthImpGuardedLocalSigmaEvidenceTemplate) sigmaRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
    (rawTemplateFormula translation
      coqDynamicTruthImpGuardedLocalPiEvidenceTemplate) piRoot ->
  exists targetWitnessList targetContext predecessorRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        targetContext callerPrefix)
      (rawDynamicTruthImpGuardedPredecessorStateExclusivityCode M)
      predecessorRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    callerPrefix sourceRoot parentAtomicRoot parentDomainRoot
    sigmaRoot piRoot hdeepAdequate hbase hsource
    hparentAtomic hparentDomain hsigma hpi.
  assert (hshapeIn : In coqDynamicTruthImpGuardedShapeTemplate
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)).
  {
    unfold coqDynamicTruthImpGuardedDeepPrefix.
    cbn. auto.
  }
  assert (hguardIn : In coqDynamicTruthImpGuardedDirectChildTemplate
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)).
  {
    unfold coqDynamicTruthImpGuardedDeepPrefix.
    cbn. auto.
  }
  destruct
    (raw_codedPALocalProofOf_dynamicTruthImpGuardedChildAdmissible_of_parent_roots_on_witnessed_extension_under_prefix
      M hPA translation hagreement baseWitnessList baseContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)
      coqDynamicTruthImpGuardedLevelTerm
      coqDynamicTruthImpGuardedParentTerm
      coqDynamicTruthImpGuardedLeftTerm
      coqDynamicTruthImpGuardedRightTerm
      coqDynamicTruthImpGuardedChildTerm
      coqDynamicTruthImpGuardedAssignmentCodeTerm
      coqDynamicTruthImpGuardedAssignmentStepTerm
      parentAtomicRoot parentDomainRoot hdeepAdequate hbase
      hshapeIn hguardIn hparentAtomic hparentDomain)
    as (targetWitnessList & targetContext & admissibleRoot &
      htargetWitnessed & hincluded & hadmissible).
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation targetContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
    (rawTemplateFormula translation
      coqDynamicTruthImpGuardedChildAdmissibleConcreteTemplate)
    admissibleRoot) in hadmissible.
  rewrite coqDynamicTruthImpGuardedChildAdmissibleConcreteTemplate_eq_local
    in hadmissible.
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)
      (rawTemplateFormula translation
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate))))
      sourceRoot hbase htargetWitnessed hincluded hsource)
    as [transportedSourceRoot htransportedSource].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedLocalSigmaEvidenceTemplate)
      sigmaRoot hbase htargetWitnessed hincluded hsigma)
    as [transportedSigmaRoot htransportedSigma].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedLocalPiEvidenceTemplate)
      piRoot hbase htargetWitnessed hincluded hpi)
    as [transportedPiRoot htransportedPi].
  pose proof (raw_template_all3_elimination_chain M translation
    coqDynamicTruthLocalExclusiveBodyTemplate
    coqDynamicTruthImpGuardedChildTerm
    coqDynamicTruthImpGuardedAssignmentCodeTerm
    coqDynamicTruthImpGuardedAssignmentStepTerm) as hchain.
  destruct
    (raw_codedPALocalProofOf_universal_elimination_chain
      M hPA
      (rawTemplateContextCodeOnTail translation targetContext
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
      (rawTemplateFormula translation
        (tfAll (tfAll (tfAll
          coqDynamicTruthLocalExclusiveBodyTemplate))))
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedLocalExclusiveBodyTemplate)
      hchain transportedSourceRoot htransportedSource)
    as [openedRoot hopened].
  rewrite coqDynamicTruthImpGuardedLocalExclusiveBodyTemplate_shape,
    !rawTemplateFormula_imp, rawTemplateFormula_bot in hopened.
  destruct (raw_codedPALocalProofOf_impE3 M hPA
    (rawTemplateContextCodeOnTail translation targetContext
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix))
    (rawTemplateFormula translation
      coqDynamicTruthImpGuardedLocalAdmissibleTemplate)
    (rawTemplateFormula translation
      coqDynamicTruthImpGuardedLocalSigmaEvidenceTemplate)
    (rawTemplateFormula translation
      coqDynamicTruthImpGuardedLocalPiEvidenceTemplate)
    (rawFormulaBotCode M)
    openedRoot admissibleRoot transportedSigmaRoot transportedPiRoot
    hopened hadmissible htransportedSigma htransportedPi)
    as [bottomRoot hbottom].
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
          coqDynamicTruthImpGuardedDirectChildTemplate)
        (rawListNode M
          (rawTemplateFormula translation
            coqDynamicTruthImpGuardedShapeTemplate)
          stateContext2))
      (rawFormulaBotCode M) bottomRoot).
  {
    unfold coqDynamicTruthImpGuardedDeepPrefix in hbottom.
    unfold stateContext2, statePrefix2, statePrefix1, statePrefix, prefix3.
    cbn [List.app rawTemplateContextCodeOnTail
      templateContextShiftMany] in hbottom |- *.
    exact hbottom.
  }
  set (guardImpRoot := rawProofImpIRoot M
    (rawListNode M
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedShapeTemplate) stateContext2)
    (rawTemplateFormula translation
      coqDynamicTruthImpGuardedDirectChildTemplate)
    (rawFormulaBotCode M) bottomRoot).
  assert (hguardImp : RawCodedPALocalProofOf M
      (rawListNode M
        (rawTemplateFormula translation
          coqDynamicTruthImpGuardedShapeTemplate) stateContext2)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqDynamicTruthImpGuardedDirectChildTemplate)
        (rawFormulaBotCode M)) guardImpRoot).
  {
    unfold guardImpRoot.
    exact (raw_codedPALocalProofOf_impI M hPA
      (rawListNode M
        (rawTemplateFormula translation
          coqDynamicTruthImpGuardedShapeTemplate) stateContext2)
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedDirectChildTemplate)
      (rawFormulaBotCode M) bottomRoot hbottomAtHeads).
  }
  set (constructorBodyRoot := rawProofImpIRoot M stateContext2
    (rawTemplateFormula translation
      coqDynamicTruthImpGuardedShapeTemplate)
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedDirectChildTemplate)
      (rawFormulaBotCode M)) guardImpRoot).
  assert (hconstructorBody : RawCodedPALocalProofOf M stateContext2
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqDynamicTruthImpGuardedShapeTemplate)
        (rawFormulaImpCode M
          (rawTemplateFormula translation
            coqDynamicTruthImpGuardedDirectChildTemplate)
          (rawFormulaBotCode M))) constructorBodyRoot).
  {
    unfold constructorBodyRoot.
    exact (raw_codedPALocalProofOf_impI M hPA stateContext2
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedShapeTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqDynamicTruthImpGuardedDirectChildTemplate)
        (rawFormulaBotCode M)) guardImpRoot hguardImp).
  }
  assert (hconstructorTemplate : RawCodedPALocalProofOf M
      stateContext2
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedConstructorBodyTemplate)
      constructorBodyRoot).
  {
    unfold coqDynamicTruthImpGuardedConstructorBodyTemplate.
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
      coqDynamicTruthImpGuardedConstructorBodyTemplate)
    constructorBodyRoot hstateShift01 hstateShift12
    hconstructorTemplate) as hall2.
  set (all2Root := rawPALocalProofClose2BetweenRoot M
    stateContext0 stateContext1
    (rawTemplateFormula translation
      coqDynamicTruthImpGuardedConstructorBodyTemplate)
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
          coqDynamicTruthImpGuardedConstructorBodyTemplate)))
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
        coqDynamicTruthImpGuardedConstructorBodyTemplate)))
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
            coqDynamicTruthImpGuardedConstructorBodyTemplate))))
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
          coqDynamicTruthImpGuardedConstructorBodyTemplate)))
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
          coqDynamicTruthImpGuardedConstructorBodyTemplate))))
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
              coqDynamicTruthImpGuardedConstructorBodyTemplate)))))
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
            coqDynamicTruthImpGuardedConstructorBodyTemplate))))
      piImpRoot hpiImp).
  }
  assert (hstateTemplate : RawCodedPALocalProofOf M outer3Context
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedPredecessorBodyTemplate)
      stateBodyRoot).
  {
    unfold coqDynamicTruthImpGuardedPredecessorBodyTemplate.
    rewrite !rawTemplateFormula_imp, !rawTemplateFormula_all.
    exact hstateBody.
  }
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
      coqDynamicTruthImpGuardedPredecessorBodyTemplate)
    stateBodyRoot houterShift01 houterShift12 houterShift23
    hstateTemplate) as hclosed.
  exists targetWitnessList, targetContext,
    (rawPALocalProofClose3BetweenRoot M
      outerContext0 outerContext1 outerContext2
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedPredecessorBodyTemplate)
      stateBodyRoot).
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  assert (hclosedTemplate : RawCodedPALocalProofOf M outerContext0
      (rawTemplateFormula translation
        coqDynamicTruthImpGuardedPredecessorFormulaTemplate)
      (rawPALocalProofClose3BetweenRoot M
        outerContext0 outerContext1 outerContext2
        (rawTemplateFormula translation
          coqDynamicTruthImpGuardedPredecessorBodyTemplate)
        stateBodyRoot)).
  {
    unfold coqDynamicTruthImpGuardedPredecessorFormulaTemplate.
    rewrite !rawTemplateFormula_all.
    exact hclosed.
  }
  rewrite coqDynamicTruthImpGuardedPredecessorFormulaTemplate_eq_embedPA
    in hclosedTemplate.
  rewrite (rawTemplateFormula_embedPA hagreement
    dynamicTruthImpGuardedPredecessorStateExclusivityFormula)
    in hclosedTemplate.
  rewrite <- rawDynamicTruthImpGuardedPredecessorStateExclusivityCode_eq_quoted
    in hclosedTemplate by exact hPA.
  unfold outerContext0 in hclosedTemplate.
  exact hclosedTemplate.
Qed.

End
  PABoundedRawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation.
