(**
  Branch-local admissibility for a direct implication child.

  The predecessor-state collision is opened before the implication's two
  constructor witnesses.  At that point the common predecessor child is
  [#2], the enclosing assignment coordinates are [#6,#5], and the parent
  formula is [#7].  This module compiles admissibility only in that honest
  branch context: the implication equation and direct-child disjunction are
  literal assumptions, while parent atomic adequacy and rank membership are
  supplied by the restricted-proof endpoint compiler.

  The constructor theorem and the universal assignment theorem may select
  different finite batches of standard PA axioms.  We deliberately run them
  successively, transport the constructor conclusion to the final witnessed
  tail, and only then form the three-part local admissibility conjunction.
  Thus no proof root is silently reused across unequal represented contexts.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofAndIntroduction
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedAssignmentUniversalDefinednessProofCompilation
  RawCodedDynamicTruthImpDirectChildAdmissibilityProofCompilation.

Module
  PABoundedRawCodedDynamicTruthImpGuardedChildAdmissibilityCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedAssignmentUniversalDefinednessProofCompilation.
Import
  PABoundedRawCodedDynamicTruthImpDirectChildAdmissibilityProofCompilation.

(** The exact constructor guards after the two left/right binders open. *)
Definition coqDynamicTruthImpGuardedChildShapeTemplate
    (level parent left right child : TemplateTerm) : TemplateFormula :=
  coqDynamicTruthImpDirectChildShapePremiseTemplate
    level parent left right child.

Definition coqDynamicTruthImpGuardedChildGuardTemplate
    (level parent left right child : TemplateTerm) : TemplateFormula :=
  coqDynamicTruthImpDirectChildGuardPremiseTemplate
    level parent left right child.

(** Project the two leaves of the constructor-only result structurally.
    The fallback is unreachable by the shape lemma below, but keeping these
    definitions total avoids baking a proof argument into every client. *)
Definition templateAndLeftOrBotLocal (input : TemplateFormula)
    : TemplateFormula :=
  match input with
  | tfAnd lhs _ => lhs
  | _ => tfBot
  end.

Definition templateAndRightOrBotLocal (input : TemplateFormula)
    : TemplateFormula :=
  match input with
  | tfAnd _ rhs => rhs
  | _ => tfBot
  end.

Definition coqDynamicTruthImpGuardedChildAtomicTemplate
    (level parent left right child : TemplateTerm) : TemplateFormula :=
  templateAndLeftOrBotLocal
    (coqDynamicTruthImpDirectChildAdmissibilityCoreConclusionTemplate
      level parent left right child).

Definition coqDynamicTruthImpGuardedChildAssignmentTemplate
    (assignmentCode assignmentStep child : TemplateTerm)
    : TemplateFormula :=
  coqAssignmentUniversalDefinednessInstanceTemplate
    assignmentCode assignmentStep child.

Definition coqDynamicTruthImpGuardedChildDomainTemplate
    (level parent left right child : TemplateTerm) : TemplateFormula :=
  templateAndRightOrBotLocal
    (coqDynamicTruthImpDirectChildAdmissibilityCoreConclusionTemplate
      level parent left right child).

Definition coqDynamicTruthImpGuardedChildAdmissibleTemplate
    (level parent left right child assignmentCode assignmentStep
      : TemplateTerm)
    : TemplateFormula :=
  tfAnd
    (coqDynamicTruthImpGuardedChildAtomicTemplate
      level parent left right child)
    (tfAnd
      (coqDynamicTruthImpGuardedChildAssignmentTemplate
        assignmentCode assignmentStep child)
      (coqDynamicTruthImpGuardedChildDomainTemplate
        level parent left right child)).

(** The conclusion of the constructor-only core is exactly the atomic and
    domain pair needed below.  Naming this definitional identity makes the
    two projections robust against later changes to the application code. *)
Lemma coqDynamicTruthImpDirectChildAdmissibilityCoreConclusionTemplate_shape :
  forall level parent left right child,
  coqDynamicTruthImpDirectChildAdmissibilityCoreConclusionTemplate
      level parent left right child =
  tfAnd
    (coqDynamicTruthImpGuardedChildAtomicTemplate
      level parent left right child)
    (coqDynamicTruthImpGuardedChildDomainTemplate
      level parent left right child).
Proof.
  intros level parent left right child.
  unfold coqDynamicTruthImpGuardedChildAtomicTemplate,
    coqDynamicTruthImpGuardedChildDomainTemplate,
    templateAndLeftOrBotLocal, templateAndRightOrBotLocal,
    coqDynamicTruthImpDirectChildAdmissibilityCoreConclusionTemplate,
    coqDynamicTruthImpDirectChildAdmissibilityCoreInstanceTemplate,
    templateUniversalOpenManyOrBot,
    dynamicTruthImpDirectChildAdmissibilityCoreFormula,
    dynamicTruthImpDirectChildAdmissibilityCoreBodyFormula.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst templateImpConsequent].
  reflexivity.
Qed.

Lemma coqDynamicTruthImpDirectChildShapePremiseTemplate_view :
  forall level parent left right child,
  coqDynamicTruthImpDirectChildShapePremiseTemplate
      level parent left right child =
  coqDynamicTruthImpGuardedChildShapeTemplate
    level parent left right child.
Proof.
  reflexivity.
Qed.

Lemma coqDynamicTruthImpDirectChildGuardPremiseTemplate_view :
  forall level parent left right child,
  coqDynamicTruthImpDirectChildGuardPremiseTemplate
      level parent left right child =
  coqDynamicTruthImpGuardedChildGuardTemplate
    level parent left right child.
Proof.
  reflexivity.
Qed.

(** Compile full child admissibility under any adequate prefix containing
    the two constructor guards.  Parent atomic/domain proofs need only exist
    in that branch context; the theorem does not demand them before the
    implication witnesses have been opened. *)
Theorem
    raw_codedPALocalProofOf_dynamicTruthImpGuardedChildAdmissible_of_parent_roots_on_witnessed_extension_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext prefix
      level parent left right child assignmentCode assignmentStep
      parentAtomicRoot parentDomainRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  In (coqDynamicTruthImpGuardedChildShapeTemplate
      level parent left right child)
    prefix ->
  In (coqDynamicTruthImpGuardedChildGuardTemplate
      level parent left right child)
    prefix ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthImpDirectChildAtomicPremiseTemplate
        level parent left right child)) parentAtomicRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthImpDirectChildDomainPremiseTemplate
        level parent left right child)) parentDomainRoot ->
  exists targetWitnessList targetContext resultRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawTemplateFormula translation
        (coqDynamicTruthImpGuardedChildAdmissibleTemplate
          level parent left right child assignmentCode assignmentStep))
      resultRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext prefix
    level parent left right child assignmentCode assignmentStep
    parentAtomicRoot parentDomainRoot hprefix hbase
    hshapeIn hguardIn hparentAtomic hparentDomain.
  pose proof
    (raw_templateAssumptionOnPAAxiomContext_localProof
      M hPA translation baseWitnessList baseContext prefix
      (coqDynamicTruthImpGuardedChildShapeTemplate
        level parent left right child)
      hbase hshapeIn) as hshape.
  pose proof
    (raw_templateAssumptionOnPAAxiomContext_localProof
      M hPA translation baseWitnessList baseContext prefix
      (coqDynamicTruthImpGuardedChildGuardTemplate
        level parent left right child)
      hbase hguardIn) as hguard.
  rewrite <- (coqDynamicTruthImpDirectChildShapePremiseTemplate_view
    level parent left right child) in hshape.
  rewrite <- (coqDynamicTruthImpDirectChildGuardPremiseTemplate_view
    level parent left right child) in hguard.
  destruct
    (raw_codedPALocalProofOf_dynamicTruthImpDirectChildAdmissibilityCore_of_roots_on_witnessed_extension_under_prefix
      M hPA translation hagreement baseWitnessList baseContext prefix
      level parent left right child
      parentAtomicRoot parentDomainRoot
      (rawTemplateProofCodeOnTail translation baseContext
        (trpAss prefix
          (coqDynamicTruthImpGuardedChildShapeTemplate
            level parent left right child)))
      (rawTemplateProofCodeOnTail translation baseContext
        (trpAss prefix
          (coqDynamicTruthImpGuardedChildGuardTemplate
            level parent left right child)))
      hprefix hbase hparentAtomic hparentDomain hshape hguard)
    as (coreWitnesses & coreRoot & hcoreWitnessed &
      hbaseCoreIncluded & hcore).
  set (coreWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      coreWitnesses baseWitnessList).
  set (coreContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      coreWitnesses baseContext).
  destruct
    (raw_codedPALocalProofOf_assignmentUniversalDefinedness_instance_on_witnessed_tail_under_prefix
      M hPA translation hagreement coreWitnessList coreContext prefix
      assignmentCode assignmentStep child hprefix hcoreWitnessed)
    as (assignmentWitnesses & assignmentRoot & hfinalWitnessed &
      hassignment).
  set (targetWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      assignmentWitnesses coreWitnessList).
  set (targetContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      assignmentWitnesses coreContext).
  assert (hcoreFinalIncluded :
      RawContextListIncluded M coreContext targetContext).
  {
    unfold targetContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA assignmentWitnesses coreContext).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation coreWitnessList coreContext
      targetWitnessList targetContext prefix
      (rawTemplateFormula translation
        (coqDynamicTruthImpDirectChildAdmissibilityCoreConclusionTemplate
          level parent left right child))
      coreRoot hcoreWitnessed hfinalWitnessed hcoreFinalIncluded hcore)
    as [transportedCoreRoot htransportedCore].
  rewrite
    (coqDynamicTruthImpDirectChildAdmissibilityCoreConclusionTemplate_shape
      level parent left right child) in htransportedCore.
  rewrite rawTemplateFormula_and in htransportedCore.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA
    (rawTemplateContextCodeOnTail translation targetContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthImpGuardedChildAtomicTemplate
        level parent left right child))
    (rawTemplateFormula translation
      (coqDynamicTruthImpGuardedChildDomainTemplate
        level parent left right child))
    transportedCoreRoot htransportedCore) as hchildAtomic.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA
    (rawTemplateContextCodeOnTail translation targetContext prefix)
    (rawTemplateFormula translation
      (coqDynamicTruthImpGuardedChildAtomicTemplate
        level parent left right child))
    (rawTemplateFormula translation
      (coqDynamicTruthImpGuardedChildDomainTemplate
        level parent left right child))
    transportedCoreRoot htransportedCore) as hchildDomain.
  lazymatch type of hchildAtomic with
  | RawCodedPALocalProofOf _ _ _ ?childAtomicRoot =>
      lazymatch type of hchildDomain with
      | RawCodedPALocalProofOf _ _ _ ?childDomainRoot =>
          pose proof (raw_codedPALocalProofOf_andI M hPA
            (rawTemplateContextCodeOnTail translation targetContext prefix)
            (rawTemplateFormula translation
              (coqDynamicTruthImpGuardedChildAssignmentTemplate
                assignmentCode assignmentStep child))
            (rawTemplateFormula translation
              (coqDynamicTruthImpGuardedChildDomainTemplate
                level parent left right child))
            assignmentRoot childDomainRoot hassignment hchildDomain)
            as hassignmentAndDomain;
          lazymatch type of hassignmentAndDomain with
          | RawCodedPALocalProofOf _ _ _ ?assignmentAndDomainRoot =>
              pose proof (raw_codedPALocalProofOf_andI M hPA
                (rawTemplateContextCodeOnTail translation
                  targetContext prefix)
                (rawTemplateFormula translation
                  (coqDynamicTruthImpGuardedChildAtomicTemplate
                    level parent left right child))
                (rawFormulaAndCode M
                  (rawTemplateFormula translation
                    (coqDynamicTruthImpGuardedChildAssignmentTemplate
                      assignmentCode assignmentStep child))
                  (rawTemplateFormula translation
                    (coqDynamicTruthImpGuardedChildDomainTemplate
                      level parent left right child)))
                childAtomicRoot assignmentAndDomainRoot
                hchildAtomic hassignmentAndDomain) as hresult;
              lazymatch type of hresult with
              | RawCodedPALocalProofOf _ _ _ ?resultRoot =>
          exists targetWitnessList, targetContext, resultRoot;
          split; [exact hfinalWitnessed |];
          split
              end
          end
      end
  end.
  - intros member hmember.
    exact (hcoreFinalIncluded member
      (hbaseCoreIncluded member hmember)).
  - unfold coqDynamicTruthImpGuardedChildAdmissibleTemplate in *.
    rewrite !rawTemplateFormula_and in *.
    exact hresult.
Qed.

End
  PABoundedRawCodedDynamicTruthImpGuardedChildAdmissibilityCompilation.
