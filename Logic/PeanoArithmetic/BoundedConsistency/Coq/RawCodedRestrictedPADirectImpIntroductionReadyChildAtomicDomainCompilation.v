(**
  Compile the Imp-I antecedent's arithmetic admissibility core in the
  literal direct ready context.

  The ready context already contains two facts about the parent formula:

  - the eight-times-renamed admissibility assumption for the parent; and
  - the Imp-I case package, whose formula-code projection says that the
    parent is the implication with displayed antecedent [#6] and consequent
    [#5].

  Atomic adequacy and rank-domain totality therefore pass to the antecedent
  by the general direct implication-child theorem.  The remaining direct-
  child guard is the reflexive left choice [#6 = #6], compiled here as an
  actual represented Eq-Refl/Or-I proof.  No Sigma/Pi state atom and no
  proof-producing callback is assumed.

  The arithmetic inheritance theorem may allocate a finite standard batch
  of PA-axiom witnesses.  The public result retains that exact batch, base
  context inclusion, and the two projected roots in one literal ready
  prefix.  This is the context-safe prerequisite for opening the aligned
  local decision law at the Imp-I coordinates [#6,#9,#8].
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateFormulaAtomicAdequacy
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateProjectionSchemas
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedDynamicTruthImpDirectChildAdmissibilityProofCompilation
  RawCodedDynamicTruthImpGuardedChildAdmissibilityCompilation
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase.

Module
  PABoundedRawCodedRestrictedPADirectImpIntroductionReadyChildAtomicDomainCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateFormulaAtomicAdequacy.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedDynamicTruthImpDirectChildAdmissibilityProofCompilation.
Import PABoundedRawCodedDynamicTruthImpGuardedChildAdmissibilityCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectImpIntroductionCase.

(** The exact ready prefix consumed by the positive Imp-I split. *)
Definition coqRestrictedPADirectImpIntroductionReadyPrefix
    : TemplateContext :=
  coqRestrictedPADirectStrongStepImpIntroductionReadyContext [].

(** The five terms used to instantiate the generic implication-child law.
    The parent is the outer conclusion below the eight rule witnesses; the
    common child is deliberately the left implication child. *)
Definition coqRestrictedPADirectImpIntroductionReadyChildLevelTerm
    : TemplateTerm :=
  coqRestrictedPASoundnessLowerLevelTerm.

Definition coqRestrictedPADirectImpIntroductionReadyChildParentTerm
    : TemplateTerm :=
  coqRestrictedPADirectAssumptionOuterConclusionTerm.

Definition coqRestrictedPADirectImpIntroductionReadyChildLeftTerm
    : TemplateTerm := ttVar 6.

Definition coqRestrictedPADirectImpIntroductionReadyChildRightTerm
    : TemplateTerm := ttVar 5.

Definition coqRestrictedPADirectImpIntroductionReadyChildTerm
    : TemplateTerm := ttVar 6.

(** Parent premises expected by the generic child-inheritance theorem. *)
Definition coqRestrictedPADirectImpIntroductionReadyParentAtomicTemplate
    : TemplateFormula :=
  coqDynamicTruthImpDirectChildAtomicPremiseTemplate
    coqRestrictedPADirectImpIntroductionReadyChildLevelTerm
    coqRestrictedPADirectImpIntroductionReadyChildParentTerm
    coqRestrictedPADirectImpIntroductionReadyChildLeftTerm
    coqRestrictedPADirectImpIntroductionReadyChildRightTerm
    coqRestrictedPADirectImpIntroductionReadyChildTerm.

Definition coqRestrictedPADirectImpIntroductionReadyParentDomainTemplate
    : TemplateFormula :=
  coqDynamicTruthImpDirectChildDomainPremiseTemplate
    coqRestrictedPADirectImpIntroductionReadyChildLevelTerm
    coqRestrictedPADirectImpIntroductionReadyChildParentTerm
    coqRestrictedPADirectImpIntroductionReadyChildLeftTerm
    coqRestrictedPADirectImpIntroductionReadyChildRightTerm
    coqRestrictedPADirectImpIntroductionReadyChildTerm.

Definition coqRestrictedPADirectImpIntroductionReadyParentAssignmentTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    (embedPAFormula
      (codedAssignmentDefinedThroughTermAt
        (tVar 1) (tVar 0) (tVar 2))).

Definition coqRestrictedPADirectImpIntroductionReadyCommonCoverageTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessCommonCoverageTemplate.

(** The inherited parent admissibility assumption has precisely the nested
    conjunction used by the three projection roots below.  Keeping this as
    an explicit finite syntax lemma makes it impossible to project a child
    fact accidentally: both displayed leaves still concern the parent
    conclusion [#10]. *)
Lemma coqRestrictedPADirectImpIntroductionReadyDeepAdmissible_shape :
  coqRestrictedPADirectAssumptionDeepAdmissibleTemplate =
  tfAnd
    (tfAnd
      coqRestrictedPADirectImpIntroductionReadyParentAtomicTemplate
      (tfAnd
        coqRestrictedPADirectImpIntroductionReadyParentAssignmentTemplate
        coqRestrictedPADirectImpIntroductionReadyParentDomainTemplate))
    coqRestrictedPADirectImpIntroductionReadyCommonCoverageTemplate.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The constructor equation already projected by the direct Imp-I case is
    exactly the parent-shape premise of the generic child theorem. *)
Definition coqRestrictedPADirectImpIntroductionReadyChildShapeTemplate
    : TemplateFormula :=
  coqDynamicTruthImpDirectChildShapePremiseTemplate
    coqRestrictedPADirectImpIntroductionReadyChildLevelTerm
    coqRestrictedPADirectImpIntroductionReadyChildParentTerm
    coqRestrictedPADirectImpIntroductionReadyChildLeftTerm
    coqRestrictedPADirectImpIntroductionReadyChildRightTerm
    coqRestrictedPADirectImpIntroductionReadyChildTerm.

Lemma coqRestrictedPADirectImpIntroductionReadyChildShape_view :
  coqRestrictedPADirectImpIntroductionReadyChildShapeTemplate =
  coqRestrictedPADirectImpIntroductionFormulaCodeTemplate.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** Selecting the antecedent as the common child reduces the direct-child
    guard to a disjunction whose left equality is reflexive. *)
Definition coqRestrictedPADirectImpIntroductionReadyChildGuardTemplate
    : TemplateFormula :=
  coqDynamicTruthImpDirectChildGuardPremiseTemplate
    coqRestrictedPADirectImpIntroductionReadyChildLevelTerm
    coqRestrictedPADirectImpIntroductionReadyChildParentTerm
    coqRestrictedPADirectImpIntroductionReadyChildLeftTerm
    coqRestrictedPADirectImpIntroductionReadyChildRightTerm
    coqRestrictedPADirectImpIntroductionReadyChildTerm.

Lemma coqRestrictedPADirectImpIntroductionReadyChildGuard_view :
  coqRestrictedPADirectImpIntroductionReadyChildGuardTemplate =
  tfOr
    (tfEq coqRestrictedPADirectImpIntroductionReadyChildLeftTerm
      coqRestrictedPADirectImpIntroductionReadyChildLeftTerm)
    (tfEq coqRestrictedPADirectImpIntroductionReadyChildLeftTerm
      coqRestrictedPADirectImpIntroductionReadyChildRightTerm).
Proof.
  vm_compute.
  reflexivity.
Qed.

(** Exact child leaves returned publicly.  These aliases are written through
    the general child theorem so the final conjunction-shape lemma can reuse
    its audited structural projection. *)
Definition coqRestrictedPADirectImpIntroductionReadyChildAtomicTemplate
    : TemplateFormula :=
  coqDynamicTruthImpGuardedChildAtomicTemplate
    coqRestrictedPADirectImpIntroductionReadyChildLevelTerm
    coqRestrictedPADirectImpIntroductionReadyChildParentTerm
    coqRestrictedPADirectImpIntroductionReadyChildLeftTerm
    coqRestrictedPADirectImpIntroductionReadyChildRightTerm
    coqRestrictedPADirectImpIntroductionReadyChildTerm.

Definition coqRestrictedPADirectImpIntroductionReadyChildDomainTemplate
    : TemplateFormula :=
  coqDynamicTruthImpGuardedChildDomainTemplate
    coqRestrictedPADirectImpIntroductionReadyChildLevelTerm
    coqRestrictedPADirectImpIntroductionReadyChildParentTerm
    coqRestrictedPADirectImpIntroductionReadyChildLeftTerm
    coqRestrictedPADirectImpIntroductionReadyChildRightTerm
    coqRestrictedPADirectImpIntroductionReadyChildTerm.

Lemma coqRestrictedPADirectImpIntroductionReadyChildAtomic_view :
  coqRestrictedPADirectImpIntroductionReadyChildAtomicTemplate =
  embedPAFormula
    (codedFormulaAtomicallyAdequateTermAt (tVar 6)).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma coqRestrictedPADirectImpIntroductionReadyChildDomain_view :
  coqRestrictedPADirectImpIntroductionReadyChildDomainTemplate =
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetFormulaQuantifierBoundedContext (tVar 6)).
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma coqRestrictedPADirectImpIntroductionReadyChildCoreConclusion_shape :
  coqDynamicTruthImpDirectChildAdmissibilityCoreConclusionTemplate
      coqRestrictedPADirectImpIntroductionReadyChildLevelTerm
      coqRestrictedPADirectImpIntroductionReadyChildParentTerm
      coqRestrictedPADirectImpIntroductionReadyChildLeftTerm
      coqRestrictedPADirectImpIntroductionReadyChildRightTerm
      coqRestrictedPADirectImpIntroductionReadyChildTerm =
  tfAnd
    coqRestrictedPADirectImpIntroductionReadyChildAtomicTemplate
    coqRestrictedPADirectImpIntroductionReadyChildDomainTemplate.
Proof.
  exact
    (coqDynamicTruthImpDirectChildAdmissibilityCoreConclusionTemplate_shape
      coqRestrictedPADirectImpIntroductionReadyChildLevelTerm
      coqRestrictedPADirectImpIntroductionReadyChildParentTerm
      coqRestrictedPADirectImpIntroductionReadyChildLeftTerm
      coqRestrictedPADirectImpIntroductionReadyChildRightTerm
      coqRestrictedPADirectImpIntroductionReadyChildTerm).
Qed.

(** ------------------------------------------------------------------
    Finite ready-context proof trees. *)

Lemma coqRestrictedPADirectImpIntroductionReady_deepAdmissible_member :
  In coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
    coqRestrictedPADirectImpIntroductionReadyPrefix.
Proof.
  unfold coqRestrictedPADirectImpIntroductionReadyPrefix,
    coqRestrictedPADirectStrongStepImpIntroductionReadyContext,
    coqRestrictedPADirectStrongStepImpIntroductionAdmissibleContext.
  right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectImpIntroductionReady_case_member :
  In coqRestrictedPADirectImpIntroductionCaseTemplate
    coqRestrictedPADirectImpIntroductionReadyPrefix.
Proof.
  unfold coqRestrictedPADirectImpIntroductionReadyPrefix,
    coqRestrictedPADirectStrongStepImpIntroductionReadyContext,
    coqRestrictedPADirectStrongStepImpIntroductionAdmissibleContext,
    coqRestrictedPADirectStrongStepImpIntroductionCaseContext.
  right. right. left. reflexivity.
Qed.

Definition coqRestrictedPADirectImpIntroductionReadyAdmissibleRoot
    : TemplateRawProof :=
  trpAss coqRestrictedPADirectImpIntroductionReadyPrefix
    coqRestrictedPADirectAssumptionDeepAdmissibleTemplate.

Definition coqRestrictedPADirectImpIntroductionReadyAdmissibleCoreRoot
    : TemplateRawProof :=
  trpAndE1 coqRestrictedPADirectImpIntroductionReadyPrefix
    (tfAnd
      coqRestrictedPADirectImpIntroductionReadyParentAtomicTemplate
      (tfAnd
        coqRestrictedPADirectImpIntroductionReadyParentAssignmentTemplate
        coqRestrictedPADirectImpIntroductionReadyParentDomainTemplate))
    coqRestrictedPADirectImpIntroductionReadyCommonCoverageTemplate
    coqRestrictedPADirectImpIntroductionReadyAdmissibleRoot.

Definition coqRestrictedPADirectImpIntroductionReadyParentAtomicRoot
    : TemplateRawProof :=
  trpAndE1 coqRestrictedPADirectImpIntroductionReadyPrefix
    coqRestrictedPADirectImpIntroductionReadyParentAtomicTemplate
    (tfAnd
      coqRestrictedPADirectImpIntroductionReadyParentAssignmentTemplate
      coqRestrictedPADirectImpIntroductionReadyParentDomainTemplate)
    coqRestrictedPADirectImpIntroductionReadyAdmissibleCoreRoot.

Definition coqRestrictedPADirectImpIntroductionReadyAssignmentDomainRoot
    : TemplateRawProof :=
  trpAndE2 coqRestrictedPADirectImpIntroductionReadyPrefix
    coqRestrictedPADirectImpIntroductionReadyParentAtomicTemplate
    (tfAnd
      coqRestrictedPADirectImpIntroductionReadyParentAssignmentTemplate
      coqRestrictedPADirectImpIntroductionReadyParentDomainTemplate)
    coqRestrictedPADirectImpIntroductionReadyAdmissibleCoreRoot.

Definition coqRestrictedPADirectImpIntroductionReadyParentDomainRoot
    : TemplateRawProof :=
  trpAndE2 coqRestrictedPADirectImpIntroductionReadyPrefix
    coqRestrictedPADirectImpIntroductionReadyParentAssignmentTemplate
    coqRestrictedPADirectImpIntroductionReadyParentDomainTemplate
    coqRestrictedPADirectImpIntroductionReadyAssignmentDomainRoot.

Lemma coqRestrictedPADirectImpIntroductionReadyAdmissibleRoot_valid :
  TemplateRawDerives coqRestrictedPADirectImpIntroductionReadyPrefix
    coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
    coqRestrictedPADirectImpIntroductionReadyAdmissibleRoot.
Proof.
  apply templateRawDerives_assumption.
  exact coqRestrictedPADirectImpIntroductionReady_deepAdmissible_member.
Qed.

Lemma coqRestrictedPADirectImpIntroductionReadyAdmissibleCoreRoot_valid :
  TemplateRawDerives coqRestrictedPADirectImpIntroductionReadyPrefix
    (tfAnd
      coqRestrictedPADirectImpIntroductionReadyParentAtomicTemplate
      (tfAnd
        coqRestrictedPADirectImpIntroductionReadyParentAssignmentTemplate
        coqRestrictedPADirectImpIntroductionReadyParentDomainTemplate))
    coqRestrictedPADirectImpIntroductionReadyAdmissibleCoreRoot.
Proof.
  unfold coqRestrictedPADirectImpIntroductionReadyAdmissibleCoreRoot.
  apply templateAndLeftFrom_derives.
  rewrite <-
    coqRestrictedPADirectImpIntroductionReadyDeepAdmissible_shape.
  exact coqRestrictedPADirectImpIntroductionReadyAdmissibleRoot_valid.
Qed.

Lemma coqRestrictedPADirectImpIntroductionReadyParentAtomicRoot_valid :
  TemplateRawDerives coqRestrictedPADirectImpIntroductionReadyPrefix
    coqRestrictedPADirectImpIntroductionReadyParentAtomicTemplate
    coqRestrictedPADirectImpIntroductionReadyParentAtomicRoot.
Proof.
  unfold coqRestrictedPADirectImpIntroductionReadyParentAtomicRoot.
  apply templateAndLeftFrom_derives.
  exact coqRestrictedPADirectImpIntroductionReadyAdmissibleCoreRoot_valid.
Qed.

Lemma coqRestrictedPADirectImpIntroductionReadyAssignmentDomainRoot_valid :
  TemplateRawDerives coqRestrictedPADirectImpIntroductionReadyPrefix
    (tfAnd
      coqRestrictedPADirectImpIntroductionReadyParentAssignmentTemplate
      coqRestrictedPADirectImpIntroductionReadyParentDomainTemplate)
    coqRestrictedPADirectImpIntroductionReadyAssignmentDomainRoot.
Proof.
  unfold coqRestrictedPADirectImpIntroductionReadyAssignmentDomainRoot.
  apply templateAndRightFrom_derives.
  exact coqRestrictedPADirectImpIntroductionReadyAdmissibleCoreRoot_valid.
Qed.

Lemma coqRestrictedPADirectImpIntroductionReadyParentDomainRoot_valid :
  TemplateRawDerives coqRestrictedPADirectImpIntroductionReadyPrefix
    coqRestrictedPADirectImpIntroductionReadyParentDomainTemplate
    coqRestrictedPADirectImpIntroductionReadyParentDomainRoot.
Proof.
  unfold coqRestrictedPADirectImpIntroductionReadyParentDomainRoot.
  apply templateAndRightFrom_derives.
  exact
    coqRestrictedPADirectImpIntroductionReadyAssignmentDomainRoot_valid.
Qed.

Definition coqRestrictedPADirectImpIntroductionReadyChildShapeRoot
    : TemplateRawProof :=
  coqRestrictedPADirectImpIntroductionFormulaCodeRootAt
    coqRestrictedPADirectImpIntroductionReadyPrefix.

Lemma coqRestrictedPADirectImpIntroductionReadyChildShapeRoot_valid :
  TemplateRawDerives coqRestrictedPADirectImpIntroductionReadyPrefix
    coqRestrictedPADirectImpIntroductionReadyChildShapeTemplate
    coqRestrictedPADirectImpIntroductionReadyChildShapeRoot.
Proof.
  rewrite coqRestrictedPADirectImpIntroductionReadyChildShape_view.
  unfold coqRestrictedPADirectImpIntroductionReadyChildShapeRoot.
  apply coqRestrictedPADirectImpIntroductionFormulaCodeRootAt_valid.
  exact coqRestrictedPADirectImpIntroductionReady_case_member.
Qed.

Definition coqRestrictedPADirectImpIntroductionReadyChildGuardRoot
    : TemplateRawProof :=
  trpOrI1 coqRestrictedPADirectImpIntroductionReadyPrefix
    (tfEq coqRestrictedPADirectImpIntroductionReadyChildLeftTerm
      coqRestrictedPADirectImpIntroductionReadyChildLeftTerm)
    (tfEq coqRestrictedPADirectImpIntroductionReadyChildLeftTerm
      coqRestrictedPADirectImpIntroductionReadyChildRightTerm)
    (trpEqRefl coqRestrictedPADirectImpIntroductionReadyPrefix
      coqRestrictedPADirectImpIntroductionReadyChildLeftTerm).

Lemma templateRawDerives_orI1_ready : forall
    context left right child,
  TemplateRawDerives context left child ->
  TemplateRawDerives context (tfOr left right)
    (trpOrI1 context left right child).
Proof.
  intros context left right child
    [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption.
Qed.

Lemma coqRestrictedPADirectImpIntroductionReadyChildGuardRoot_valid :
  TemplateRawDerives coqRestrictedPADirectImpIntroductionReadyPrefix
    coqRestrictedPADirectImpIntroductionReadyChildGuardTemplate
    coqRestrictedPADirectImpIntroductionReadyChildGuardRoot.
Proof.
  rewrite coqRestrictedPADirectImpIntroductionReadyChildGuard_view.
  unfold coqRestrictedPADirectImpIntroductionReadyChildGuardRoot.
  apply templateRawDerives_orI1_ready.
  apply templateRawDerives_eqRefl.
Qed.

(** Every directly translated finite prefix is atomically adequate.  This
    local lemma avoids importing a global-row handoff merely for the generic
    template-translation contract. *)
Lemma raw_restrictedPADirectImpIntroductionReadyPrefix_atomically_adequate :
    forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    coqRestrictedPADirectImpIntroductionReadyPrefix.
Proof.
  intros M hPA inputs formula _.
  exact (raw_codedTemplateFormula_atomically_adequate_core M hPA
    (rawDirectStructuralTemplateTranslation M hPA inputs) formula).
Qed.

(** Main proof-producing endpoint.  All four premises of the generic child
    theorem are compiled above from the literal ready context; the result's
    conjunction is projected only after the theorem's standard witness
    extension has been fixed. *)
Theorem
    raw_restrictedPADirectImpIntroduction_readyChild_atomic_and_domain_on_standard_witness_extension :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix)
      atomicRoot domainRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext)
        coqRestrictedPADirectImpIntroductionReadyPrefix)
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectImpIntroductionReadyChildAtomicTemplate)
      atomicRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext)
        coqRestrictedPADirectImpIntroductionReadyPrefix)
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectImpIntroductionReadyChildDomainTemplate)
      domainRoot.
Proof.
  intros M hPA inputs baseWitnessList baseContext hbase.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (prefix := coqRestrictedPADirectImpIntroductionReadyPrefix).

  pose proof
    (raw_templateProofOnPAAxiomContext_localProof
      M hPA translation baseWitnessList baseContext
      coqRestrictedPADirectImpIntroductionReadyParentAtomicRoot
      hbase
      (proj1
        coqRestrictedPADirectImpIntroductionReadyParentAtomicRoot_valid))
    as hparentAtomic.
  pose proof
    (raw_templateProofOnPAAxiomContext_localProof
      M hPA translation baseWitnessList baseContext
      coqRestrictedPADirectImpIntroductionReadyParentDomainRoot
      hbase
      (proj1
        coqRestrictedPADirectImpIntroductionReadyParentDomainRoot_valid))
    as hparentDomain.
  pose proof
    (raw_templateProofOnPAAxiomContext_localProof
      M hPA translation baseWitnessList baseContext
      coqRestrictedPADirectImpIntroductionReadyChildShapeRoot
      hbase
      (proj1
        coqRestrictedPADirectImpIntroductionReadyChildShapeRoot_valid))
    as hshape.
  pose proof
    (raw_templateProofOnPAAxiomContext_localProof
      M hPA translation baseWitnessList baseContext
      coqRestrictedPADirectImpIntroductionReadyChildGuardRoot
      hbase
      (proj1
        coqRestrictedPADirectImpIntroductionReadyChildGuardRoot_valid))
    as hguard.

  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      coqRestrictedPADirectImpIntroductionReadyParentAtomicTemplate)
    (rawTemplateProofCodeOnTail translation baseContext
      coqRestrictedPADirectImpIntroductionReadyParentAtomicRoot))
    in hparentAtomic.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      coqRestrictedPADirectImpIntroductionReadyParentDomainTemplate)
    (rawTemplateProofCodeOnTail translation baseContext
      coqRestrictedPADirectImpIntroductionReadyParentDomainRoot))
    in hparentDomain.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      coqRestrictedPADirectImpIntroductionReadyChildShapeTemplate)
    (rawTemplateProofCodeOnTail translation baseContext
      coqRestrictedPADirectImpIntroductionReadyChildShapeRoot))
    in hshape.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      coqRestrictedPADirectImpIntroductionReadyChildGuardTemplate)
    (rawTemplateProofCodeOnTail translation baseContext
      coqRestrictedPADirectImpIntroductionReadyChildGuardRoot))
    in hguard.

  destruct
    (raw_codedPALocalProofOf_dynamicTruthImpDirectChildAdmissibilityCore_of_roots_on_witnessed_extension_under_prefix
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      baseWitnessList baseContext prefix
      coqRestrictedPADirectImpIntroductionReadyChildLevelTerm
      coqRestrictedPADirectImpIntroductionReadyChildParentTerm
      coqRestrictedPADirectImpIntroductionReadyChildLeftTerm
      coqRestrictedPADirectImpIntroductionReadyChildRightTerm
      coqRestrictedPADirectImpIntroductionReadyChildTerm
      (rawTemplateProofCodeOnTail translation baseContext
        coqRestrictedPADirectImpIntroductionReadyParentAtomicRoot)
      (rawTemplateProofCodeOnTail translation baseContext
        coqRestrictedPADirectImpIntroductionReadyParentDomainRoot)
      (rawTemplateProofCodeOnTail translation baseContext
        coqRestrictedPADirectImpIntroductionReadyChildShapeRoot)
      (rawTemplateProofCodeOnTail translation baseContext
        coqRestrictedPADirectImpIntroductionReadyChildGuardRoot)
      (raw_restrictedPADirectImpIntroductionReadyPrefix_atomically_adequate
        M hPA inputs)
      hbase hparentAtomic hparentDomain hshape hguard)
    as (witnesses & coreRoot & hextended & hincluded & hcore).
  rewrite
    coqRestrictedPADirectImpIntroductionReadyChildCoreConclusion_shape,
    rawTemplateFormula_and in hcore.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) prefix)
    (rawTemplateFormula translation
      coqRestrictedPADirectImpIntroductionReadyChildAtomicTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectImpIntroductionReadyChildDomainTemplate)
    coreRoot hcore) as hatomic.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) prefix)
    (rawTemplateFormula translation
      coqRestrictedPADirectImpIntroductionReadyChildAtomicTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectImpIntroductionReadyChildDomainTemplate)
    coreRoot hcore) as hdomain.
  lazymatch type of hatomic with
  | RawCodedPALocalProofOf _ _ _ ?atomicRoot =>
      lazymatch type of hdomain with
      | RawCodedPALocalProofOf _ _ _ ?domainRoot =>
          exists witnesses, atomicRoot, domainRoot;
          split; [exact hextended |];
          split; [exact hincluded |];
          split; assumption
      end
  end.
Qed.

End
  PABoundedRawCodedRestrictedPADirectImpIntroductionReadyChildAtomicDomainCompilation.
