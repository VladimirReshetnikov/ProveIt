(**
  Reusable recursive-child compilation for same-context unary rules.

  Conjunction elimination and disjunction introduction have the same
  recursive shape: their sole child has the parent's displayed context.
  The constructor tags and selected child conclusions differ, but none of
  that changes the strong-prefix argument.  This module factors that common
  argument into three layers.

  - At the semantic layer, [raw_recursive_constructor_child_interface] is
    instantiated uniformly for both And-E projections and both Or-I
    injections.
  - At the represented layer, a four-field child interface and the inherited
    strong prefix produce [context truth -> child truth].
  - A finite template proof of [P -> E -> P] inserts the displayed endpoint
    antecedent.  It is important that this is a genuine coded proof: no
    implicit weakening across a nonstandard coded context is used.

  The final adapters target the exact public residuals of And-E-left,
  And-E-right, and Or-I-right.  Their only premise is the corresponding
  same-context child-interface root.  Producing that arithmetic root from
  the strengthened parent certificates is intentionally kept as the sharp
  branch-specific boundary; the remainder of the pipeline is shared here.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedProofConstructors
  RawCodedProofDescent
  RawCodedProofEndpoints
  RawCodedProofRules
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedProofAndEConstructors
  RawCodedProofOrIConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedRestrictedProofAdmissibility
  RawCodedCarrierRestrictedProofReroot
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPADerivationSoundnessRecursiveChildInterface
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildCompilation.

Import PA.
Import PAListCode.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedProofOrIConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedRestrictedProofAdmissibility.
Import PABoundedRawCodedCarrierRestrictedProofReroot.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildInterface.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase.

(** ------------------------------------------------------------------
    Literal recursive rows for the two unary constructor families. *)

Lemma raw_andElimination_recursive_child_data : forall
    (M : RawPAModel) projection root context leftFormula rightFormula child,
  root = rawProofAndERoot M projection
    context leftFormula rightFormula child ->
  RawProofConstructorCode M
      root context leftFormula rightFormula
      (raw_zero M) (raw_zero M) child (raw_zero M) (raw_zero M) /\
  In
    ([rawNumeralValue M (rawAndProjectionTag projection);
        context; leftFormula; rightFormula; child], [child])
    (rawProofRecursiveCases M
      context leftFormula rightFormula
      (raw_zero M) (raw_zero M) child (raw_zero M) (raw_zero M)) /\
  root = rawListCode M
    [rawNumeralValue M (rawAndProjectionTag projection);
      context; leftFormula; rightFormula; child] /\
  In child [child].
Proof.
  intros M projection root context leftFormula rightFormula child hcode.
  repeat split.
  - rewrite hcode. apply raw_proofAndERoot_constructor.
  - unfold rawProofRecursiveCases.
    destruct projection; cbn; tauto.
  - exact hcode.
  - left. reflexivity.
Qed.

Lemma raw_orIntroduction_recursive_child_data : forall
    (M : RawPAModel) injection root context leftFormula rightFormula child,
  root = rawProofOrIRoot M injection
    context leftFormula rightFormula child ->
  RawProofConstructorCode M
      root context leftFormula rightFormula
      (raw_zero M) (raw_zero M) child (raw_zero M) (raw_zero M) /\
  In
    ([rawNumeralValue M (rawOrInjectionTag injection);
        context; leftFormula; rightFormula; child], [child])
    (rawProofRecursiveCases M
      context leftFormula rightFormula
      (raw_zero M) (raw_zero M) child (raw_zero M) (raw_zero M)) /\
  root = rawListCode M
    [rawNumeralValue M (rawOrInjectionTag injection);
      context; leftFormula; rightFormula; child] /\
  In child [child].
Proof.
  intros M injection root context leftFormula rightFormula child hcode.
  repeat split.
  - rewrite hcode. apply raw_proofOrIRoot_constructor.
  - unfold rawProofRecursiveCases.
    destruct injection; cbn; tauto.
  - exact hcode.
  - left. reflexivity.
Qed.

(** Both And-E rules recurse into a proof of the displayed conjunction.  The
    projection affects only the parent's conclusion, so it is absent from
    the inherited child bundle except through the constructor tag. *)
Theorem raw_andElimination_child_interface : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level projection root coverageBound context
    leftFormula rightFormula child assignmentCode assignmentStep,
  RawCarrierRestrictedProofAt M tail level root ->
  RawProofAtomicallyAdequate M root ->
  RawProofFormulaCoverage M root coverageBound ->
  RawProofRuleCoverage M root ->
  root = rawProofAndERoot M projection
    context leftFormula rightFormula child ->
  RawProofEndpoint M child context
    (rawFormulaAndCode M leftFormula rightFormula) ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep coverageBound ->
  rawLt M child root /\
  RawCarrierRestrictedProofAt M tail level child /\
  RawProofAtomicallyAdequate M child /\
  RawProofFormulaCoverage M child coverageBound /\
  RawProofRuleCoverage M child /\
  RawProofRuleValid M child context
    (rawFormulaAndCode M leftFormula rightFormula) /\
  RawCodedFormulaAtomicallyAdequate M
    (rawFormulaAndCode M leftFormula rightFormula) /\
  RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep
    (rawFormulaAndCode M leftFormula rightFormula) /\
  RawCarrierFormulaQuantifierBounded M level
    (rawFormulaAndCode M leftFormula rightFormula).
Proof.
  intros M hPA tail level projection root coverageBound context
    leftFormula rightFormula child assignmentCode assignmentStep
    hrestricted hatomic hformulaCoverage hruleCoverage hcode
    hendpoint hassignmentCoverage.
  destruct (raw_andElimination_recursive_child_data M projection root
    context leftFormula rightFormula child hcode) as
    [hconstructor [hentry [hfields hchild]]].
  exact
    (raw_recursive_constructor_child_interface
      M hPA tail level root coverageBound context
      leftFormula rightFormula (raw_zero M) (raw_zero M)
      child (raw_zero M) (raw_zero M)
      [rawNumeralValue M (rawAndProjectionTag projection);
        context; leftFormula; rightFormula; child]
      [child] child (rawFormulaAndCode M leftFormula rightFormula)
      assignmentCode assignmentStep
      hrestricted hatomic hformulaCoverage hruleCoverage
      hconstructor hentry hfields hchild hendpoint hassignmentCoverage).
Qed.

Corollary raw_andEliminationLeft_child_interface : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level root coverageBound context
    leftFormula rightFormula child assignmentCode assignmentStep,
  RawCarrierRestrictedProofAt M tail level root ->
  RawProofAtomicallyAdequate M root ->
  RawProofFormulaCoverage M root coverageBound ->
  RawProofRuleCoverage M root ->
  root = rawProofAndERoot M RawAndLeft
    context leftFormula rightFormula child ->
  RawProofEndpoint M child context
    (rawFormulaAndCode M leftFormula rightFormula) ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep coverageBound ->
  rawLt M child root /\
  RawCarrierRestrictedProofAt M tail level child /\
  RawProofAtomicallyAdequate M child /\
  RawProofFormulaCoverage M child coverageBound /\
  RawProofRuleCoverage M child /\
  RawProofRuleValid M child context
    (rawFormulaAndCode M leftFormula rightFormula) /\
  RawCodedFormulaAtomicallyAdequate M
    (rawFormulaAndCode M leftFormula rightFormula) /\
  RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep
    (rawFormulaAndCode M leftFormula rightFormula) /\
  RawCarrierFormulaQuantifierBounded M level
    (rawFormulaAndCode M leftFormula rightFormula).
Proof.
  intros M hPA tail level root coverageBound context
    leftFormula rightFormula child assignmentCode assignmentStep
    hrestricted hatomic hformulaCoverage hruleCoverage hcode
    hendpoint hassignmentCoverage.
  exact (raw_andElimination_child_interface
    M hPA tail level RawAndLeft root coverageBound context
    leftFormula rightFormula child assignmentCode assignmentStep
    hrestricted hatomic hformulaCoverage hruleCoverage hcode
    hendpoint hassignmentCoverage).
Qed.

Corollary raw_andEliminationRight_child_interface : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level root coverageBound context
    leftFormula rightFormula child assignmentCode assignmentStep,
  RawCarrierRestrictedProofAt M tail level root ->
  RawProofAtomicallyAdequate M root ->
  RawProofFormulaCoverage M root coverageBound ->
  RawProofRuleCoverage M root ->
  root = rawProofAndERoot M RawAndRight
    context leftFormula rightFormula child ->
  RawProofEndpoint M child context
    (rawFormulaAndCode M leftFormula rightFormula) ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep coverageBound ->
  rawLt M child root /\
  RawCarrierRestrictedProofAt M tail level child /\
  RawProofAtomicallyAdequate M child /\
  RawProofFormulaCoverage M child coverageBound /\
  RawProofRuleCoverage M child /\
  RawProofRuleValid M child context
    (rawFormulaAndCode M leftFormula rightFormula) /\
  RawCodedFormulaAtomicallyAdequate M
    (rawFormulaAndCode M leftFormula rightFormula) /\
  RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep
    (rawFormulaAndCode M leftFormula rightFormula) /\
  RawCarrierFormulaQuantifierBounded M level
    (rawFormulaAndCode M leftFormula rightFormula).
Proof.
  intros M hPA tail level root coverageBound context
    leftFormula rightFormula child assignmentCode assignmentStep
    hrestricted hatomic hformulaCoverage hruleCoverage hcode
    hendpoint hassignmentCoverage.
  exact (raw_andElimination_child_interface
    M hPA tail level RawAndRight root coverageBound context
    leftFormula rightFormula child assignmentCode assignmentStep
    hrestricted hatomic hformulaCoverage hruleCoverage hcode
    hendpoint hassignmentCoverage).
Qed.

(** Or-I selects one of its two displayed formulae as the child conclusion.
    Keeping the injection abstract makes the left and right arithmetic
    descent proofs literally the same theorem. *)
Theorem raw_orIntroduction_child_interface : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level injection root coverageBound context
    leftFormula rightFormula child assignmentCode assignmentStep,
  RawCarrierRestrictedProofAt M tail level root ->
  RawProofAtomicallyAdequate M root ->
  RawProofFormulaCoverage M root coverageBound ->
  RawProofRuleCoverage M root ->
  root = rawProofOrIRoot M injection
    context leftFormula rightFormula child ->
  RawProofEndpoint M child context
    (rawOrInjectionPremise M injection leftFormula rightFormula) ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep coverageBound ->
  rawLt M child root /\
  RawCarrierRestrictedProofAt M tail level child /\
  RawProofAtomicallyAdequate M child /\
  RawProofFormulaCoverage M child coverageBound /\
  RawProofRuleCoverage M child /\
  RawProofRuleValid M child context
    (rawOrInjectionPremise M injection leftFormula rightFormula) /\
  RawCodedFormulaAtomicallyAdequate M
    (rawOrInjectionPremise M injection leftFormula rightFormula) /\
  RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep
    (rawOrInjectionPremise M injection leftFormula rightFormula) /\
  RawCarrierFormulaQuantifierBounded M level
    (rawOrInjectionPremise M injection leftFormula rightFormula).
Proof.
  intros M hPA tail level injection root coverageBound context
    leftFormula rightFormula child assignmentCode assignmentStep
    hrestricted hatomic hformulaCoverage hruleCoverage hcode
    hendpoint hassignmentCoverage.
  destruct (raw_orIntroduction_recursive_child_data M injection root
    context leftFormula rightFormula child hcode) as
    [hconstructor [hentry [hfields hchild]]].
  exact
    (raw_recursive_constructor_child_interface
      M hPA tail level root coverageBound context
      leftFormula rightFormula (raw_zero M) (raw_zero M)
      child (raw_zero M) (raw_zero M)
      [rawNumeralValue M (rawOrInjectionTag injection);
        context; leftFormula; rightFormula; child]
      [child] child
      (rawOrInjectionPremise M injection leftFormula rightFormula)
      assignmentCode assignmentStep
      hrestricted hatomic hformulaCoverage hruleCoverage
      hconstructor hentry hfields hchild hendpoint hassignmentCoverage).
Qed.

Corollary raw_orIntroductionRight_child_interface : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level root coverageBound context
    leftFormula rightFormula child assignmentCode assignmentStep,
  RawCarrierRestrictedProofAt M tail level root ->
  RawProofAtomicallyAdequate M root ->
  RawProofFormulaCoverage M root coverageBound ->
  RawProofRuleCoverage M root ->
  root = rawProofOrIRoot M RawOrRight
    context leftFormula rightFormula child ->
  RawProofEndpoint M child context rightFormula ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep coverageBound ->
  rawLt M child root /\
  RawCarrierRestrictedProofAt M tail level child /\
  RawProofAtomicallyAdequate M child /\
  RawProofFormulaCoverage M child coverageBound /\
  RawProofRuleCoverage M child /\
  RawProofRuleValid M child context rightFormula /\
  RawCodedFormulaAtomicallyAdequate M rightFormula /\
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep rightFormula /\
  RawCarrierFormulaQuantifierBounded M level rightFormula.
Proof.
  intros M hPA tail level root coverageBound context
    leftFormula rightFormula child assignmentCode assignmentStep
    hrestricted hatomic hformulaCoverage hruleCoverage hcode
    hendpoint hassignmentCoverage.
  exact (raw_orIntroduction_child_interface
    M hPA tail level RawOrRight root coverageBound context
    leftFormula rightFormula child assignmentCode assignmentStep
    hrestricted hatomic hformulaCoverage hruleCoverage hcode
    hendpoint hassignmentCoverage).
Qed.

(** ------------------------------------------------------------------
    The common strong-prefix compiler before context truth is consumed. *)

(** This is the reusable prefix of the existing And-I child-truth theorem.
    Stopping before its final modus ponens is exactly what unary rule cases
    need: the witness-context truth remains the consequent's antecedent. *)
Theorem raw_codedPALocalProofOf_sameContextUnaryChildContinuation : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M)
    localContext child witnessContext childConclusion
    interfaceRoot prefixRoot,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation
      (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
        child witnessContext childConclusion)) interfaceRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation
      coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate)
    prefixRoot ->
  exists continuationRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation localContext)
      (rawTemplateFormula translation
        (tfImp
          (coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
            child witnessContext childConclusion)
          (coqRestrictedPADirectAndIntroductionChildTruthTemplate
            child witnessContext childConclusion))) continuationRoot.
Proof.
  intros M hPA translation localContext child witnessContext
    childConclusion interfaceRoot prefixRoot hinterface hprefix.
  set (contextCode := rawTemplateContextCode translation localContext).
  set (below :=
    coqRestrictedPADirectAndIntroductionChildBelowTemplate child).
  set (restricted :=
    coqRestrictedPADirectAndIntroductionChildRestrictedTemplate
      child witnessContext childConclusion).
  set (childEndpoint :=
    coqRestrictedPADirectAndIntroductionChildEndpointTemplate
      child witnessContext childConclusion).
  set (childAdmissible :=
    coqRestrictedPADirectAndIntroductionChildAdmissibleTemplate
      child witnessContext childConclusion).
  set (lastPair := tfAnd childEndpoint childAdmissible).
  set (rest := tfAnd restricted lastPair).

  unfold
    coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    in hinterface.
  rewrite rawTemplateFormula_and in hinterface.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _
    interfaceRoot hinterface) as hbelow.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _
    interfaceRoot hinterface) as hrest.
  rewrite rawTemplateFormula_and in hrest.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _ hrest)
    as hrestricted.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _ hrest)
    as hlastPair.
  rewrite rawTemplateFormula_and in hlastPair.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _ hlastPair)
    as hchildEndpoint.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _ hlastPair)
    as hchildAdmissible.

  rewrite coqRestrictedPADirectAndIntroduction_deep_prefix_shape in hprefix.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAllE
      M hPA translation localContext
      coqRestrictedPADirectAndIntroductionDeepStrongPrefixBodyTemplate
      child prefixRoot hprefix) as hguarded.
  lazymatch type of hguarded with
  | RawCodedPALocalProofOf _ _ _ ?guardedRoot =>
      change (RawCodedPALocalProofOf M contextCode
        (rawTemplateFormula translation
          (coqRestrictedPADirectAndIntroductionChildGuardedTemplate child))
        guardedRoot) in hguarded
  end.
  rewrite coqRestrictedPADirectAndIntroduction_child_guarded_shape
    in hguarded.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ _ hguarded hbelow)
    as hpredicate.

  rewrite
    coqRestrictedPADirectAndIntroduction_child_predicate_all_shape
    in hpredicate.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAllE
      M hPA translation localContext _ witnessContext _ hpredicate)
    as hafterContext.
  lazymatch type of hafterContext with
  | RawCodedPALocalProofOf _ _ _ ?afterContextRoot =>
      change (RawCodedPALocalProofOf M contextCode
        (rawTemplateFormula translation
          (coqRestrictedPADirectAndIntroductionChildAfterContextTemplate
            child witnessContext)) afterContextRoot) in hafterContext
  end.
  rewrite
    coqRestrictedPADirectAndIntroduction_child_after_context_all_shape
    in hafterContext.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAllE
      M hPA translation localContext _ childConclusion _ hafterContext)
    as hafterConclusion.
  lazymatch type of hafterConclusion with
  | RawCodedPALocalProofOf _ _ _ ?afterConclusionRoot =>
      change (RawCodedPALocalProofOf M contextCode
        (rawTemplateFormula translation
          (coqRestrictedPADirectAndIntroductionChildAfterConclusionTemplate
            child witnessContext childConclusion)) afterConclusionRoot)
        in hafterConclusion
  end.
  rewrite
    coqRestrictedPADirectAndIntroduction_child_after_conclusion_all_shape
    in hafterConclusion.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAllE
      M hPA translation localContext _
      coqRestrictedPADirectAndIntroductionAssignmentCodeTerm _
      hafterConclusion) as hafterAssignmentCode.
  lazymatch type of hafterAssignmentCode with
  | RawCodedPALocalProofOf _ _ _ ?afterAssignmentCodeRoot =>
      change (RawCodedPALocalProofOf M contextCode
        (rawTemplateFormula translation
          (coqRestrictedPADirectAndIntroductionChildAfterAssignmentCodeTemplate
            child witnessContext childConclusion
            coqRestrictedPADirectAndIntroductionAssignmentCodeTerm))
        afterAssignmentCodeRoot) in hafterAssignmentCode
  end.
  rewrite
    coqRestrictedPADirectAndIntroduction_child_after_assignment_all_shape
    in hafterAssignmentCode.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAllE
      M hPA translation localContext _
      coqRestrictedPADirectAndIntroductionAssignmentStepTerm _
      hafterAssignmentCode) as hready.
  lazymatch type of hready with
  | RawCodedPALocalProofOf _ _ _ ?readyRoot =>
      change (RawCodedPALocalProofOf M contextCode
        (rawTemplateFormula translation
          (coqRestrictedPADirectAndIntroductionChildReadyTemplate
            child witnessContext childConclusion
            coqRestrictedPADirectAndIntroductionAssignmentCodeTerm
            coqRestrictedPADirectAndIntroductionAssignmentStepTerm))
        readyRoot) in hready
  end.
  rewrite coqRestrictedPADirectAndIntroduction_child_ready_shape in hready.

  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ _ hready hrestricted)
    as hafterRestricted.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ _
      hafterRestricted hchildEndpoint) as hafterEndpoint.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext _ _ _ _
      hafterEndpoint hchildAdmissible) as hafterAdmissible.
  lazymatch type of hafterAdmissible with
  | RawCodedPALocalProofOf _ _ _ ?continuationRoot =>
      exists continuationRoot; exact hafterAdmissible
  end.
Qed.

(** ------------------------------------------------------------------
    A represented K-combinator in an arbitrary unchanged context. *)

Definition coqRestrictedPASameContextUnaryKInnerContext
    (context : TemplateContext) (consequence unused : TemplateFormula)
    : TemplateContext :=
  unused :: consequence :: context.

Definition coqRestrictedPASameContextUnaryKAssumptionRoot
    (context : TemplateContext) (consequence unused : TemplateFormula)
    : TemplateRawProof :=
  trpAss
    (coqRestrictedPASameContextUnaryKInnerContext
      context consequence unused)
    consequence.

Definition coqRestrictedPASameContextUnaryKUnusedImpRoot
    (context : TemplateContext) (consequence unused : TemplateFormula)
    : TemplateRawProof :=
  trpImpI (consequence :: context) unused consequence
    (coqRestrictedPASameContextUnaryKAssumptionRoot
      context consequence unused).

Definition coqRestrictedPASameContextUnaryKRoot
    (context : TemplateContext) (consequence unused : TemplateFormula)
    : TemplateRawProof :=
  trpImpI context consequence (tfImp unused consequence)
    (coqRestrictedPASameContextUnaryKUnusedImpRoot
      context consequence unused).

Lemma raw_sameContextUnary_templateRawDerives_impI : forall
    context antecedent consequent child,
  TemplateRawDerives (antecedent :: context) consequent child ->
  TemplateRawDerives context (tfImp antecedent consequent)
    (trpImpI context antecedent consequent child).
Proof.
  intros context antecedent consequent child
    [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqRestrictedPASameContextUnaryKAssumptionRoot_valid : forall
    context consequence unused,
  TemplateRawDerives
    (coqRestrictedPASameContextUnaryKInnerContext
      context consequence unused)
    consequence
    (coqRestrictedPASameContextUnaryKAssumptionRoot
      context consequence unused).
Proof.
  intros context consequence unused.
  apply templateRawDerives_assumption.
  right. left. reflexivity.
Qed.

Lemma coqRestrictedPASameContextUnaryKUnusedImpRoot_valid : forall
    context consequence unused,
  TemplateRawDerives (consequence :: context)
    (tfImp unused consequence)
    (coqRestrictedPASameContextUnaryKUnusedImpRoot
      context consequence unused).
Proof.
  intros context consequence unused.
  apply raw_sameContextUnary_templateRawDerives_impI.
  exact (coqRestrictedPASameContextUnaryKAssumptionRoot_valid
    context consequence unused).
Qed.

Lemma coqRestrictedPASameContextUnaryKRoot_valid : forall
    context consequence unused,
  TemplateRawDerives context
    (tfImp consequence (tfImp unused consequence))
    (coqRestrictedPASameContextUnaryKRoot context consequence unused).
Proof.
  intros context consequence unused.
  apply raw_sameContextUnary_templateRawDerives_impI.
  exact (coqRestrictedPASameContextUnaryKUnusedImpRoot_valid
    context consequence unused).
Qed.

Theorem raw_codedPALocalProofOf_sameContextUnary_add_unused_antecedent :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M)
    localContext consequence unused consequenceRoot,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation consequence) consequenceRoot ->
  exists resultRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation localContext)
      (rawTemplateFormula translation (tfImp unused consequence))
      resultRoot.
Proof.
  intros M hPA translation localContext consequence unused
    consequenceRoot hconsequence.
  pose proof
    (raw_templateProof_localProof M hPA translation
      (coqRestrictedPASameContextUnaryKRoot
        localContext consequence unused)
      (proj1 (coqRestrictedPASameContextUnaryKRoot_valid
        localContext consequence unused))) as hk.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation
      (tfImp consequence (tfImp unused consequence)))
    (rawTemplateProofCode translation
      (coqRestrictedPASameContextUnaryKRoot
        localContext consequence unused))) in hk.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation localContext consequence
      (tfImp unused consequence) _ consequenceRoot hk hconsequence)
    as hresult.
  lazymatch type of hresult with
  | RawCodedPALocalProofOf _ _ _ ?resultRoot =>
      exists resultRoot; exact hresult
  end.
Qed.

(** The fully shared compiler.  Notice that the displayed endpoint is used
    only as the antecedent inserted by K.  The child interface already
    contains the rule-valid endpoint consumed by the induction prefix. *)
Theorem raw_codedPALocalProofOf_sameContextUnaryRecursiveChildLaw : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M)
    localContext child witnessContext childConclusion displayedEndpoint
    interfaceRoot prefixRoot,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation
      (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
        child witnessContext childConclusion)) interfaceRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation localContext)
    (rawTemplateFormula translation
      coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate)
    prefixRoot ->
  exists lawRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation localContext)
      (rawTemplateFormula translation
        (tfImp displayedEndpoint
          (tfImp
            (coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
              child witnessContext childConclusion)
            (coqRestrictedPADirectAndIntroductionChildTruthTemplate
              child witnessContext childConclusion)))) lawRoot.
Proof.
  intros M hPA translation localContext child witnessContext
    childConclusion displayedEndpoint interfaceRoot prefixRoot
    hinterface hprefix.
  destruct
    (raw_codedPALocalProofOf_sameContextUnaryChildContinuation
      M hPA translation localContext child witnessContext childConclusion
      interfaceRoot prefixRoot hinterface hprefix)
    as [continuationRoot hcontinuation].
  exact
    (raw_codedPALocalProofOf_sameContextUnary_add_unused_antecedent
      M hPA translation localContext
      (tfImp
        (coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
          child witnessContext childConclusion)
        (coqRestrictedPADirectAndIntroductionChildTruthTemplate
          child witnessContext childConclusion))
      displayedEndpoint continuationRoot hcontinuation).
Qed.

(** ------------------------------------------------------------------
    Root interface and generic ready-context compiler. *)

Definition RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (context : TemplateContext)
    (child witnessContext childConclusion : TemplateTerm) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        (coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
          child witnessContext childConclusion)) root.

Arguments RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt
  M translation context child witnessContext childConclusion
  : clear implicits.

Theorem raw_sameContextUnary_recursiveChildLawRootAt_of_interface : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M)
    context child witnessContext childConclusion displayedEndpoint,
  In coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate context ->
  RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt
    M translation context child witnessContext childConclusion ->
  exists lawRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        (tfImp displayedEndpoint
          (tfImp
            (coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
              child witnessContext childConclusion)
            (coqRestrictedPADirectAndIntroductionChildTruthTemplate
              child witnessContext childConclusion)))) lawRoot.
Proof.
  intros M hPA translation context child witnessContext childConclusion
    displayedEndpoint hprefixIn [interfaceRoot hinterface].
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation context
      coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate
      hprefixIn) as hprefix.
  exact
    (raw_codedPALocalProofOf_sameContextUnaryRecursiveChildLaw
      M hPA translation context child witnessContext childConclusion
      displayedEndpoint interfaceRoot _ hinterface hprefix).
Qed.

(** The endpoint shell is identical in every direct eight-witness rule case.
    This lemma records the one non-obvious membership calculation used by
    all three public adapters below. *)
Lemma coqRestrictedPASameContextUnary_deep_prefix_in : forall
    first second third tail,
  In coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate
    (first :: second :: third ::
      rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
      rawCoqRestrictedPADirectEndpointDeepTail
        (rawCoqRestrictedPADirectStrongStepEndpointTail tail)).
Proof.
  intros first second third tail.
  do 3 right.
  rewrite <- raw_coqRestrictedPADirectEndpointDeepContext_shape.
  unfold coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate.
  apply raw_coqTemplateNestedExContext_inherited.
  unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  right.
  unfold rawCoqRestrictedPADirectStrongStepFourBinderContext.
  apply coqRestrictedPADirectAndIntroduction_contextShiftN_head.
Qed.

(** ------------------------------------------------------------------
    Exact branch instances and their remaining arithmetic input. *)

Definition coqRestrictedPADirectAndEliminationChildTerm : TemplateTerm :=
  ttVar 2.

Definition coqRestrictedPADirectAndEliminationWitnessContextTerm
    : TemplateTerm := ttVar 7.

Definition coqRestrictedPADirectAndEliminationChildConclusionTerm
    : TemplateTerm := ttVar 4.

Definition coqRestrictedPADirectOrIntroductionRightChildTerm
    : TemplateTerm := ttVar 2.

Definition coqRestrictedPADirectOrIntroductionRightWitnessContextTerm
    : TemplateTerm := ttVar 7.

Lemma coqRestrictedPADirectAndElimination_child_context_truth_agreement :
  coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
    coqRestrictedPADirectAndEliminationChildTerm
    coqRestrictedPADirectAndEliminationWitnessContextTerm
    coqRestrictedPADirectAndEliminationChildConclusionTerm =
  coqRestrictedPADirectAssumptionWitnessContextTruthTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndElimination_child_truth_agreement :
  coqRestrictedPADirectAndIntroductionChildTruthTemplate
    coqRestrictedPADirectAndEliminationChildTerm
    coqRestrictedPADirectAndEliminationWitnessContextTerm
    coqRestrictedPADirectAndEliminationChildConclusionTerm =
  coqRestrictedPADirectAndEliminationLeftFormulaTruthTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndEliminationRight_child_truth_agreement :
  coqRestrictedPADirectAndIntroductionChildTruthTemplate
    coqRestrictedPADirectAndEliminationChildTerm
    coqRestrictedPADirectAndEliminationWitnessContextTerm
    coqRestrictedPADirectAndEliminationChildConclusionTerm =
  coqRestrictedPADirectAndEliminationRightFormulaTruthTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectOrIntroductionRight_child_context_truth_agreement :
  coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
    coqRestrictedPADirectOrIntroductionRightChildTerm
    coqRestrictedPADirectOrIntroductionRightWitnessContextTerm
    coqRestrictedPADirectOrIntroductionRightFormulaTerm =
  coqRestrictedPADirectAssumptionWitnessContextTruthTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectOrIntroductionRight_child_truth_agreement :
  coqRestrictedPADirectAndIntroductionChildTruthTemplate
    coqRestrictedPADirectOrIntroductionRightChildTerm
    coqRestrictedPADirectOrIntroductionRightWitnessContextTerm
    coqRestrictedPADirectOrIntroductionRightFormulaTerm =
  coqRestrictedPADirectOrIntroductionRightFormulaTruthTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndEliminationLeft_ready_prefix_in : forall tail,
  In coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate
    (coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext,
    coqRestrictedPADirectStrongStepAndEliminationLeftAdmissibleContext,
    coqRestrictedPADirectStrongStepAndEliminationLeftCaseContext,
    coqRestrictedPADirectStrongStepAndEliminationLeftDeepEndpointContext.
  apply coqRestrictedPASameContextUnary_deep_prefix_in.
Qed.

Lemma coqRestrictedPADirectAndEliminationRight_ready_prefix_in : forall tail,
  In coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate
    (coqRestrictedPADirectStrongStepAndEliminationRightReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepAndEliminationRightReadyContext,
    coqRestrictedPADirectStrongStepAndEliminationRightAdmissibleContext,
    coqRestrictedPADirectStrongStepAndEliminationRightCaseContext,
    coqRestrictedPADirectStrongStepAndEliminationRightDeepEndpointContext.
  apply coqRestrictedPASameContextUnary_deep_prefix_in.
Qed.

Lemma coqRestrictedPADirectOrIntroductionRight_ready_prefix_in : forall tail,
  In coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate
    (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext,
    coqRestrictedPADirectStrongStepOrIntroductionRightAdmissibleContext,
    coqRestrictedPADirectStrongStepOrIntroductionRightCaseContext,
    coqRestrictedPADirectStrongStepOrIntroductionRightDeepEndpointContext.
  apply coqRestrictedPASameContextUnary_deep_prefix_in.
Qed.

Definition RawCoqRestrictedPADirectAndEliminationLeftChildInterfaceRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext tail)
    coqRestrictedPADirectAndEliminationChildTerm
    coqRestrictedPADirectAndEliminationWitnessContextTerm
    coqRestrictedPADirectAndEliminationChildConclusionTerm.

Definition RawCoqRestrictedPADirectAndEliminationRightChildInterfaceRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqRestrictedPADirectStrongStepAndEliminationRightReadyContext tail)
    coqRestrictedPADirectAndEliminationChildTerm
    coqRestrictedPADirectAndEliminationWitnessContextTerm
    coqRestrictedPADirectAndEliminationChildConclusionTerm.

Definition RawCoqRestrictedPADirectOrIntroductionRightChildInterfaceRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext tail)
    coqRestrictedPADirectOrIntroductionRightChildTerm
    coqRestrictedPADirectOrIntroductionRightWitnessContextTerm
    coqRestrictedPADirectOrIntroductionRightFormulaTerm.

Arguments RawCoqRestrictedPADirectAndEliminationLeftChildInterfaceRoot
  M hPA inputs tail : clear implicits.
Arguments RawCoqRestrictedPADirectAndEliminationRightChildInterfaceRoot
  M hPA inputs tail : clear implicits.
Arguments RawCoqRestrictedPADirectOrIntroductionRightChildInterfaceRoot
  M hPA inputs tail : clear implicits.

Theorem
    raw_andEliminationLeft_recursiveChildLawRoot_of_sameContextInterface :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectAndEliminationLeftChildInterfaceRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail hinterface.
  unfold RawCoqRestrictedPADirectAndEliminationLeftChildInterfaceRoot
    in hinterface.
  destruct
    (raw_sameContextUnary_recursiveChildLawRootAt_of_interface
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext tail)
      coqRestrictedPADirectAndEliminationChildTerm
      coqRestrictedPADirectAndEliminationWitnessContextTerm
      coqRestrictedPADirectAndEliminationChildConclusionTerm
      coqRestrictedPADirectAndEliminationLeftChildEndpointTemplate
      (coqRestrictedPADirectAndEliminationLeft_ready_prefix_in tail)
      hinterface) as [lawRoot hlaw].
  rewrite coqRestrictedPADirectAndElimination_child_context_truth_agreement,
    coqRestrictedPADirectAndElimination_child_truth_agreement in hlaw.
  exists lawRoot.
  exact hlaw.
Qed.

Theorem
    raw_andEliminationRight_recursiveChildLawRoot_of_sameContextInterface :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectAndEliminationRightChildInterfaceRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail hinterface.
  unfold RawCoqRestrictedPADirectAndEliminationRightChildInterfaceRoot
    in hinterface.
  destruct
    (raw_sameContextUnary_recursiveChildLawRootAt_of_interface
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqRestrictedPADirectStrongStepAndEliminationRightReadyContext tail)
      coqRestrictedPADirectAndEliminationChildTerm
      coqRestrictedPADirectAndEliminationWitnessContextTerm
      coqRestrictedPADirectAndEliminationChildConclusionTerm
      coqRestrictedPADirectAndEliminationRightChildEndpointTemplate
      (coqRestrictedPADirectAndEliminationRight_ready_prefix_in tail)
      hinterface) as [lawRoot hlaw].
  rewrite coqRestrictedPADirectAndElimination_child_context_truth_agreement,
    coqRestrictedPADirectAndEliminationRight_child_truth_agreement in hlaw.
  exists lawRoot.
  exact hlaw.
Qed.

Theorem
    raw_orIntroductionRight_recursiveChildLawRoot_of_sameContextInterface :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectOrIntroductionRightChildInterfaceRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail hinterface.
  unfold RawCoqRestrictedPADirectOrIntroductionRightChildInterfaceRoot
    in hinterface.
  destruct
    (raw_sameContextUnary_recursiveChildLawRootAt_of_interface
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext tail)
      coqRestrictedPADirectOrIntroductionRightChildTerm
      coqRestrictedPADirectOrIntroductionRightWitnessContextTerm
      coqRestrictedPADirectOrIntroductionRightFormulaTerm
      coqRestrictedPADirectOrIntroductionRightChildEndpointTemplate
      (coqRestrictedPADirectOrIntroductionRight_ready_prefix_in tail)
      hinterface) as [lawRoot hlaw].
  rewrite
    coqRestrictedPADirectOrIntroductionRight_child_context_truth_agreement,
    coqRestrictedPADirectOrIntroductionRight_child_truth_agreement in hlaw.
  exists lawRoot.
  exact hlaw.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildCompilation.
