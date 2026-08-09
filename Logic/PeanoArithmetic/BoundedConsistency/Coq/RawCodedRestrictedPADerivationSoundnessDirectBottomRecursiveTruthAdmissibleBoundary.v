(**
  Honest Bottom-E recursive truth below the admissibility premise.

  The historical Bottom-E residual is ordered too early: its context contains
  the rule row, the restricted parent proof, and [K(d)], but the outer
  admissibility premise has not yet been introduced.  In contrast, every
  genuine use of [K(d)] needs the child's admissibility bundle, including the
  common proof-coverage/assignment-coverage witness.  The Or-I-left compiler
  obtains that witness from its ready context; Bottom-E cannot obtain it from
  the older case context alone.

  This file performs the largest sound fragment of the intended reduction.
  It adds the already-public admissibility premise to a corrected ready
  context, specializes recursive proof descent to the literal Bot-E child,
  compiles the complete arithmetic child interface from one fixed PA source,
  applies [K(d)], and transports the resulting opaque conclusion-truth atom
  along the literal equality between the child's conclusion and the bottom
  code.  Thus no child-interface or child-truth law remains assumed.

  The final section records, without hiding either issue, the two operations
  still required to recover the older frozen residual:

  - normalize truth of the closed bottom code from the current assignment to
    the canonical all-zero assignment used by the native refutation; and
  - erase the admissibility premise which the historical residual omitted.

  The second operation is deliberately exposed as an implication in the
  represented calculus.  It is not silently justified by arithmetic
  completeness, because it contains opaque truth atoms and is not a valid
  propositional principle.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawModelCompleteness
  RawCodedAssignment
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedContextLists
  RawCodedProofConstructors
  RawCodedProofDescent
  RawCodedProofEndpoints
  RawCodedProofRules
  RawCodedProofUnaryConstructors
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedFixedLevelTruthTotality
  RawCodedRestrictedPAProof
  RawCodedRestrictedProofAdmissibility
  RawCodedCarrierRestrictedProofReroot
  RawCodedRestrictedPADerivationSoundnessRecursiveChildInterface
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedTargetTemplateSemantics
  RawCodedPALocalProofExistential
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofEquality
  RawCodedPALocalProofUniversalSourceInstance
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplateParameterAbstraction
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectRenamedChildTruth
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation
  RawCodedRestrictedPADerivationSoundnessDirectBottomEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterBottomElimination
  RawCodedRestrictedPADerivationSoundnessDirectBottomCoreNativeReduction.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomRecursiveTruthAdmissibleBoundary.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofUnaryConstructors.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedProofAdmissibility.
Import PABoundedRawCodedCarrierRestrictedProofReroot.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildInterface.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedTargetTemplateSemantics.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofEquality.
Import PABoundedRawCodedPALocalProofUniversalSourceInstance.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRenamedChildTruth.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterBottomElimination.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomCoreNativeReduction.

(** ------------------------------------------------------------------
    Corrected contexts and the literal Bottom-E child. *)

Definition coqRestrictedPADirectBottomChildTerm : TemplateTerm := ttVar 2.

Definition coqRestrictedPADirectBottomChildConclusionTerm
    : TemplateTerm := ttVar 5.

Definition coqRestrictedPADirectBottomChildInterfaceResultTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    coqRestrictedPADirectBottomChildTerm
    coqRestrictedPADirectBottomWitnessContextTerm
    coqRestrictedPADirectBottomChildConclusionTerm.

Definition coqRestrictedPADirectBottomChildBelowTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildBelowTemplate
    coqRestrictedPADirectBottomChildTerm.

Definition coqRestrictedPADirectBottomChildRestrictedTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildRestrictedTemplate
    coqRestrictedPADirectBottomChildTerm
    coqRestrictedPADirectBottomWitnessContextTerm
    coqRestrictedPADirectBottomChildConclusionTerm.

Definition coqRestrictedPADirectBottomChildPredicateEndpointTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildEndpointTemplate
    coqRestrictedPADirectBottomChildTerm
    coqRestrictedPADirectBottomWitnessContextTerm
    coqRestrictedPADirectBottomChildConclusionTerm.

Definition coqRestrictedPADirectBottomChildAdmissibleTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildAdmissibleTemplate
    coqRestrictedPADirectBottomChildTerm
    coqRestrictedPADirectBottomWitnessContextTerm
    coqRestrictedPADirectBottomChildConclusionTerm.

(** The formula-code equality is stated separately from the child interface.
    This is what permits represented equality elimination through an opaque
    conclusion-truth predicate after [K(d)] has returned child truth. *)
Definition coqRestrictedPADirectBottomChildFormulaEqualityTemplate
    : TemplateFormula :=
  tfEq coqRestrictedPADirectBottomChildConclusionTerm
    (embedPATerm rawFormulaBotCodeTerm).

Definition coqRestrictedPADirectBottomChildInterfaceAndEqualityTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectBottomChildInterfaceResultTemplate
    coqRestrictedPADirectBottomChildFormulaEqualityTemplate.

(** Unlike the frozen case context, this ready context contains the
    admissibility premise before the recursive call.  Its head ordering is
    chosen so two represented Imp-I steps later produce
    [Admissible -> ContextTruth -> ...]. *)
Definition coqRestrictedPADirectBottomAdmissibleContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectBottomAdmissibleTemplate ::
    coqRestrictedPADirectBottomCaseContext tail.

Definition coqRestrictedPADirectBottomRecursiveReadyContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectBottomWitnessContextTruthTemplate ::
    coqRestrictedPADirectBottomAdmissibleContext tail.

Definition coqRestrictedPADirectBottomCoverageEigenContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate ::
    templateContextShift
      (coqRestrictedPADirectBottomRecursiveReadyContext tail).

Arguments coqRestrictedPADirectBottomAdmissibleContext tail : clear implicits.
Arguments coqRestrictedPADirectBottomRecursiveReadyContext tail
  : clear implicits.
Arguments coqRestrictedPADirectBottomCoverageEigenContext tail
  : clear implicits.

Lemma coqRestrictedPADirectBottom_child_interface_shape :
  coqRestrictedPADirectBottomChildInterfaceResultTemplate =
  tfAnd coqRestrictedPADirectBottomChildBelowTemplate
    (tfAnd coqRestrictedPADirectBottomChildRestrictedTemplate
      (tfAnd coqRestrictedPADirectBottomChildPredicateEndpointTemplate
        coqRestrictedPADirectBottomChildAdmissibleTemplate)).
Proof. reflexivity. Qed.

Definition coqRestrictedPADirectBottomChildRestrictedCoreTemplate
    : TemplateFormula :=
  coqRestrictedPADirectTemplateAndLeft
    coqRestrictedPADirectBottomChildRestrictedTemplate.

Lemma coqRestrictedPADirectBottom_child_below_shape :
  coqRestrictedPADirectBottomChildBelowTemplate =
  embedPAFormula
    (Formula.ltTermAt (tVar 2) (liftTerm 8 (tVar 4))).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectBottom_child_restricted_shape :
  coqRestrictedPADirectBottomChildRestrictedTemplate =
  tfAnd coqRestrictedPADirectBottomChildRestrictedCoreTemplate
    (tfAnd
      (embedPAFormula (proofAtomicallyAdequateTermAt (tVar 2)))
      (tfAnd
        (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 2)))
        (embedPAFormula (proofRuleCoverageTermAt (tVar 2))))).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectBottom_child_restricted_core_shape :
  coqRestrictedPADirectBottomChildRestrictedCoreTemplate =
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetProofContext (tVar 2)).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectBottom_child_endpoint_shape :
  coqRestrictedPADirectBottomChildPredicateEndpointTemplate =
  embedPAFormula
    (proofRuleValidTermAt (tVar 2) (tVar 7) (tVar 5)).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectBottom_child_admissible_shape :
  coqRestrictedPADirectBottomChildAdmissibleTemplate =
  tfAnd
    (tfAnd
      (embedPAFormula
        (codedFormulaAtomicallyAdequateTermAt (tVar 5)))
      (tfAnd
        (embedPAFormula
          (codedAssignmentDefinedThroughTermAt
            (tVar 9) (tVar 8) (tVar 5)))
        (restrictedTargetTemplateFormulaContext
          coqRestrictedPASoundnessLowerLevelTerm
          (restrictedTargetFormulaQuantifierBoundedContext (tVar 5)))))
    (embedPAFormula
      (pEx
        (pAnd
          (proofFormulaCoverageTermAt (tVar 3) (tVar 0))
          (codedAssignmentDefinedThroughTermAt
            (tVar 10) (tVar 9) (tVar 0))))).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectBottom_child_context_truth_shape :
  coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
    coqRestrictedPADirectBottomChildTerm
    coqRestrictedPADirectBottomWitnessContextTerm
    coqRestrictedPADirectBottomChildConclusionTerm =
  coqRestrictedPADirectBottomWitnessContextTruthTemplate.
Proof. reflexivity. Qed.

Definition coqRestrictedPADirectBottomChildConclusionTruthTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildTruthTemplate
    coqRestrictedPADirectBottomChildTerm
    coqRestrictedPADirectBottomWitnessContextTerm
    coqRestrictedPADirectBottomChildConclusionTerm.

Definition coqRestrictedPADirectBottomCurrentTruthTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     embedPATerm rawFormulaBotCodeTerm; ttVar 9; ttVar 8].

(** ------------------------------------------------------------------
    Constructor-generic descent specialized to Bot-E. *)

Lemma raw_bottom_recursive_child_data : forall
    (M : RawPAModel) root context conclusion child,
  root = rawProofBotERoot M context conclusion child ->
  RawProofConstructorCode M root context conclusion
      (raw_zero M) (raw_zero M) (raw_zero M)
      child (raw_zero M) (raw_zero M) /\
  In
    ([rawNumeralValue M 3; context; conclusion; child], [child])
    (rawProofRecursiveCases M context conclusion
      (raw_zero M) (raw_zero M) (raw_zero M)
      child (raw_zero M) (raw_zero M)) /\
  root = rawListCode M
    [rawNumeralValue M 3; context; conclusion; child] /\
  In child [child].
Proof.
  intros M root context conclusion child hcode.
  repeat split.
  - rewrite hcode. unfold RawProofConstructorCode, rawProofBotERoot.
    do 3 right. left. reflexivity.
  - unfold rawProofRecursiveCases. cbn. tauto.
  - exact hcode.
  - left. reflexivity.
Qed.

Theorem raw_bottom_child_interface : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    tail level root coverageBound context conclusion bottomCode child
      assignmentCode assignmentStep,
  RawCarrierRestrictedProofAt M tail level root ->
  RawProofAtomicallyAdequate M root ->
  RawProofFormulaCoverage M root coverageBound ->
  RawProofRuleCoverage M root ->
  root = rawProofBotERoot M context conclusion child ->
  RawProofEndpoint M child context bottomCode ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep coverageBound ->
  rawLt M child root /\
  RawCarrierRestrictedProofAt M tail level child /\
  RawProofAtomicallyAdequate M child /\
  RawProofFormulaCoverage M child coverageBound /\
  RawProofRuleCoverage M child /\
  RawProofRuleValid M child context bottomCode /\
  RawCodedFormulaAtomicallyAdequate M bottomCode /\
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep bottomCode /\
  RawCarrierFormulaQuantifierBounded M level bottomCode.
Proof.
  intros M hPA tail level root coverageBound context conclusion
    bottomCode child assignmentCode assignmentStep
    hrestricted hatomic hformulaCoverage hruleCoverage hcode
    hendpoint hassignmentCoverage.
  destruct (raw_bottom_recursive_child_data M root context conclusion child
    hcode) as [hconstructor [hentry [hfields hin]]].
  exact
    (raw_recursive_constructor_child_interface
      M hPA tail level root coverageBound context
      conclusion (raw_zero M) (raw_zero M) (raw_zero M)
      child (raw_zero M) (raw_zero M)
      [rawNumeralValue M 3; context; conclusion; child] [child]
      child bottomCode assignmentCode assignmentStep
      hrestricted hatomic hformulaCoverage hruleCoverage
      hconstructor hentry hfields hin hendpoint hassignmentCoverage).
Qed.

(** ------------------------------------------------------------------
    Semantic views of the represented child bundle. *)

Lemma raw_bottom_child_restricted_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectBottomChildRestrictedTemplate <->
  RawCarrierRestrictedProofAt M variables
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      (variables 2) /\
  RawProofAtomicallyAdequate M (variables 2) /\
  RawProofHasFormulaCoverage M (variables 2) /\
  RawProofRuleCoverage M (variables 2).
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPADirectBottom_child_restricted_shape.
  cbn [rawTemplateFormulaSat].
  rewrite coqRestrictedPADirectBottom_child_restricted_core_shape.
  unfold coqRestrictedPASoundnessLowerLevelTerm.
  rewrite rawTemplateFormulaSat_restrictedTarget_parameter;
    [|apply restrictedTargetProofContext_seal_free].
  rewrite raw_carrierRestrictedProofContextSat_iff.
  repeat rewrite rawTemplateFormulaSat_embedPA.
  rewrite raw_sat_proofAtomicallyAdequateTermAt_iff,
    raw_sat_proofHasFormulaCoverageTermAt_iff,
    raw_sat_proofRuleCoverageTermAt_iff.
  cbn [raw_term_eval]. reflexivity.
Qed.

Lemma raw_bottom_child_endpoint_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectBottomChildPredicateEndpointTemplate <->
  RawProofRuleValid M (variables 2) (variables 7) (variables 5).
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPADirectBottom_child_endpoint_shape.
  rewrite rawTemplateFormulaSat_embedPA.
  rewrite raw_sat_proofRuleValidTermAt_iff.
  cbn [raw_term_eval]. reflexivity.
Qed.

Lemma raw_bottom_child_admissible_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectBottomChildAdmissibleTemplate <->
  RawCodedFormulaAtomicallyAdequate M (variables 5) /\
  RawCodedAssignmentDefinedThrough M
    (variables 9) (variables 8) (variables 5) /\
  RawCarrierFormulaQuantifierBounded M
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 5) /\
  exists coverageBound,
    RawProofFormulaCoverage M (variables 2) coverageBound /\
    RawCodedAssignmentDefinedThrough M
      (variables 9) (variables 8) coverageBound.
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPADirectBottom_child_admissible_shape.
  cbn [rawTemplateFormulaSat].
  repeat rewrite rawTemplateFormulaSat_embedPA.
  rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff,
    raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  unfold coqRestrictedPASoundnessLowerLevelTerm.
  rewrite rawTemplateFormulaSat_restrictedTarget_parameter;
    [|apply restrictedTargetFormulaQuantifierBoundedContext_seal_free].
  rewrite raw_restrictedTargetFormulaQuantifierBoundedContextSat_iff.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofFormulaCoverageTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  cbn [raw_term_eval scons]. tauto.
Qed.

Lemma raw_bottom_child_interface_renamed_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    (templateFormulaRename S
      coqRestrictedPADirectBottomChildInterfaceResultTemplate) <->
  rawLt M (variables 3) (variables 13) /\
  RawCarrierRestrictedProofAt M (fun index => variables (S index))
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      (variables 3) /\
  RawProofAtomicallyAdequate M (variables 3) /\
  RawProofHasFormulaCoverage M (variables 3) /\
  RawProofRuleCoverage M (variables 3) /\
  RawProofRuleValid M (variables 3) (variables 8) (variables 6) /\
  RawCodedFormulaAtomicallyAdequate M (variables 6) /\
  RawCodedAssignmentDefinedThrough M
    (variables 10) (variables 9) (variables 6) /\
  RawCarrierFormulaQuantifierBounded M
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 6) /\
  exists coverageBound,
    RawProofFormulaCoverage M (variables 3) coverageBound /\
    RawCodedAssignmentDefinedThrough M
      (variables 10) (variables 9) coverageBound.
Proof.
  intros M variables parameters predicates.
  rewrite rawTemplateFormulaSat_rename.
  rewrite coqRestrictedPADirectBottom_child_interface_shape.
  cbn [rawTemplateFormulaSat].
  rewrite coqRestrictedPADirectBottom_child_below_shape.
  rewrite rawTemplateFormulaSat_embedPA, raw_sat_ltTermAt_iff.
  cbn [raw_term_eval]. repeat rewrite raw_term_eval_liftTerm.
  rewrite raw_bottom_child_restricted_sat_iff,
    raw_bottom_child_endpoint_sat_iff,
    raw_bottom_child_admissible_sat_iff.
  tauto.
Qed.

(** ------------------------------------------------------------------
    The fixed arithmetic source under the coverage eigenvariable. *)

Definition coqRestrictedPADirectBottomOpenedCoverageCompilerLawTemplate
    : TemplateFormula :=
  tfImp
    (templateFormulaRename S
      coqRestrictedPADirectOrIntroductionLeftDeepRestrictedCoreTemplate)
    (tfImp
      (templateFormulaRename S
        coqRestrictedPADirectOrIntroductionLeftDeepAtomicTemplate)
      (tfImp
        (templateFormulaRename S
          coqRestrictedPADirectOrIntroductionLeftDeepRuleCoverageTemplate)
        (tfImp
          coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate
          (tfImp
            (templateFormulaRename S
              coqRestrictedPADirectBottomCaseTemplate)
            (templateFormulaRename S
              coqRestrictedPADirectBottomChildInterfaceAndEqualityTemplate))))).

Definition RawCoqRestrictedPADirectBottomOpenedCoverageCompilerLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectBottomCoverageEigenContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectBottomOpenedCoverageCompilerLawTemplate)
      root.

Arguments RawCoqRestrictedPADirectBottomOpenedCoverageCompilerLawRoot
  M hPA inputs tail : clear implicits.

Theorem raw_coqRestrictedPADirectBottomOpenedCoverageLaw_valid : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectBottomOpenedCoverageCompilerLawTemplate.
Proof.
  intros M hPA variables parameters predicates.
  unfold coqRestrictedPADirectBottomOpenedCoverageCompilerLawTemplate.
  cbn [rawTemplateFormulaSat].
  intros hrestricted hatomic hruleCoverage hcommonCoverage hcase.

  rewrite rawTemplateFormulaSat_rename in hrestricted.
  unfold coqRestrictedPADirectOrIntroductionLeftDeepRestrictedCoreTemplate
    in hrestricted.
  rewrite rawTemplateFormulaSat_rawCoqTemplateRenameN in hrestricted.
  unfold coqRestrictedPADerivationSoundnessRestrictedProofCoreTemplate,
    coqRestrictedPASoundnessLowerLevelTerm in hrestricted.
  rewrite rawTemplateFormulaSat_restrictedTarget_parameter in hrestricted;
    [|apply restrictedTargetProofContext_seal_free].
  apply (proj1 (raw_carrierRestrictedProofContextSat_iff M
    (fun index => variables (S (index + 8)))
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (tVar 4))) in hrestricted.
  cbn [raw_term_eval] in hrestricted.

  rewrite rawTemplateFormulaSat_rename in hatomic.
  unfold coqRestrictedPADirectOrIntroductionLeftDeepAtomicTemplate
    in hatomic.
  rewrite rawTemplateFormulaSat_rawCoqTemplateRenameN in hatomic.
  rewrite rawTemplateFormulaSat_embedPA in hatomic.
  rewrite raw_sat_proofAtomicallyAdequateTermAt_iff in hatomic.
  cbn [raw_term_eval] in hatomic.

  rewrite rawTemplateFormulaSat_rename in hruleCoverage.
  unfold coqRestrictedPADirectOrIntroductionLeftDeepRuleCoverageTemplate
    in hruleCoverage.
  rewrite rawTemplateFormulaSat_rawCoqTemplateRenameN in hruleCoverage.
  rewrite rawTemplateFormulaSat_embedPA in hruleCoverage.
  rewrite raw_sat_proofRuleCoverageTermAt_iff in hruleCoverage.
  cbn [raw_term_eval] in hruleCoverage.

  rewrite coqRestrictedPADirectOrIntroductionLeft_common_coverage_body_shape
    in hcommonCoverage.
  rewrite rawTemplateFormulaSat_embedPA in hcommonCoverage.
  cbn [raw_formula_sat] in hcommonCoverage.
  rewrite raw_sat_proofFormulaCoverageTermAt_iff,
    raw_sat_codedAssignmentDefinedThroughTermAt_iff in hcommonCoverage.
  cbn [raw_term_eval] in hcommonCoverage.
  destruct hcommonCoverage as [hparentCoverage hassignmentCoverage].

  rewrite rawTemplateFormulaSat_rename in hcase.
  rewrite coqRestrictedPADirectBottom_case_shape in hcase.
  cbn [rawTemplateFormulaSat] in hcase.
  destruct hcase as
    [hcode [_conclusion [hformula [hendpoint _terminal]]]].
  unfold coqRestrictedPADirectBottomCodeEqualityTemplate in hcode.
  rewrite rawTemplateFormulaSat_embedPA in hcode.
  cbn [raw_formula_sat raw_term_eval] in hcode.
  unfold coqRestrictedPADirectBottomFormulaCodeTemplate in hformula.
  rewrite rawTemplateFormulaSat_embedPA in hformula.
  rewrite raw_sat_formulaBotCodeTermAt_iff in hformula.
  cbn [raw_term_eval] in hformula.
  unfold coqRestrictedPADirectBottomChildEndpointTemplate in hendpoint.
  rewrite rawTemplateFormulaSat_embedPA in hendpoint.
  rewrite raw_sat_proofEndpointTermAt_iff in hendpoint.
  cbn [raw_term_eval] in hendpoint.

  pose proof (raw_bottom_child_interface M hPA
    (fun index => variables (S (index + 8)))
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 13) (variables 0) (variables 8)
    (variables 7) (variables 6) (variables 3)
    (variables 10) (variables 9)
    hrestricted hatomic hparentCoverage hruleCoverage hcode
    hendpoint hassignmentCoverage) as hinterface.
  apply (proj2 (rawTemplateFormulaSat_rename M variables parameters
    predicates S coqRestrictedPADirectBottomChildInterfaceAndEqualityTemplate)).
  cbn [rawTemplateFormulaSat]. split.
  - apply (proj2 (raw_bottom_child_interface_renamed_sat_iff
      M variables parameters predicates)).
    destruct hinterface as
      [hbelow [hchildRestricted [hchildAtomic [hchildCoverage
        [hchildRuleCoverage [hchildRuleValid
          [hformulaAtomic [hformulaDefined hformulaBounded]]]]]]]].
    repeat split; try assumption.
    + exists (variables 0). exact hchildCoverage.
    + exists (variables 0). split; assumption.
  - cbn [rawTemplateFormulaSat raw_term_eval].
    exact hformula.
Qed.

Definition coqRestrictedPADirectBottomOpenedCoverageSourceBodyTemplate
    : TemplateFormula :=
  templateFormulaAbstractParameter
    coqRestrictedPASoundnessLowerLevelParameterName
    coqRestrictedPADirectBottomOpenedCoverageCompilerLawTemplate.

Definition coqRestrictedPADirectBottomOpenedCoverageSourceBodyFormula
    : formula :=
  match templateFormulaAsPAFormula
    coqRestrictedPADirectBottomOpenedCoverageSourceBodyTemplate with
  | Some output => output
  | None => pBot
  end.

Definition coqRestrictedPADirectBottomOpenedCoverageSourceFormula
    : formula :=
  pAll coqRestrictedPADirectBottomOpenedCoverageSourceBodyFormula.

Lemma coqRestrictedPADirectBottomOpenedCoverageSource_reifies :
  templateFormulaAsPAFormula
    coqRestrictedPADirectBottomOpenedCoverageSourceBodyTemplate =
  Some coqRestrictedPADirectBottomOpenedCoverageSourceBodyFormula.
Proof. vm_compute. reflexivity. Qed.

Theorem coqRestrictedPADirectBottomOpenedCoverageSource_embed :
  embedPAFormula coqRestrictedPADirectBottomOpenedCoverageSourceBodyFormula =
  coqRestrictedPADirectBottomOpenedCoverageSourceBodyTemplate.
Proof.
  apply templateFormulaAsPAFormula_sound.
  exact coqRestrictedPADirectBottomOpenedCoverageSource_reifies.
Qed.

Theorem coqRestrictedPADirectBottomOpenedCoverageSource_open :
  templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
    (embedPAFormula
      coqRestrictedPADirectBottomOpenedCoverageSourceBodyFormula) =
  coqRestrictedPADirectBottomOpenedCoverageCompilerLawTemplate.
Proof.
  rewrite coqRestrictedPADirectBottomOpenedCoverageSource_embed.
  apply templateFormulaAbstractParameter_open.
Qed.

Lemma rawDirect_bottomOpenedCoverageSourceBody_agreement : forall
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
    (embedPAFormula
      coqRestrictedPADirectBottomOpenedCoverageSourceBodyFormula) =
  rawQuotedFormulaCode M
    coqRestrictedPADirectBottomOpenedCoverageSourceBodyFormula.
Proof.
  intros M inputs. unfold rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

Theorem rawDirect_bottomOpenedCoverageSource_substitution : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedFormulaSingleSubstitution M
    (rawDirectTemplateTerm inputs coqRestrictedPASoundnessLowerLevelTerm)
    (rawQuotedFormulaCode M
      coqRestrictedPADirectBottomOpenedCoverageSourceBodyFormula)
    (rawDirectTemplateFormula inputs
      coqRestrictedPADirectBottomOpenedCoverageCompilerLawTemplate).
Proof.
  intros M hPA inputs.
  pose proof (rawDirectTemplateFormula_open M hPA inputs
    (embedPAFormula
      coqRestrictedPADirectBottomOpenedCoverageSourceBodyFormula)
    coqRestrictedPASoundnessLowerLevelTerm) as hopen.
  rewrite rawDirect_bottomOpenedCoverageSourceBody_agreement in hopen.
  rewrite coqRestrictedPADirectBottomOpenedCoverageSource_open in hopen.
  exact hopen.
Qed.

Theorem raw_coqRestrictedPADirectBottomOpenedCoverageSource_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall variables,
  raw_formula_sat M variables
    coqRestrictedPADirectBottomOpenedCoverageSourceFormula.
Proof.
  intros M hPA variables.
  unfold coqRestrictedPADirectBottomOpenedCoverageSourceFormula.
  cbn [raw_formula_sat]. intro level.
  pose (parameters :=
    (fun _ : TemplateParameterName => raw_zero M)).
  pose (predicates :=
    (fun (_ : TemplatePredicateName) (_ : list M) => True)).
  apply (proj1 (rawTemplateFormulaSat_embedPA M
    (scons M level variables) parameters predicates
    coqRestrictedPADirectBottomOpenedCoverageSourceBodyFormula)).
  rewrite coqRestrictedPADirectBottomOpenedCoverageSource_embed.
  unfold coqRestrictedPADirectBottomOpenedCoverageSourceBodyTemplate.
  apply (proj2 (rawTemplateFormulaSat_abstractParameter M
    variables parameters predicates
    coqRestrictedPASoundnessLowerLevelParameterName level
    coqRestrictedPADirectBottomOpenedCoverageCompilerLawTemplate)).
  apply raw_coqRestrictedPADirectBottomOpenedCoverageLaw_valid.
  exact hPA.
Qed.

Theorem PA_proves_coqRestrictedPADirectBottomOpenedCoverageSource :
  Formula.BProv Formula.Ax_s []
    coqRestrictedPADirectBottomOpenedCoverageSourceFormula.
Proof.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA
        coqRestrictedPADirectBottomOpenedCoverageSourceFormula)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA variables.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact
        (raw_coqRestrictedPADirectBottomOpenedCoverageSource_valid
          M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename Formula.Ax_s []
    coqRestrictedPADirectBottomOpenedCoverageSourceFormula
    (fun index => index) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

(** ------------------------------------------------------------------
    Compile the fixed source below a selected standard PA tail. *)

Lemma coqRestrictedPADirectBottomRecursiveReadyContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectBottomRecursiveReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectBottomRecursiveReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  unfold coqRestrictedPADirectBottomRecursiveReadyContext,
    coqRestrictedPADirectBottomAdmissibleContext.
  cbn [List.app].
  now rewrite coqRestrictedPADirectBottomCaseContext_app_witnesses.
Qed.

(** The eigenvariable shifts every inherited local formula once.  Embedded
    witnessed PA axioms are sentences, so the standard tail is unchanged. *)
Lemma coqRestrictedPADirectBottomCoverageEigenContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectBottomCoverageEigenContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectBottomCoverageEigenContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  unfold coqRestrictedPADirectBottomCoverageEigenContext.
  rewrite coqRestrictedPADirectBottomRecursiveReadyContext_app_witnesses.
  unfold templateContextShift, templateContextRename.
  rewrite map_app. cbn [List.app].
  rewrite templateContextShift_embedPAAxiomWitnesses.
  reflexivity.
Qed.

Lemma raw_bottomCoverageEigenContext_witnessed_code : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall witnesses,
  rawTemplateContextCode translation
    (coqRestrictedPADirectBottomCoverageEigenContext
      (embedPAContext (map witnessedAxiom witnesses))) =
  rawTemplateContextCodeOnTail translation
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (coqRestrictedPADirectBottomCoverageEigenContext []).
Proof.
  intros M translation hagreement witnesses.
  rewrite coqRestrictedPADirectBottomCoverageEigenContext_app_witnesses.
  rewrite rawTemplateContextCode_app_on_tail.
  assert (htail : rawTemplateContextCode translation
      (embedPAContext (map witnessedAxiom witnesses)) =
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)).
  {
    rewrite rawTemplateContextCode_as_on_tail.
    apply (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
      M translation hagreement witnesses (raw_zero M)).
  }
  now rewrite htail.
Qed.

Theorem raw_codedPALocalProof_bottomOpenedCoverageLaw_on_witnessed_base :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext)
        (coqRestrictedPADirectBottomCoverageEigenContext []))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectBottomOpenedCoverageCompilerLawTemplate)
      root.
Proof.
  intros M hPA inputs baseWitnessList baseContext hbase.
  exact
    (raw_codedPALocalProof_universalSourceInstance_under_directPrefix
      M hPA inputs baseWitnessList baseContext
      coqRestrictedPADirectBottomOpenedCoverageSourceBodyFormula
      (rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm)
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectBottomOpenedCoverageCompilerLawTemplate)
      (coqRestrictedPADirectBottomCoverageEigenContext [])
      hbase
      PA_proves_coqRestrictedPADirectBottomOpenedCoverageSource
      (rawDirect_bottomOpenedCoverageSource_substitution M hPA inputs)).
Qed.

Corollary raw_bottomOpenedCoverageCompilerLawRoot_on_selected_witnessed_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectBottomOpenedCoverageCompilerLawRoot
      M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).
Proof.
  intros M hPA inputs.
  assert (hempty : RawCodedPAAxiomWitnessContext M
      (raw_zero M) (raw_zero M)).
  {
    pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
    cbn [rawQuotedPAAxiomWitnessList rawListCode map] in h.
    exact h.
  }
  destruct (raw_codedPALocalProof_bottomOpenedCoverageLaw_on_witnessed_base
    M hPA inputs (raw_zero M) (raw_zero M) hempty)
    as (witnesses & root & hwitnessed & hroot).
  exists witnesses. split.
  - rewrite rawTemplateContextCode_as_on_tail.
    rewrite (raw_templateContextCodeOnTail_embedPAAxiomWitnesses M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      witnesses (raw_zero M)).
    exact hwitnessed.
  - exists root.
    rewrite (raw_bottomCoverageEigenContext_witnessed_code M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      witnesses).
    exact hroot.
Qed.

(** ------------------------------------------------------------------
    Consume the opened bundle and invoke the recursive hypothesis. *)

(** These are definitional identifications, recorded explicitly so the proof
    below documents which generic And-I/Or-I interfaces Bottom-E reuses. *)
Lemma coqRestrictedPADirectBottom_restricted_agrees_with_deep :
  coqRestrictedPADirectBottomRestrictedProofTemplate =
  coqRestrictedPADirectOrIntroductionLeftDeepRestrictedTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectBottom_admissible_agrees_with_deep :
  coqRestrictedPADirectBottomAdmissibleTemplate =
  coqRestrictedPADirectOrIntroductionLeftDeepAdmissibleTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectBottom_prefix_agrees_with_child_prefix :
  coqRestrictedPADirectBottomStrongPrefixTemplate =
  coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectBottom_ready_context_truth_in : forall tail,
  In coqRestrictedPADirectBottomWitnessContextTruthTemplate
    (coqRestrictedPADirectBottomRecursiveReadyContext tail).
Proof. intro tail. left. reflexivity. Qed.

Lemma coqRestrictedPADirectBottom_ready_admissible_in : forall tail,
  In coqRestrictedPADirectBottomAdmissibleTemplate
    (coqRestrictedPADirectBottomRecursiveReadyContext tail).
Proof. intro tail. right. left. reflexivity. Qed.

Lemma coqRestrictedPADirectBottom_ready_case_in : forall tail,
  In coqRestrictedPADirectBottomCaseTemplate
    (coqRestrictedPADirectBottomRecursiveReadyContext tail).
Proof. intro tail. right. right. left. reflexivity. Qed.

Lemma coqRestrictedPADirectBottom_ready_restricted_in : forall tail,
  In coqRestrictedPADirectBottomRestrictedProofTemplate
    (coqRestrictedPADirectBottomRecursiveReadyContext tail).
Proof.
  intro tail. right. right.
  exact (coqRestrictedPADirectBottom_restricted_in_case_context tail).
Qed.

Lemma coqRestrictedPADirectBottom_ready_prefix_in : forall tail,
  In coqRestrictedPADirectBottomStrongPrefixTemplate
    (coqRestrictedPADirectBottomRecursiveReadyContext tail).
Proof.
  intro tail. right. right.
  exact (coqRestrictedPADirectBottom_strongPrefix_in_case_context tail).
Qed.

Lemma coqRestrictedPADirectBottom_eigen_inherited : forall tail formula,
  In formula (coqRestrictedPADirectBottomRecursiveReadyContext tail) ->
  In (templateFormulaRename S formula)
    (coqRestrictedPADirectBottomCoverageEigenContext tail).
Proof.
  intros tail formula hin.
  unfold coqRestrictedPADirectBottomCoverageEigenContext,
    templateContextShift, templateContextRename.
  right. apply in_map. exact hin.
Qed.

Lemma coqRestrictedPADirectBottom_eigen_coverage_body_in : forall tail,
  In coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate
    (coqRestrictedPADirectBottomCoverageEigenContext tail).
Proof. intro tail. left. reflexivity. Qed.

(** Equality elimination substitutes the child's displayed conclusion code in
    precisely one opaque-truth argument.  Variables [10] and [9] in the
    motive lower to the current assignment variables [9] and [8]. *)
Definition coqRestrictedPADirectBottomConclusionTruthMotiveTemplate
    : TemplateFormula :=
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     ttVar 0; ttVar 10; ttVar 9].

Lemma coqRestrictedPADirectBottomConclusionTruthMotive_child_open :
  templateFormulaOpen coqRestrictedPADirectBottomChildConclusionTerm
    coqRestrictedPADirectBottomConclusionTruthMotiveTemplate =
  coqRestrictedPADirectBottomChildConclusionTruthTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPADirectBottomConclusionTruthMotive_bottom_open :
  templateFormulaOpen (embedPATerm rawFormulaBotCodeTerm)
    coqRestrictedPADirectBottomConclusionTruthMotiveTemplate =
  coqRestrictedPADirectBottomCurrentTruthTemplate.
Proof. vm_compute. reflexivity. Qed.

(** This theorem is the substantive Bottom-E result.  The common coverage
    existential is opened only long enough to compile the child interface;
    Ex-E then returns the complete bundle to the ready context before [K(d)]
    is applied.  Finally, represented equality elimination changes the
    child's displayed conclusion code to the literal bottom-formula code. *)
Theorem raw_bottomCurrentTruth_of_openedCoverageCompiler : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectBottomOpenedCoverageCompilerLawRoot
    M hPA inputs tail ->
  exists truthRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectBottomRecursiveReadyContext tail))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqRestrictedPADirectBottomCurrentTruthTemplate)
      truthRoot.
Proof.
  intros M hPA inputs tail (openedRoot & hopened).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (readyContext :=
    coqRestrictedPADirectBottomRecursiveReadyContext tail).
  set (eigenContext :=
    coqRestrictedPADirectBottomCoverageEigenContext tail).
  set (readyCode := rawTemplateContextCode translation readyContext).
  set (eigenCode := rawTemplateContextCode translation eigenContext).

  (** Project the common coverage existential from the admissibility row. *)
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation readyContext
      coqRestrictedPADirectBottomAdmissibleTemplate
      (coqRestrictedPADirectBottom_ready_admissible_in tail))
    as hadmissible.
  rewrite coqRestrictedPADirectBottom_admissible_agrees_with_deep
    in hadmissible.
  rewrite coqRestrictedPADirectOrIntroductionLeft_deep_admissible_shape
    in hadmissible.
  rewrite rawTemplateFormula_and in hadmissible.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _ hadmissible)
    as hcommonCoverage.
  rewrite coqRestrictedPADirectOrIntroductionLeft_common_coverage_ex_shape
    in hcommonCoverage.
  rewrite rawTemplateFormula_ex in hcommonCoverage.

  (** Split the inherited strengthened restriction in the eigencontext. *)
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        coqRestrictedPADirectBottomRestrictedProofTemplate)
      (coqRestrictedPADirectBottom_eigen_inherited tail _
        (coqRestrictedPADirectBottom_ready_restricted_in tail)))
    as hrestrictedEigen.
  rewrite coqRestrictedPADirectBottom_restricted_agrees_with_deep
    in hrestrictedEigen.
  rewrite coqRestrictedPADirectOrIntroductionLeft_deep_restricted_shape
    in hrestrictedEigen.
  cbn [templateFormulaRename] in hrestrictedEigen.
  rewrite rawTemplateFormula_and in hrestrictedEigen.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _
    hrestrictedEigen) as hrestrictedCore.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _
    hrestrictedEigen) as hrestrictedTail.
  rewrite rawTemplateFormula_and in hrestrictedTail.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _
    hrestrictedTail) as hatomic.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _
    hrestrictedTail) as hcoverageTail.
  rewrite rawTemplateFormula_and in hcoverageTail.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _
    hcoverageTail) as hruleCoverage.

  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate
      (coqRestrictedPADirectBottom_eigen_coverage_body_in tail))
    as hcoverageBody.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S coqRestrictedPADirectBottomCaseTemplate)
      (coqRestrictedPADirectBottom_eigen_inherited tail _
        (coqRestrictedPADirectBottom_ready_case_in tail)))
    as hcase.

  (** Apply the fixed arithmetic compiler to its five literal premises. *)
  unfold coqRestrictedPADirectBottomOpenedCoverageCompilerLawTemplate
    in hopened.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ openedRoot _
      hopened hrestrictedCore) as hopened1.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _
      hopened1 hatomic) as hopened2.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _
      hopened2 hruleCoverage) as hopened3.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _
      hopened3 hcoverageBody) as hopened4.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _
      hopened4 hcase) as hshiftedPair.

  (** Close the coverage eigenvariable while retaining both the child
      interface and its formula-code equality. *)
  pose proof
    (raw_codedPALocalProofOf_exE M hPA readyCode
      (rawTemplateContextCode translation (templateContextShift readyContext))
      (rawTemplateFormula translation
        coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomChildInterfaceAndEqualityTemplate)
      (rawTemplateFormula translation
        (templateFormulaRename S
          coqRestrictedPADirectBottomChildInterfaceAndEqualityTemplate))
      _ _ hcommonCoverage
      (raw_templateContext_shift M hPA translation readyContext)
      (rawTemplateFormula_shift translation
        coqRestrictedPADirectBottomChildInterfaceAndEqualityTemplate)
      hshiftedPair) as hpair.
  unfold coqRestrictedPADirectBottomChildInterfaceAndEqualityTemplate
    in hpair.
  rewrite rawTemplateFormula_and in hpair.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _ hpair)
    as hinterface.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _ hpair)
    as hformulaEquality.

  (** The other two [K(d)] inputs are inherited assumptions. *)
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation readyContext
      coqRestrictedPADirectBottomStrongPrefixTemplate
      (coqRestrictedPADirectBottom_ready_prefix_in tail))
    as hprefix.
  rewrite coqRestrictedPADirectBottom_prefix_agrees_with_child_prefix
    in hprefix.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation readyContext
      coqRestrictedPADirectBottomWitnessContextTruthTemplate
      (coqRestrictedPADirectBottom_ready_context_truth_in tail))
    as hcontextTruth.
  rewrite <- coqRestrictedPADirectBottom_child_context_truth_shape
    in hcontextTruth.
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionChildTruth
      M hPA translation readyContext
      coqRestrictedPADirectBottomChildTerm
      coqRestrictedPADirectBottomWitnessContextTerm
      coqRestrictedPADirectBottomChildConclusionTerm
      _ _ _ hinterface hprefix hcontextTruth)
    as [childTruthRoot hchildTruth].

  (** Transport the opaque truth atom along [childConclusion = botCode]. *)
  change (RawCodedPALocalProofOf M readyCode
    (rawTemplateFormula translation
      coqRestrictedPADirectBottomChildConclusionTruthTemplate)
    childTruthRoot) in hchildTruth.
  rewrite <- coqRestrictedPADirectBottomConclusionTruthMotive_child_open
    in hchildTruth.
  pose proof
    (raw_codedPALocalProofOf_templateEqElim M hPA translation readyCode
      coqRestrictedPADirectBottomChildConclusionTerm
      (embedPATerm rawFormulaBotCodeTerm)
      coqRestrictedPADirectBottomConclusionTruthMotiveTemplate
      _ childTruthRoot hformulaEquality hchildTruth) as hcurrentTruth.
  rewrite coqRestrictedPADirectBottomConclusionTruthMotive_bottom_open
    in hcurrentTruth.
  lazymatch type of hcurrentTruth with
  | RawCodedPALocalProofOf _ _ _ ?currentTruthRoot =>
      exists currentTruthRoot;
      exact hcurrentTruth
  end.
Qed.

(** The actual recursive Bottom-E producer, with the necessary admissibility
    row visible in its context.  Its standard-tail shape matches the frozen
    compiler interface except for that row and the assignment arguments of
    the opaque truth atom. *)
Definition
    RawCoqRestrictedPADirectBottomCurrentTruthUnderAdmissibilityStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists (suffix : StandardPAAxiomWitnessPrefix) (truthRoot : M),
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectBottomRecursiveReadyContext
          (embedPAContext
            (map witnessedAxiom (baseWitnesses ++ suffix)))))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqRestrictedPADirectBottomCurrentTruthTemplate)
      truthRoot.

Arguments
  RawCoqRestrictedPADirectBottomCurrentTruthUnderAdmissibilityStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem raw_bottomCurrentTruthUnderAdmissibility_standardTail : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectBottomCurrentTruthUnderAdmissibilityStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs baseWitnesses.
  destruct
    (raw_bottomOpenedCoverageCompilerLawRoot_on_selected_witnessed_tail
      M hPA inputs) as (witnesses & _hwitnessed & hopened).
  destruct (raw_bottomCurrentTruth_of_openedCoverageCompiler
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)) hopened)
    as [truthRoot htruth].
  rewrite coqRestrictedPADirectBottomRecursiveReadyContext_app_witnesses
    in htruth.
  destruct
    (raw_codedPALocalProof_standardWitnessTail_surround_under_prefix
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (coqRestrictedPADirectBottomRecursiveReadyContext [])
      baseWitnesses witnesses []
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqRestrictedPADirectBottomCurrentTruthTemplate)
      truthRoot htruth) as [transportedRoot htransported].
  exists witnesses, transportedRoot.
  cbn [List.app] in htransported.
  rewrite app_nil_r in htransported.
  rewrite coqRestrictedPADirectBottomRecursiveReadyContext_app_witnesses.
  exact htransported.
Qed.

(** ------------------------------------------------------------------
    Exact factorization of the historical frozen residual. *)

(** This implication is the assignment-code transport still needed from the
    native closed-formula truth development.  It changes no formula code and
    no structural premise: only the last two opaque-predicate arguments move
    from the current assignment [(9,8)] to the canonical assignment [(0,0)]. *)
Definition coqRestrictedPADirectBottomCurrentAssignmentNormalizationTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectBottomCurrentTruthTemplate
    coqRestrictedPADirectBottomClosedTruthTemplate.

(** Once current truth has been normalized, two Imp-I steps give this honest
    law in the original case context.  Notice that admissibility remains an
    antecedent; it cannot be deleted merely by assignment-code transport. *)
Definition coqRestrictedPADirectBottomAdmissibleClosedTruthLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectBottomAdmissibleTemplate
    (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate
      coqRestrictedPADirectBottomClosedTruthTemplate).

(** This is the genuinely non-derivable structural step required by the old
    frozen residual.  It asks the object calculus to erase the admissibility
    antecedent even though that antecedent supplied the common coverage used
    to construct the recursive child interface. *)
Definition coqRestrictedPADirectBottomAdmissibilityErasureTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectBottomAdmissibleClosedTruthLawTemplate
    (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate
      coqRestrictedPADirectBottomClosedTruthTemplate).

Definition RawCoqRestrictedPADirectBottomCurrentTruthRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectBottomRecursiveReadyContext tail))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqRestrictedPADirectBottomCurrentTruthTemplate)
      root.

Definition RawCoqRestrictedPADirectBottomCurrentAssignmentNormalizationRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectBottomRecursiveReadyContext tail))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqRestrictedPADirectBottomCurrentAssignmentNormalizationTemplate)
      root.

Definition RawCoqRestrictedPADirectBottomAdmissibilityErasureRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectBottomCaseContext tail))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        coqRestrictedPADirectBottomAdmissibilityErasureTemplate)
      root.

Arguments RawCoqRestrictedPADirectBottomCurrentTruthRoot
  M hPA inputs tail : clear implicits.
Arguments RawCoqRestrictedPADirectBottomCurrentAssignmentNormalizationRoot
  M hPA inputs tail : clear implicits.
Arguments RawCoqRestrictedPADirectBottomAdmissibilityErasureRoot
  M hPA inputs tail : clear implicits.

(** At a common tail, the two named residuals are sufficient to recover the
    exact frozen law.  The proof is deliberately only propositional plumbing:
    normalization consumes current truth, the two assumptions are discharged,
    and erasure is applied last.  Therefore no semantic gap is hidden here. *)
Theorem raw_bottomRecursiveClosedTruthLawRoot_of_factored_residuals : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectBottomCurrentTruthRoot M hPA inputs tail ->
  RawCoqRestrictedPADirectBottomCurrentAssignmentNormalizationRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectBottomAdmissibilityErasureRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectBottomRecursiveClosedTruthLawRoot
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail
    (currentRoot & hcurrent) (normalizationRoot & hnormalization)
    (erasureRoot & herasure).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (caseCode := rawTemplateContextCode translation
    (coqRestrictedPADirectBottomCaseContext tail)).
  set (admissibleCode := rawTemplateContextCode translation
    (coqRestrictedPADirectBottomAdmissibleContext tail)).
  set (readyCode := rawTemplateContextCode translation
    (coqRestrictedPADirectBottomRecursiveReadyContext tail)).
  unfold coqRestrictedPADirectBottomCurrentAssignmentNormalizationTemplate
    in hnormalization.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation
      (coqRestrictedPADirectBottomRecursiveReadyContext tail)
      coqRestrictedPADirectBottomCurrentTruthTemplate
      coqRestrictedPADirectBottomClosedTruthTemplate
      normalizationRoot currentRoot hnormalization hcurrent)
    as hclosed.
  pose proof
    (raw_codedPALocalProofOf_impI M hPA admissibleCode
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomWitnessContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomClosedTruthTemplate)
      _ hclosed) as hwitnessLaw.
  pose proof
    (raw_codedPALocalProofOf_impI M hPA caseCode
      (rawTemplateFormula translation
        coqRestrictedPADirectBottomAdmissibleTemplate)
      (rawTemplateFormula translation
        (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate
          coqRestrictedPADirectBottomClosedTruthTemplate))
      _ hwitnessLaw) as hadmissibleLaw.
  unfold coqRestrictedPADirectBottomAdmissibilityErasureTemplate
    in herasure.
  unfold coqRestrictedPADirectBottomAdmissibleClosedTruthLawTemplate
    in hadmissibleLaw.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation (coqRestrictedPADirectBottomCaseContext tail)
      coqRestrictedPADirectBottomAdmissibleClosedTruthLawTemplate
      (tfImp coqRestrictedPADirectBottomWitnessContextTruthTemplate
        coqRestrictedPADirectBottomClosedTruthTemplate)
      erasureRoot _ herasure hadmissibleLaw) as hfrozen.
  lazymatch type of hfrozen with
  | RawCodedPALocalProofOf _ _ _ ?frozenRoot =>
      exists frozenRoot;
      exact hfrozen
  end.
Qed.

(** Standard-tail formulations make the two outstanding compiler contracts
    directly comparable with the frozen residual.  They are definitions, not
    assumptions introduced into the trusted environment. *)
Definition
    RawCoqRestrictedPADirectBottomCurrentAssignmentNormalizationStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectBottomCurrentAssignmentNormalizationRoot
      M hPA inputs
      (embedPAContext (map witnessedAxiom (baseWitnesses ++ suffix))).

Definition
    RawCoqRestrictedPADirectBottomAdmissibilityErasureStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall baseWitnesses : StandardPAAxiomWitnessPrefix,
  exists suffix : StandardPAAxiomWitnessPrefix,
    RawCoqRestrictedPADirectBottomAdmissibilityErasureRoot
      M hPA inputs
      (embedPAContext (map witnessedAxiom (baseWitnesses ++ suffix))).

Arguments
  RawCoqRestrictedPADirectBottomCurrentAssignmentNormalizationStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectBottomAdmissibilityErasureStandardTailCompiler
  M hPA inputs : clear implicits.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomRecursiveTruthAdmissibleBoundary.
