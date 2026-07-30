(**
  Covered recursive-child compilation for the left disjunction introduction
  branch.

  The public soundness predicate now carries proof-wide atomic adequacy,
  formula coverage, rule coverage, and a common assignment-coverage bound.
  This module records exactly how those resources enter the existing
  Or-I-left recursive residual.

  The only open operation below is structural.  It lives after the common
  coverage existential has been eliminated, receives the old restriction
  and admissibility cores plus the three proof-wide certificates and the
  literal constructor row, and returns the four facts consumed by [K(d)]:

    child < parent, child restrictedness, child rule validity,
    and child admissibility.

  It does not assume child truth or the existing recursive-child law.  Once
  that structural root is supplied, all existential elimination, prefix
  instantiation, context truth, and implication introduction are compiled
  here as model-coded PA proofs.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedAssignment
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedProofDescent
  RawCodedProofRules
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedFixedLevelTruthTotality
  RawCodedRestrictedPAProof
  RawCodedRestrictedProofAdmissibility
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedPALocalProofExistential
  RawCodedPALocalProofAndIntroduction
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofPropositionalRules
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedPADerivationSoundnessDirectRenamedChildTruth
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedProofAdmissibility.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRenamedChildTruth.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase.

(** ------------------------------------------------------------------
    Literal deep resources and the matching [K(d)] child instance. *)

Definition coqRestrictedPADirectOrIntroductionLeftDeepRestrictedTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate.

Definition
    coqRestrictedPADirectOrIntroductionLeftDeepRestrictedCoreTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessRestrictedProofCoreTemplate.

Definition coqRestrictedPADirectOrIntroductionLeftDeepAtomicTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    (embedPAFormula
      (proofAtomicallyAdequateTermAt (tVar 4))).

Definition coqRestrictedPADirectOrIntroductionLeftDeepHasCoverageTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    (embedPAFormula
      (proofHasFormulaCoverageTermAt (tVar 4))).

Definition coqRestrictedPADirectOrIntroductionLeftDeepRuleCoverageTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    (embedPAFormula
      (proofRuleCoverageTermAt (tVar 4))).

Definition coqRestrictedPADirectOrIntroductionLeftDeepAdmissibleTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAssumptionDeepAdmissibleTemplate.

Definition
    coqRestrictedPADirectOrIntroductionLeftDeepAdmissibleCoreTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessAdmissibleCoreTemplate.

Definition
    coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessCommonCoverageTemplate.

Definition coqRestrictedPADirectTemplateExBody
    (formula : TemplateFormula) : TemplateFormula :=
  match formula with
  | tfEx body => body
  | _ => tfBot
  end.

Definition
    coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate
    : TemplateFormula :=
  coqRestrictedPADirectTemplateExBody
    coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageTemplate.

Definition coqRestrictedPADirectOrIntroductionLeftChildTerm
    : TemplateTerm :=
  coqRestrictedPADirectAndIntroductionLeftChildTerm.

Definition coqRestrictedPADirectOrIntroductionLeftWitnessContextTerm
    : TemplateTerm :=
  coqRestrictedPADirectAndIntroductionWitnessContextTerm.

Definition coqRestrictedPADirectOrIntroductionLeftChildConclusionTerm
    : TemplateTerm :=
  coqRestrictedPADirectAndIntroductionLeftFormulaTerm.

Definition
    coqRestrictedPADirectOrIntroductionLeftChildInterfaceResultTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    coqRestrictedPADirectOrIntroductionLeftChildTerm
    coqRestrictedPADirectOrIntroductionLeftWitnessContextTerm
    coqRestrictedPADirectOrIntroductionLeftChildConclusionTerm.

Definition coqRestrictedPADirectOrIntroductionLeftChildBelowTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildBelowTemplate
    coqRestrictedPADirectOrIntroductionLeftChildTerm.

Definition coqRestrictedPADirectOrIntroductionLeftChildRestrictedTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildRestrictedTemplate
    coqRestrictedPADirectOrIntroductionLeftChildTerm
    coqRestrictedPADirectOrIntroductionLeftWitnessContextTerm
    coqRestrictedPADirectOrIntroductionLeftChildConclusionTerm.

Definition
    coqRestrictedPADirectOrIntroductionLeftChildPredicateEndpointTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildEndpointTemplate
    coqRestrictedPADirectOrIntroductionLeftChildTerm
    coqRestrictedPADirectOrIntroductionLeftWitnessContextTerm
    coqRestrictedPADirectOrIntroductionLeftChildConclusionTerm.

Definition coqRestrictedPADirectOrIntroductionLeftChildAdmissibleTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildAdmissibleTemplate
    coqRestrictedPADirectOrIntroductionLeftChildTerm
    coqRestrictedPADirectOrIntroductionLeftWitnessContextTerm
    coqRestrictedPADirectOrIntroductionLeftChildConclusionTerm.

Definition coqRestrictedPADirectTemplateAndLeft
    (formula : TemplateFormula) : TemplateFormula :=
  match formula with
  | tfAnd lhs _ => lhs
  | _ => tfBot
  end.

(** This is the first genuinely absent object-level operation.  The
    metatheoretic theorem [raw_restrictedProof_recursive_child] is stated at
    a fixed Rocq [level : nat]; the direct predicate instead contains a
    carrier-valued numeral-term parameter.  No existing PA proof root
    reroots that dynamic restriction core at the displayed child. *)
Definition
    coqRestrictedPADirectOrIntroductionLeftChildRestrictedCoreTemplate
    : TemplateFormula :=
  coqRestrictedPADirectTemplateAndLeft
    coqRestrictedPADirectAndIntroductionLeftRestrictedTemplate.

Lemma coqRestrictedPADirectOrIntroductionLeft_child_interface_shape :
  coqRestrictedPADirectOrIntroductionLeftChildInterfaceResultTemplate =
  tfAnd coqRestrictedPADirectOrIntroductionLeftChildBelowTemplate
    (tfAnd coqRestrictedPADirectOrIntroductionLeftChildRestrictedTemplate
      (tfAnd
        coqRestrictedPADirectOrIntroductionLeftChildPredicateEndpointTemplate
        coqRestrictedPADirectOrIntroductionLeftChildAdmissibleTemplate)).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_child_below_shape :
  coqRestrictedPADirectOrIntroductionLeftChildBelowTemplate =
  embedPAFormula
    (Formula.ltTermAt (tVar 2) (liftTerm 8 (tVar 4))).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_child_restricted_shape :
  coqRestrictedPADirectOrIntroductionLeftChildRestrictedTemplate =
  tfAnd coqRestrictedPADirectOrIntroductionLeftChildRestrictedCoreTemplate
    (tfAnd
      (embedPAFormula (proofAtomicallyAdequateTermAt (tVar 2)))
      (tfAnd
        (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 2)))
        (embedPAFormula (proofRuleCoverageTermAt (tVar 2))))).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_child_predicate_endpoint_shape :
  coqRestrictedPADirectOrIntroductionLeftChildPredicateEndpointTemplate =
  embedPAFormula
    (proofRuleValidTermAt (tVar 2) (tVar 7) (tVar 6)).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_child_admissible_shape :
  coqRestrictedPADirectOrIntroductionLeftChildAdmissibleTemplate =
  tfAnd
    (tfAnd
      (embedPAFormula
        (codedFormulaAtomicallyAdequateTermAt (tVar 6)))
      (tfAnd
        (embedPAFormula
          (codedAssignmentDefinedThroughTermAt
            (tVar 9) (tVar 8) (tVar 6)))
        (restrictedTargetTemplateFormulaContext
          coqRestrictedPASoundnessLowerLevelTerm
          (restrictedTargetFormulaQuantifierBoundedContext (tVar 6)))))
    (embedPAFormula
      (pEx
        (pAnd
          (proofFormulaCoverageTermAt (tVar 3) (tVar 0))
          (codedAssignmentDefinedThroughTermAt
            (tVar 10) (tVar 9) (tVar 0))))).
Proof. reflexivity. Qed.

Lemma
    coqRestrictedPADirectOrIntroductionLeft_deep_restricted_shape :
  coqRestrictedPADirectOrIntroductionLeftDeepRestrictedTemplate =
  tfAnd
    coqRestrictedPADirectOrIntroductionLeftDeepRestrictedCoreTemplate
    (tfAnd
      coqRestrictedPADirectOrIntroductionLeftDeepAtomicTemplate
      (tfAnd
        coqRestrictedPADirectOrIntroductionLeftDeepHasCoverageTemplate
        coqRestrictedPADirectOrIntroductionLeftDeepRuleCoverageTemplate)).
Proof. reflexivity. Qed.

Lemma
    coqRestrictedPADirectOrIntroductionLeft_deep_admissible_shape :
  coqRestrictedPADirectOrIntroductionLeftDeepAdmissibleTemplate =
  tfAnd
    coqRestrictedPADirectOrIntroductionLeftDeepAdmissibleCoreTemplate
    coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageTemplate.
Proof. reflexivity. Qed.

Lemma
    coqRestrictedPADirectOrIntroductionLeft_common_coverage_ex_shape :
  coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageTemplate =
  tfEx
    coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_common_coverage_body_shape :
  coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate =
  embedPAFormula
    (pAnd
      (proofFormulaCoverageTermAt (tVar 13) (tVar 0))
      (codedAssignmentDefinedThroughTermAt
        (tVar 10) (tVar 9) (tVar 0))).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_child_context_truth_agreement :
  coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
    coqRestrictedPADirectOrIntroductionLeftChildTerm
    coqRestrictedPADirectOrIntroductionLeftWitnessContextTerm
    coqRestrictedPADirectOrIntroductionLeftChildConclusionTerm =
  coqRestrictedPADirectAssumptionWitnessContextTruthTemplate.
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_child_truth_agreement :
  coqRestrictedPADirectAndIntroductionChildTruthTemplate
    coqRestrictedPADirectOrIntroductionLeftChildTerm
    coqRestrictedPADirectOrIntroductionLeftWitnessContextTerm
    coqRestrictedPADirectOrIntroductionLeftChildConclusionTerm =
  coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    The two implication assumptions and the coverage eigenvariable. *)

Definition coqRestrictedPADirectOrIntroductionLeftLawEndpointContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectOrIntroductionLeftChildEndpointTemplate ::
    coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext tail.

Definition coqRestrictedPADirectOrIntroductionLeftLawBodyContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectAssumptionWitnessContextTruthTemplate ::
    coqRestrictedPADirectOrIntroductionLeftLawEndpointContext tail.

Definition coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate ::
    templateContextShift
      (coqRestrictedPADirectOrIntroductionLeftLawBodyContext tail).

Arguments coqRestrictedPADirectOrIntroductionLeftLawEndpointContext
  tail : clear implicits.
Arguments coqRestrictedPADirectOrIntroductionLeftLawBodyContext
  tail : clear implicits.
Arguments coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext
  tail : clear implicits.

Lemma coqRestrictedPADirectOrIntroductionLeft_ready_restricted_in :
    forall tail,
  In coqRestrictedPADirectOrIntroductionLeftDeepRestrictedTemplate
    (coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftAdmissibleContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftCaseContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftDeepEndpointContext.
  do 3 right.
  rewrite <- raw_coqRestrictedPADirectEndpointDeepContext_shape.
  unfold coqRestrictedPADirectOrIntroductionLeftDeepRestrictedTemplate,
    coqRestrictedPADirectAndIntroductionDeepRestrictedTemplate.
  apply raw_coqTemplateNestedExContext_inherited.
  unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  left. reflexivity.
Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_ready_prefix_in : forall tail,
  In coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate
    (coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftAdmissibleContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftCaseContext,
    coqRestrictedPADirectStrongStepOrIntroductionLeftDeepEndpointContext.
  do 3 right.
  rewrite <- raw_coqRestrictedPADirectEndpointDeepContext_shape.
  unfold coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate.
  apply raw_coqTemplateNestedExContext_inherited.
  unfold rawCoqRestrictedPADirectStrongStepEndpointTail.
  right.
  unfold rawCoqRestrictedPADirectStrongStepFourBinderContext.
  apply coqRestrictedPADirectAndIntroduction_contextShiftN_head.
Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_law_body_restricted_in :
    forall tail,
  In coqRestrictedPADirectOrIntroductionLeftDeepRestrictedTemplate
    (coqRestrictedPADirectOrIntroductionLeftLawBodyContext tail).
Proof.
  intro tail. right. right.
  apply coqRestrictedPADirectOrIntroductionLeft_ready_restricted_in.
Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_law_body_admissible_in :
    forall tail,
  In coqRestrictedPADirectOrIntroductionLeftDeepAdmissibleTemplate
    (coqRestrictedPADirectOrIntroductionLeftLawBodyContext tail).
Proof.
  intro tail. right. right. right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_law_body_prefix_in :
    forall tail,
  In coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate
    (coqRestrictedPADirectOrIntroductionLeftLawBodyContext tail).
Proof.
  intro tail. right. right.
  apply coqRestrictedPADirectOrIntroductionLeft_ready_prefix_in.
Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_law_body_case_in : forall tail,
  In coqRestrictedPADirectOrIntroductionLeftCaseTemplate
    (coqRestrictedPADirectOrIntroductionLeftLawBodyContext tail).
Proof.
  intro tail. right. right. right. right. left. reflexivity.
Qed.

(** The two hypotheses of the recursive-child residual are deliberately the
    first two entries of the law-body context.  Naming these positions keeps
    the later implication-introduction proof independent of the much longer
    strong-step tail. *)
Lemma coqRestrictedPADirectOrIntroductionLeft_law_body_context_truth_in :
    forall tail,
  In coqRestrictedPADirectAssumptionWitnessContextTruthTemplate
    (coqRestrictedPADirectOrIntroductionLeftLawBodyContext tail).
Proof. intro tail. left. reflexivity. Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_law_body_endpoint_in :
    forall tail,
  In coqRestrictedPADirectOrIntroductionLeftChildEndpointTemplate
    (coqRestrictedPADirectOrIntroductionLeftLawBodyContext tail).
Proof. intro tail. right. left. reflexivity. Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_eigen_inherited : forall
    tail formula,
  In formula (coqRestrictedPADirectOrIntroductionLeftLawBodyContext tail) ->
  In (templateFormulaRename S formula)
    (coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext tail).
Proof.
  intros tail formula hin. right.
  unfold templateContextShift, templateContextRename.
  apply in_map. exact hin.
Qed.

(** After existential elimination the coverage witness itself is the fresh
    head assumption, while every pre-existing resource has crossed exactly
    one de Bruijn binder.  These small membership lemmas are the syntactic
    contract used by the opened coverage compiler and by the shifted [K(d)]
    application which follows it. *)
Lemma coqRestrictedPADirectOrIntroductionLeft_eigen_coverage_body_in :
    forall tail,
  In coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate
    (coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext tail).
Proof. intro tail. left. reflexivity. Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_eigen_restricted_in :
    forall tail,
  In (templateFormulaRename S
      coqRestrictedPADirectOrIntroductionLeftDeepRestrictedTemplate)
    (coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext tail).
Proof.
  intro tail.
  apply coqRestrictedPADirectOrIntroductionLeft_eigen_inherited.
  apply coqRestrictedPADirectOrIntroductionLeft_law_body_restricted_in.
Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_eigen_admissible_in :
    forall tail,
  In (templateFormulaRename S
      coqRestrictedPADirectOrIntroductionLeftDeepAdmissibleTemplate)
    (coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext tail).
Proof.
  intro tail.
  apply coqRestrictedPADirectOrIntroductionLeft_eigen_inherited.
  apply coqRestrictedPADirectOrIntroductionLeft_law_body_admissible_in.
Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_eigen_prefix_in : forall tail,
  In (templateFormulaRename S
      coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate)
    (coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext tail).
Proof.
  intro tail.
  apply coqRestrictedPADirectOrIntroductionLeft_eigen_inherited.
  apply coqRestrictedPADirectOrIntroductionLeft_law_body_prefix_in.
Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_eigen_case_in : forall tail,
  In (templateFormulaRename S
      coqRestrictedPADirectOrIntroductionLeftCaseTemplate)
    (coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext tail).
Proof.
  intro tail.
  apply coqRestrictedPADirectOrIntroductionLeft_eigen_inherited.
  apply coqRestrictedPADirectOrIntroductionLeft_law_body_case_in.
Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_eigen_context_truth_in :
    forall tail,
  In (templateFormulaRename S
      coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
    (coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext tail).
Proof.
  intro tail.
  apply coqRestrictedPADirectOrIntroductionLeft_eigen_inherited.
  apply
    coqRestrictedPADirectOrIntroductionLeft_law_body_context_truth_in.
Qed.

Lemma coqRestrictedPADirectOrIntroductionLeft_eigen_endpoint_in : forall tail,
  In (templateFormulaRename S
      coqRestrictedPADirectOrIntroductionLeftChildEndpointTemplate)
    (coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext tail).
Proof.
  intro tail.
  apply coqRestrictedPADirectOrIntroductionLeft_eigen_inherited.
  apply coqRestrictedPADirectOrIntroductionLeft_law_body_endpoint_in.
Qed.

(** ------------------------------------------------------------------
    Sharp opened-bound structural compiler boundary. *)

Definition
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawTemplate
    : TemplateFormula :=
  tfImp
    (templateFormulaRename S
      coqRestrictedPADirectOrIntroductionLeftDeepRestrictedCoreTemplate)
    (tfImp
      (templateFormulaRename S
        coqRestrictedPADirectOrIntroductionLeftDeepAtomicTemplate)
      (tfImp
        (templateFormulaRename S
          coqRestrictedPADirectOrIntroductionLeftDeepHasCoverageTemplate)
        (tfImp
          (templateFormulaRename S
            coqRestrictedPADirectOrIntroductionLeftDeepRuleCoverageTemplate)
          (tfImp
            (templateFormulaRename S
              coqRestrictedPADirectOrIntroductionLeftDeepAdmissibleCoreTemplate)
            (tfImp
              coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate
              (tfImp
                (templateFormulaRename S
                  coqRestrictedPADirectOrIntroductionLeftCaseTemplate)
                (templateFormulaRename S
                  coqRestrictedPADirectOrIntroductionLeftChildInterfaceResultTemplate))))))).

Definition
    RawCoqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawTemplate)
      root.

Arguments
  RawCoqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawRoot
  M hPA inputs tail : clear implicits.

(** The first missing component can be audited independently of the bundled
    interface above.  It asks only for carrier-parametric rerooting of the
    dynamic restriction core; unlike [raw_restrictedProof_recursive_child],
    it does not freeze the hierarchy level metatheoretically. *)
Definition
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootLawTemplate
    : TemplateFormula :=
  tfImp
    (templateFormulaRename S
      coqRestrictedPADirectOrIntroductionLeftDeepRestrictedCoreTemplate)
    (tfImp
      (templateFormulaRename S
        coqRestrictedPADirectOrIntroductionLeftCaseTemplate)
      (templateFormulaRename S
        coqRestrictedPADirectOrIntroductionLeftChildRestrictedCoreTemplate)).

Definition
    RawCoqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootLawTemplate)
      root.

Arguments
  RawCoqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootLawRoot
  M hPA inputs tail : clear implicits.

(** ------------------------------------------------------------------
    Close the legacy recursive-child residual from the opened compiler.

    The structural compiler runs under the eigenvariable introduced for the
    common coverage witness.  Every inherited formula is therefore renamed
    once.  The generic renamed child-truth theorem above consumes its output
    together with the shifted strong prefix; represented Ex-E then returns
    the unshifted child truth before the two public law hypotheses are
    discharged by implication introduction. *)
Theorem
    raw_codedPALocalProof_recursiveChildLaw_of_openedCoverageCompiler :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectOrIntroductionLeftRecursiveChildLawRoot
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail (openedRoot & hopened).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (readyContext :=
    coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext tail).
  set (endpointContext :=
    coqRestrictedPADirectOrIntroductionLeftLawEndpointContext tail).
  set (bodyContext :=
    coqRestrictedPADirectOrIntroductionLeftLawBodyContext tail).
  set (eigenContext :=
    coqRestrictedPADirectOrIntroductionLeftCoverageEigenContext tail).
  set (readyCode := rawTemplateContextCode translation readyContext).
  set (endpointCode := rawTemplateContextCode translation endpointContext).
  set (bodyCode := rawTemplateContextCode translation bodyContext).
  set (eigenCode := rawTemplateContextCode translation eigenContext).

  (** First expose the common coverage existential before entering its
      eigenvariable context. *)
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation bodyContext
      coqRestrictedPADirectOrIntroductionLeftDeepAdmissibleTemplate
      (coqRestrictedPADirectOrIntroductionLeft_law_body_admissible_in tail))
    as hadmissibleBody.
  rewrite coqRestrictedPADirectOrIntroductionLeft_deep_admissible_shape
    in hadmissibleBody.
  rewrite rawTemplateFormula_and in hadmissibleBody.
  pose proof
    (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _ hadmissibleBody)
    as hcommonCoverage.
  rewrite coqRestrictedPADirectOrIntroductionLeft_common_coverage_ex_shape
    in hcommonCoverage.
  rewrite rawTemplateFormula_ex in hcommonCoverage.

  (** In the opened context, project the four strengthened restriction
      fields. *)
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        coqRestrictedPADirectOrIntroductionLeftDeepRestrictedTemplate)
      (coqRestrictedPADirectOrIntroductionLeft_eigen_restricted_in tail))
    as hrestrictedEigen.
  rewrite coqRestrictedPADirectOrIntroductionLeft_deep_restricted_shape
    in hrestrictedEigen.
  cbn [templateFormulaRename] in hrestrictedEigen.
  rewrite rawTemplateFormula_and in hrestrictedEigen.
  pose proof
    (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _ hrestrictedEigen)
    as hrestrictedCore.
  pose proof
    (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _ hrestrictedEigen)
    as hrestrictedTail.
  rewrite rawTemplateFormula_and in hrestrictedTail.
  pose proof
    (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _ hrestrictedTail)
    as hatomic.
  pose proof
    (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _ hrestrictedTail)
    as hcoverageTail.
  rewrite rawTemplateFormula_and in hcoverageTail.
  pose proof
    (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _ hcoverageTail)
    as hformulaCoverage.
  pose proof
    (raw_codedPALocalProofOf_andE2 M hPA _ _ _ _ hcoverageTail)
    as hruleCoverage.

  (** The admissibility core is inherited, while the coverage body is the
      fresh head assumption selected by Ex-E. *)
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        coqRestrictedPADirectOrIntroductionLeftDeepAdmissibleTemplate)
      (coqRestrictedPADirectOrIntroductionLeft_eigen_admissible_in tail))
    as hadmissibleEigen.
  rewrite coqRestrictedPADirectOrIntroductionLeft_deep_admissible_shape
    in hadmissibleEigen.
  cbn [templateFormulaRename] in hadmissibleEigen.
  rewrite rawTemplateFormula_and in hadmissibleEigen.
  pose proof
    (raw_codedPALocalProofOf_andE1 M hPA _ _ _ _ hadmissibleEigen)
    as hadmissibleCore.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate
      (coqRestrictedPADirectOrIntroductionLeft_eigen_coverage_body_in tail))
    as hcoverageBody.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        coqRestrictedPADirectOrIntroductionLeftCaseTemplate)
      (coqRestrictedPADirectOrIntroductionLeft_eigen_case_in tail))
    as hcase.

  (** Apply the opened structural operation to its seven literal inputs. *)
  unfold
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawTemplate
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
      hopened2 hformulaCoverage) as hopened3.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _
      hopened3 hruleCoverage) as hopened4.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _
      hopened4 hadmissibleCore) as hopened5.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _
      hopened5 hcoverageBody) as hopened6.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateImpE
      M hPA translation eigenContext _ _ _ _
      hopened6 hcase) as hinterface.

  (** The remaining two inputs to [K(d)] are direct inherited assumptions. *)
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate)
      (coqRestrictedPADirectOrIntroductionLeft_eigen_prefix_in tail))
    as hprefix.
  pose proof
    (raw_codedPALocalProofOf_coqRestrictedPADirect_templateAssumption
      M hPA translation eigenContext
      (templateFormulaRename S
        coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
      (coqRestrictedPADirectOrIntroductionLeft_eigen_context_truth_in tail))
    as hcontextTruth.
  assert (hchildContextTruth : RawCodedPALocalProofOf M eigenCode
    (rawTemplateFormula translation
      (templateFormulaRename S
        (coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
          coqRestrictedPADirectOrIntroductionLeftChildTerm
          coqRestrictedPADirectOrIntroductionLeftWitnessContextTerm
          coqRestrictedPADirectOrIntroductionLeftChildConclusionTerm)))
    (rawTemplateProofCode translation
      (trpAss eigenContext
        (templateFormulaRename S
          coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)))).
  {
    rewrite
      coqRestrictedPADirectOrIntroductionLeft_child_context_truth_agreement.
    exact hcontextTruth.
  }
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectAndIntroductionChildTruth_renamed
      M hPA translation eigenContext S
      coqRestrictedPADirectOrIntroductionLeftChildTerm
      coqRestrictedPADirectOrIntroductionLeftWitnessContextTerm
      coqRestrictedPADirectOrIntroductionLeftChildConclusionTerm
      _ _ _ hinterface hprefix hchildContextTruth)
    as [shiftedTruthRoot hshiftedTruth].
  rewrite coqRestrictedPADirectOrIntroductionLeft_child_truth_agreement
    in hshiftedTruth.

  (** Eliminate common coverage, then discharge context truth and endpoint in
      the exact order of the public recursive-child law. *)
  pose proof
    (raw_codedPALocalProofOf_exE M hPA bodyCode
      (rawTemplateContextCode translation (templateContextShift bodyContext))
      (rawTemplateFormula translation
        coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate)
      (rawTemplateFormula translation
        (templateFormulaRename S
          coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate))
      _ shiftedTruthRoot hcommonCoverage
      (raw_templateContext_shift M hPA translation bodyContext)
      (rawTemplateFormula_shift translation
        coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate)
      hshiftedTruth) as hbodyTruth.
  pose proof
    (raw_codedPALocalProofOf_impI M hPA endpointCode
      (rawTemplateFormula translation
        coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate)
      _ hbodyTruth) as hcontextTruthLaw.
  pose proof
    (raw_codedPALocalProofOf_impI M hPA readyCode
      (rawTemplateFormula translation
        coqRestrictedPADirectOrIntroductionLeftChildEndpointTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectAssumptionWitnessContextTruthTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate))
      _ hcontextTruthLaw) as hrecursiveLaw.
  lazymatch type of hrecursiveLaw with
  | RawCodedPALocalProofOf _ _ _ ?root =>
      exists root;
      change (RawCodedPALocalProofOf M readyCode
        (rawTemplateFormula translation
          coqRestrictedPADirectOrIntroductionLeftRecursiveChildLawTemplate)
        root);
      rewrite rawTemplateFormula_orIntroductionLeftRecursiveChildLaw_view;
      exact hrecursiveLaw
  end.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
