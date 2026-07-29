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
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedProofDescent
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedRestrictedPAProof
  RawCodedRestrictedProofAdmissibility
  RawCodedPALocalProofExistential
  RawCodedPALocalProofAndIntroduction
  RawCodedPALocalProofPropositionalRules
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
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
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedProofAdmissibility.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
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

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
