(**
  One arithmetic child-interface source for All-E and Ex-I.

  The two quantifier rules have different literal constructor rows, but the
  recursive child occupies the same three endpoint-witness slots in both:

    child = v2, witness context = v7, child conclusion = v5.

  Consequently their inherited four-field child interface is literally the
  same template as the already audited Or-I-right interface.  This module
  reuses that template and its semantic decoding, while proving separately
  that each quantifier constructor row supplies the recursive-child data.

  Keeping this family separate from the same-context propositional unary
  family is deliberate.  It records the quantifier constructors honestly
  and avoids pretending that their rule rows are interchangeable with an
  And-E or Or-I row.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedAssignment
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedProofConstructors
  RawCodedProofDescent
  RawCodedProofEndpoints
  RawCodedProofRules
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedRestrictedPAProof
  RawCodedFixedLevelTruthTotality
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedTemplateEmbeddedUniversalValidity
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateParameterAbstraction
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedTargetTemplateSemantics
  RawCodedCarrierRestrictedProofReroot
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity
  RawCodedProofAllEConstructor
  RawCodedProofExIConstructor
  RawCodedRestrictedPADerivationSoundnessRecursiveChildInterface
  RawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageSource.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessQuantifierUnaryChildInterfaceOpenedCoverageSource.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import PABoundedRawCodedTemplateEmbeddedUniversalValidity.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedTargetTemplateSemantics.
Import PABoundedRawCodedCarrierRestrictedProofReroot.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedProofExIConstructor.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildInterface.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageSource.

(** A two-element metatheoretic index selects the represented constructor
    row.  It disappears in each concrete compiler corollary. *)
Inductive CoqRestrictedPAQuantifierUnaryRule : Type :=
| CoqQuantifierUniversalElimination
| CoqQuantifierExistentialIntroduction.

Definition coqRestrictedPAQuantifierUnaryCaseTemplate
    (rule : CoqRestrictedPAQuantifierUnaryRule) : TemplateFormula :=
  match rule with
  | CoqQuantifierUniversalElimination =>
      coqRestrictedPADirectUniversalEliminationCaseTemplate
  | CoqQuantifierExistentialIntroduction =>
      coqRestrictedPADirectExistentialIntroductionCaseTemplate
  end.

Definition coqRestrictedPAQuantifierUnaryChildTerm : TemplateTerm := ttVar 2.

Definition coqRestrictedPAQuantifierUnaryWitnessContextTerm
    : TemplateTerm := ttVar 7.

Definition coqRestrictedPAQuantifierUnaryChildConclusionTerm
    : TemplateTerm := ttVar 5.

Definition coqRestrictedPAQuantifierUnaryChildInterfaceTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    coqRestrictedPAQuantifierUnaryChildTerm
    coqRestrictedPAQuantifierUnaryWitnessContextTerm
    coqRestrictedPAQuantifierUnaryChildConclusionTerm.

(** This equality is the key sharing boundary: all existing semantic
    decoding lemmas for the Or-I-right child interface apply without any
    propositional approximation or code transport. *)
Lemma coqRestrictedPAQuantifierUnary_child_interface_agreement :
  coqRestrictedPAQuantifierUnaryChildInterfaceTemplate =
  coqRestrictedPASameContextOrIntroductionRightChildInterfaceTemplate.
Proof. reflexivity. Qed.

Definition coqRestrictedPAQuantifierUnaryOpenedCoverageLawTemplate
    (rule : CoqRestrictedPAQuantifierUnaryRule) : TemplateFormula :=
  tfImp coqRestrictedPADirectAndIntroductionOpenedRestrictedTemplate
    (tfImp coqRestrictedPADirectAndIntroductionOpenedAtomicTemplate
      (tfImp
        coqRestrictedPADirectAndIntroductionOpenedFormulaCoverageTemplate
        (tfImp
          coqRestrictedPADirectAndIntroductionOpenedRuleCoverageTemplate
          (tfImp
            coqRestrictedPADirectAndIntroductionOpenedAdmissibleCoreTemplate
            (tfImp
              coqRestrictedPADirectAndIntroductionOpenedCommonCoverageTemplate
              (tfImp
                (templateFormulaRename S
                  (coqRestrictedPAQuantifierUnaryCaseTemplate rule))
                (templateFormulaRename S
                  coqRestrictedPAQuantifierUnaryChildInterfaceTemplate))))))).

(** ------------------------------------------------------------------
    Semantic recursive-child data for the two genuine constructor rows. *)

Theorem raw_universalElimination_child_interface : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail level root coverageBound context body replacement child
      childConclusion assignmentCode assignmentStep,
  RawCarrierRestrictedProofAt M tail level root ->
  RawProofAtomicallyAdequate M root ->
  RawProofFormulaCoverage M root coverageBound ->
  RawProofRuleCoverage M root ->
  root = rawProofAllERoot M context body replacement child ->
  RawProofEndpoint M child context childConclusion ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep coverageBound ->
  rawLt M child root /\
  RawCarrierRestrictedProofAt M tail level child /\
  RawProofAtomicallyAdequate M child /\
  RawProofFormulaCoverage M child coverageBound /\
  RawProofRuleCoverage M child /\
  RawProofRuleValid M child context childConclusion /\
  RawCodedFormulaAtomicallyAdequate M childConclusion /\
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep childConclusion /\
  RawCarrierFormulaQuantifierBounded M level childConclusion.
Proof.
  intros M hPA tail level root coverageBound context body replacement child
    childConclusion assignmentCode assignmentStep
    hrestricted hatomic hformulaCoverage hruleCoverage hcode hendpoint
    hassignmentCoverage.
  exact
    (raw_recursive_constructor_child_interface
      M hPA tail level root coverageBound context
      body (raw_zero M) (raw_zero M) replacement
      child (raw_zero M) (raw_zero M)
      [rawNumeralValue M 12; context; body; replacement; child]
      [child] child childConclusion assignmentCode assignmentStep
      hrestricted hatomic hformulaCoverage hruleCoverage
      (ltac:(
        unfold RawProofConstructorCode;
        rewrite hcode;
        do 12 right; left; reflexivity))
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      (ltac:(unfold rawProofAllERoot in hcode; exact hcode))
      (ltac:(left; reflexivity)) hendpoint hassignmentCoverage).
Qed.

Theorem raw_existentialIntroduction_child_interface : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      tail level root coverageBound context body replacement child
      childConclusion assignmentCode assignmentStep,
  RawCarrierRestrictedProofAt M tail level root ->
  RawProofAtomicallyAdequate M root ->
  RawProofFormulaCoverage M root coverageBound ->
  RawProofRuleCoverage M root ->
  root = rawProofExIRoot M context body replacement child ->
  RawProofEndpoint M child context childConclusion ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep coverageBound ->
  rawLt M child root /\
  RawCarrierRestrictedProofAt M tail level child /\
  RawProofAtomicallyAdequate M child /\
  RawProofFormulaCoverage M child coverageBound /\
  RawProofRuleCoverage M child /\
  RawProofRuleValid M child context childConclusion /\
  RawCodedFormulaAtomicallyAdequate M childConclusion /\
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep childConclusion /\
  RawCarrierFormulaQuantifierBounded M level childConclusion.
Proof.
  intros M hPA tail level root coverageBound context body replacement child
    childConclusion assignmentCode assignmentStep
    hrestricted hatomic hformulaCoverage hruleCoverage hcode hendpoint
    hassignmentCoverage.
  exact
    (raw_recursive_constructor_child_interface
      M hPA tail level root coverageBound context
      body (raw_zero M) (raw_zero M) replacement
      child (raw_zero M) (raw_zero M)
      [rawNumeralValue M 13; context; body; replacement; child]
      [child] child childConclusion assignmentCode assignmentStep
      hrestricted hatomic hformulaCoverage hruleCoverage
      (ltac:(
        unfold RawProofConstructorCode;
        rewrite hcode;
        do 13 right; left; reflexivity))
      (ltac:(unfold rawProofRecursiveCases; cbn; tauto))
      (ltac:(unfold rawProofExIRoot in hcode; exact hcode))
      (ltac:(left; reflexivity)) hendpoint hassignmentCoverage).
Qed.

(** ------------------------------------------------------------------
    Model validity of the common opened-coverage implication. *)

Theorem raw_quantifierUnary_openedCoverageLaw_valid : forall
    (rule : CoqRestrictedPAQuantifierUnaryRule)
    (M : RawPAModel), RawPASatisfies M ->
  forall variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    (coqRestrictedPAQuantifierUnaryOpenedCoverageLawTemplate rule).
Proof.
  intros rule M hPA variables parameters predicates.
  destruct rule;
    unfold coqRestrictedPAQuantifierUnaryOpenedCoverageLawTemplate;
    cbn [coqRestrictedPAQuantifierUnaryCaseTemplate
      rawTemplateFormulaSat];
    intros hrestricted hatomic _ hruleCoverage _ hcommonCoverage hcase.
  - pose proof (raw_sameContextUnary_opened_parent_facts M variables
      parameters predicates hrestricted hatomic hruleCoverage
      hcommonCoverage) as hparent.
    destruct hparent as
      [hparentRestricted hparentAtomic hparentRuleCoverage
        hparentFormulaCoverage hassignmentCoverage].
    rewrite rawTemplateFormulaSat_rename in hcase.
    rewrite coqRestrictedPADirectUniversalElimination_case_shape in hcase.
    cbn [rawTemplateFormulaSat] in hcase.
    destruct hcase as [hcode [_ [_ [hendpoint _]]]].
    unfold coqRestrictedPADirectUniversalEliminationCodeEqualityTemplate
      in hcode.
    rewrite rawTemplateFormulaSat_embedPA in hcode.
    cbn [raw_formula_sat raw_term_eval] in hcode.
    change (variables 13 = rawProofAllERoot M
      (variables 8) (variables 7) (variables 4) (variables 3)) in hcode.
    unfold coqRestrictedPADirectUniversalEliminationChildEndpointTemplate
      in hendpoint.
    rewrite rawTemplateFormulaSat_embedPA,
      raw_sat_proofEndpointTermAt_iff in hendpoint.
    cbn [raw_term_eval] in hendpoint.
    destruct (raw_universalElimination_child_interface M hPA
      (fun index => variables (S (index + 8)))
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      (variables 13) (variables 0) (variables 8) (variables 7)
      (variables 4) (variables 3) (variables 6)
      (variables 10) (variables 9)
      hparentRestricted hparentAtomic hparentFormulaCoverage
      hparentRuleCoverage hcode hendpoint hassignmentCoverage) as
      [hbelow [hchildRestricted [hchildAtomic
        [hchildFormulaCoverage [hchildRuleCoverage [hchildRuleValid
          [hformulaAtomic [hformulaDefined hformulaBounded]]]]]]]].
    rewrite coqRestrictedPAQuantifierUnary_child_interface_agreement.
    apply (proj2
      (raw_sameContextOrIntroductionRight_child_interface_renamed_sat_iff
        M variables parameters predicates)).
    repeat split; try assumption.
    + exists (variables 0). exact hchildFormulaCoverage.
    + exists (variables 0). split; assumption.
  - pose proof (raw_sameContextUnary_opened_parent_facts M variables
      parameters predicates hrestricted hatomic hruleCoverage
      hcommonCoverage) as hparent.
    destruct hparent as
      [hparentRestricted hparentAtomic hparentRuleCoverage
        hparentFormulaCoverage hassignmentCoverage].
    rewrite rawTemplateFormulaSat_rename in hcase.
    rewrite coqRestrictedPADirectExistentialIntroduction_case_shape in hcase.
    cbn [rawTemplateFormulaSat] in hcase.
    destruct hcase as [hcode [_ [_ [hendpoint _]]]].
    unfold coqRestrictedPADirectExistentialIntroductionCodeEqualityTemplate
      in hcode.
    rewrite rawTemplateFormulaSat_embedPA in hcode.
    cbn [raw_formula_sat raw_term_eval] in hcode.
    change (variables 13 = rawProofExIRoot M
      (variables 8) (variables 7) (variables 4) (variables 3)) in hcode.
    unfold coqRestrictedPADirectExistentialIntroductionChildEndpointTemplate
      in hendpoint.
    rewrite rawTemplateFormulaSat_embedPA,
      raw_sat_proofEndpointTermAt_iff in hendpoint.
    cbn [raw_term_eval] in hendpoint.
    destruct (raw_existentialIntroduction_child_interface M hPA
      (fun index => variables (S (index + 8)))
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      (variables 13) (variables 0) (variables 8) (variables 7)
      (variables 4) (variables 3) (variables 6)
      (variables 10) (variables 9)
      hparentRestricted hparentAtomic hparentFormulaCoverage
      hparentRuleCoverage hcode hendpoint hassignmentCoverage) as
      [hbelow [hchildRestricted [hchildAtomic
        [hchildFormulaCoverage [hchildRuleCoverage [hchildRuleValid
          [hformulaAtomic [hformulaDefined hformulaBounded]]]]]]]].
    rewrite coqRestrictedPAQuantifierUnary_child_interface_agreement.
    apply (proj2
      (raw_sameContextOrIntroductionRight_child_interface_renamed_sat_iff
        M variables parameters predicates)).
    repeat split; try assumption.
    + exists (variables 0). exact hchildFormulaCoverage.
    + exists (variables 0). split; assumption.
Qed.

(** ------------------------------------------------------------------
    Reification and PA completeness for the shared arithmetic source. *)

Definition coqRestrictedPAQuantifierUnaryOpenedCoverageSourceBodyTemplate
    (rule : CoqRestrictedPAQuantifierUnaryRule) : TemplateFormula :=
  templateFormulaAbstractParameter
    coqRestrictedPASoundnessLowerLevelParameterName
    (coqRestrictedPAQuantifierUnaryOpenedCoverageLawTemplate rule).

Definition coqRestrictedPAQuantifierUnaryOpenedCoverageSourceBodyFormula
    (rule : CoqRestrictedPAQuantifierUnaryRule) : formula :=
  match templateFormulaAsPAFormula
    (coqRestrictedPAQuantifierUnaryOpenedCoverageSourceBodyTemplate rule)
  with
  | Some output => output
  | None => pBot
  end.

Definition coqRestrictedPAQuantifierUnaryOpenedCoverageSourceFormula
    (rule : CoqRestrictedPAQuantifierUnaryRule) : formula :=
  pAll (coqRestrictedPAQuantifierUnaryOpenedCoverageSourceBodyFormula rule).

Lemma coqRestrictedPAQuantifierUnaryOpenedCoverageSource_reifies :
  forall rule,
  templateFormulaAsPAFormula
    (coqRestrictedPAQuantifierUnaryOpenedCoverageSourceBodyTemplate rule) =
  Some
    (coqRestrictedPAQuantifierUnaryOpenedCoverageSourceBodyFormula rule).
Proof. intro rule. destruct rule; vm_compute; reflexivity. Qed.

Theorem coqRestrictedPAQuantifierUnaryOpenedCoverageSource_embed :
  forall rule,
  embedPAFormula
    (coqRestrictedPAQuantifierUnaryOpenedCoverageSourceBodyFormula rule) =
  coqRestrictedPAQuantifierUnaryOpenedCoverageSourceBodyTemplate rule.
Proof.
  intro rule. apply templateFormulaAsPAFormula_sound.
  apply coqRestrictedPAQuantifierUnaryOpenedCoverageSource_reifies.
Qed.

Theorem coqRestrictedPAQuantifierUnaryOpenedCoverageSource_open :
  forall rule,
  templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
    (embedPAFormula
      (coqRestrictedPAQuantifierUnaryOpenedCoverageSourceBodyFormula rule)) =
  coqRestrictedPAQuantifierUnaryOpenedCoverageLawTemplate rule.
Proof.
  intro rule.
  rewrite coqRestrictedPAQuantifierUnaryOpenedCoverageSource_embed.
  apply templateFormulaAbstractParameter_open.
Qed.

Theorem raw_quantifierUnary_openedCoverageSource_valid : forall
    rule (M : RawPAModel), RawPASatisfies M -> forall variables,
  raw_formula_sat M variables
    (coqRestrictedPAQuantifierUnaryOpenedCoverageSourceFormula rule).
Proof.
  intros rule M hPA variables.
  unfold coqRestrictedPAQuantifierUnaryOpenedCoverageSourceFormula.
  apply (raw_formula_sat_all_of_embedded_template_validity M
    (coqRestrictedPAQuantifierUnaryOpenedCoverageSourceBodyFormula rule)
    (fun _ : TemplateParameterName => raw_zero M)
    (fun (_ : TemplatePredicateName) (_ : list M) => True)).
  intros inner level.
  rewrite coqRestrictedPAQuantifierUnaryOpenedCoverageSource_embed.
  unfold coqRestrictedPAQuantifierUnaryOpenedCoverageSourceBodyTemplate.
  apply (proj2 (rawTemplateFormulaSat_abstractParameter M
    inner
    (fun _ : TemplateParameterName => raw_zero M)
    (fun (_ : TemplatePredicateName) (_ : list M) => True)
    coqRestrictedPASoundnessLowerLevelParameterName level
    (coqRestrictedPAQuantifierUnaryOpenedCoverageLawTemplate rule))).
  apply raw_quantifierUnary_openedCoverageLaw_valid. exact hPA.
Qed.

Theorem PA_proves_coqRestrictedPAQuantifierUnaryOpenedCoverageSource :
  forall rule,
  Formula.BProv Formula.Ax_s []
    (coqRestrictedPAQuantifierUnaryOpenedCoverageSourceFormula rule).
Proof.
  intro rule.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA
        (coqRestrictedPAQuantifierUnaryOpenedCoverageSourceFormula rule))).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA variables.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact (raw_quantifierUnary_openedCoverageSource_valid
        rule M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename Formula.Ax_s []
    (coqRestrictedPAQuantifierUnaryOpenedCoverageSourceFormula rule)
    (fun index => index) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

Lemma rawDirect_quantifierUnaryOpenedCoverageSourceBody_agreement : forall
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) rule,
  rawDirectTemplateFormula inputs
    (embedPAFormula
      (coqRestrictedPAQuantifierUnaryOpenedCoverageSourceBodyFormula rule)) =
  rawQuotedFormulaCode M
    (coqRestrictedPAQuantifierUnaryOpenedCoverageSourceBodyFormula rule).
Proof.
  intros M inputs rule. unfold rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

Theorem rawDirect_quantifierUnaryOpenedCoverageSource_substitution : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (inputs : RawCodedTemplateDirectStructuralInputs M) rule,
  RawCodedFormulaSingleSubstitution M
    (rawDirectTemplateTerm inputs coqRestrictedPASoundnessLowerLevelTerm)
    (rawQuotedFormulaCode M
      (coqRestrictedPAQuantifierUnaryOpenedCoverageSourceBodyFormula rule))
    (rawDirectTemplateFormula inputs
      (coqRestrictedPAQuantifierUnaryOpenedCoverageLawTemplate rule)).
Proof.
  intros M hPA inputs rule.
  pose proof (rawDirectTemplateFormula_open M hPA inputs
    (embedPAFormula
      (coqRestrictedPAQuantifierUnaryOpenedCoverageSourceBodyFormula rule))
    coqRestrictedPASoundnessLowerLevelTerm) as hopen.
  rewrite rawDirect_quantifierUnaryOpenedCoverageSourceBody_agreement
    in hopen.
  rewrite coqRestrictedPAQuantifierUnaryOpenedCoverageSource_open in hopen.
  exact hopen.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessQuantifierUnaryChildInterfaceOpenedCoverageSource.
