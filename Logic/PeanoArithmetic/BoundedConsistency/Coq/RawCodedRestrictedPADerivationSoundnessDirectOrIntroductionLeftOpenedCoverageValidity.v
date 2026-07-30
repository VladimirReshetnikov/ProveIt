(**
  Raw-model validity of the complete opened Or-I-left coverage law.

  The template law has seven arithmetic premises.  Their semantic content is
  exactly the carrier-valued child-interface theorem: parent restriction and
  proof-wide certificates descend to the displayed child, the common formula
  bound supplies assignment coverage, and child rule coverage upgrades the
  displayed endpoint to rule validity.  This file connects those semantic
  relations to the reified fixed PA source and applies arithmetic
  completeness once.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment
  RawCodedSyntaxConstructors
  RawCodedProofConstructors
  RawCodedProofEndpoints
  RawCodedProofRules
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedRestrictedPAProof
  RawCodedFixedLevelTruthTotality
  RawModelCompleteness
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedTargetTemplateSemantics
  RawCodedCarrierRestrictedProofReroot
  RawCodedOrIntroductionLeftChildInterface
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageSource.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedTargetTemplateSemantics.
Import PABoundedRawCodedCarrierRestrictedProofReroot.
Import PABoundedRawCodedOrIntroductionLeftChildInterface.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageSource.

(** Semantic views of the four child-interface fields. *)
Lemma raw_orIntroductionLeft_child_below_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectOrIntroductionLeftChildBelowTemplate <->
  rawLt M (variables 2) (variables 12).
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPADirectOrIntroductionLeft_child_below_shape.
  rewrite rawTemplateFormulaSat_embedPA.
  rewrite raw_sat_ltTermAt_iff.
  cbn [raw_term_eval].
  repeat rewrite raw_term_eval_liftTerm.
  reflexivity.
Qed.

Lemma raw_orIntroductionLeft_child_restricted_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectOrIntroductionLeftChildRestrictedTemplate <->
  RawCarrierRestrictedProofAt M variables
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      (variables 2) /\
  RawProofAtomicallyAdequate M (variables 2) /\
  RawProofHasFormulaCoverage M (variables 2) /\
  RawProofRuleCoverage M (variables 2).
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPADirectOrIntroductionLeft_child_restricted_shape.
  cbn [rawTemplateFormulaSat].
  rewrite
    coqRestrictedPADirectOrIntroductionLeftChildRestrictedCore_shape.
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

Lemma raw_orIntroductionLeft_child_endpoint_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectOrIntroductionLeftChildPredicateEndpointTemplate <->
  RawProofRuleValid M (variables 2) (variables 7) (variables 6).
Proof.
  intros M variables parameters predicates.
  rewrite
    coqRestrictedPADirectOrIntroductionLeft_child_predicate_endpoint_shape.
  rewrite rawTemplateFormulaSat_embedPA.
  rewrite raw_sat_proofRuleValidTermAt_iff.
  cbn [raw_term_eval]. reflexivity.
Qed.

Lemma raw_orIntroductionLeft_child_admissible_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectOrIntroductionLeftChildAdmissibleTemplate <->
  RawCodedFormulaAtomicallyAdequate M (variables 6) /\
  RawCodedAssignmentDefinedThrough M
    (variables 9) (variables 8) (variables 6) /\
  RawCarrierFormulaQuantifierBounded M
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 6) /\
  exists coverageBound,
    RawProofFormulaCoverage M (variables 2) coverageBound /\
    RawCodedAssignmentDefinedThrough M
      (variables 9) (variables 8) coverageBound.
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPADirectOrIntroductionLeft_child_admissible_shape.
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

Lemma raw_orIntroductionLeft_child_interface_renamed_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    (templateFormulaRename S
      coqRestrictedPADirectOrIntroductionLeftChildInterfaceResultTemplate) <->
  rawLt M (variables 3) (variables 13) /\
  RawCarrierRestrictedProofAt M (fun index => variables (S index))
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      (variables 3) /\
  RawProofAtomicallyAdequate M (variables 3) /\
  RawProofHasFormulaCoverage M (variables 3) /\
  RawProofRuleCoverage M (variables 3) /\
  RawProofRuleValid M (variables 3) (variables 8) (variables 7) /\
  RawCodedFormulaAtomicallyAdequate M (variables 7) /\
  RawCodedAssignmentDefinedThrough M
    (variables 10) (variables 9) (variables 7) /\
  RawCarrierFormulaQuantifierBounded M
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 7) /\
  exists coverageBound,
    RawProofFormulaCoverage M (variables 3) coverageBound /\
    RawCodedAssignmentDefinedThrough M
      (variables 10) (variables 9) coverageBound.
Proof.
  intros M variables parameters predicates.
  rewrite rawTemplateFormulaSat_rename.
  rewrite coqRestrictedPADirectOrIntroductionLeft_child_interface_shape.
  cbn [rawTemplateFormulaSat].
  rewrite raw_orIntroductionLeft_child_below_sat_iff,
    raw_orIntroductionLeft_child_restricted_sat_iff,
    raw_orIntroductionLeft_child_endpoint_sat_iff,
    raw_orIntroductionLeft_child_admissible_sat_iff.
  tauto.
Qed.

(** The seven-premise template law follows directly from the general
    carrier-valued arithmetic interface. *)
Theorem raw_coqRestrictedPADirectOrIntroductionLeftOpenedCoverageLaw_valid :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawTemplate.
Proof.
  intros M hPA variables parameters predicates.
  unfold
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawTemplate.
  cbn [rawTemplateFormulaSat].
  intros hrestricted hatomic _ hruleCoverage _ hcommonCoverage hcase.

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

  rewrite
    coqRestrictedPADirectOrIntroductionLeft_common_coverage_body_shape
    in hcommonCoverage.
  rewrite rawTemplateFormulaSat_embedPA in hcommonCoverage.
  cbn [raw_formula_sat] in hcommonCoverage.
  rewrite raw_sat_proofFormulaCoverageTermAt_iff,
    raw_sat_codedAssignmentDefinedThroughTermAt_iff in hcommonCoverage.
  cbn [raw_term_eval] in hcommonCoverage.
  destruct hcommonCoverage as [hformulaCoverage hassignmentCoverage].

  rewrite rawTemplateFormulaSat_rename in hcase.
  rewrite coqRestrictedPADirectOrIntroductionLeft_case_shape in hcase.
  cbn [rawTemplateFormulaSat] in hcase.
  destruct hcase as [hcode [_ [hendpoint _]]].
  unfold coqRestrictedPADirectOrIntroductionLeftCodeEqualityTemplate
    in hcode.
  rewrite rawTemplateFormulaSat_embedPA in hcode.
  cbn [raw_formula_sat raw_term_eval] in hcode.
  unfold coqRestrictedPADirectOrIntroductionLeftChildEndpointTemplate
    in hendpoint.
  rewrite rawTemplateFormulaSat_embedPA in hendpoint.
  rewrite raw_sat_proofEndpointTermAt_iff in hendpoint.
  cbn [raw_term_eval] in hendpoint.

  destruct (raw_orIntroductionLeft_child_interface M hPA
    (fun index => variables (S (index + 8)))
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 13) (variables 0) (variables 8) (variables 7)
    (variables 6) (variables 3) (variables 10) (variables 9)
    hrestricted hatomic hformulaCoverage hruleCoverage hcode
    hendpoint hassignmentCoverage) as
    [hbelow [hchildRestricted [hchildAtomic
      [hchildFormulaCoverage [hchildRuleCoverage [hchildRuleValid
        [hleftAtomic [hleftDefined hleftBounded]]]]]]]].

  apply (proj2
    (raw_orIntroductionLeft_child_interface_renamed_sat_iff
      M variables parameters predicates)).
  repeat split; try assumption.
  - exists (variables 0). exact hchildFormulaCoverage.
  - exists (variables 0). split; assumption.
Qed.

Theorem
    raw_coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSource_valid :
  forall (M : RawPAModel), RawPASatisfies M -> forall variables,
  raw_formula_sat M variables
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceFormula.
Proof.
  intros M hPA variables.
  unfold coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceFormula.
  cbn [raw_formula_sat]. intro level.
  pose (parameters :=
    (fun _ : TemplateParameterName => raw_zero M)).
  pose (predicates :=
    (fun (_ : TemplatePredicateName) (_ : list M) => True)).
  apply (proj1 (rawTemplateFormulaSat_embedPA M
    (scons M level variables) parameters predicates
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceBodyFormula)).
  rewrite coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSource_embed.
  unfold
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceBodyTemplate.
  apply (proj2 (rawTemplateFormulaSat_abstractParameter M
    variables parameters predicates
    coqRestrictedPASoundnessLowerLevelParameterName level
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawTemplate)).
  apply raw_coqRestrictedPADirectOrIntroductionLeftOpenedCoverageLaw_valid.
  exact hPA.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity.
