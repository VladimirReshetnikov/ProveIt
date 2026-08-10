(**
  One arithmetic source family for every same-context unary child.

  And-E-left, And-E-right, Or-I-left, and Or-I-right differ only in their
  literal constructor row and in the formula displayed at the sole child.
  The proof-wide descent argument is otherwise identical.  This module
  records that fact before quotation: one finite index selects the literal
  case and child conclusion, while a single opened-coverage law constructor,
  semantic argument, parameter abstraction, and completeness proof serve all
  four rules.

  Keeping Or-I-left in the family is intentional.  It shows that the source
  is not an adapter tailored to the three residual fields: it genuinely
  generalizes the independently completed Or-I-left arithmetic source.
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
  RawCodedProofAndEConstructors
  RawCodedProofOrIConstructors
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
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildCompilation.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageSource.

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
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedProofOrIConstructors.
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
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
Import PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildCompilation.

(** A finite metatheoretic index is preferable to four nearly identical PA
    source files.  It disappears when a concrete corollary is selected. *)
Inductive CoqRestrictedPASameContextUnaryRule : Type :=
| CoqSameContextAndEliminationLeft
| CoqSameContextAndEliminationRight
| CoqSameContextOrIntroductionLeft
| CoqSameContextOrIntroductionRight.

Definition coqRestrictedPASameContextUnaryCaseTemplate
    (rule : CoqRestrictedPASameContextUnaryRule) : TemplateFormula :=
  match rule with
  | CoqSameContextAndEliminationLeft =>
      coqRestrictedPADirectAndEliminationLeftCaseTemplate
  | CoqSameContextAndEliminationRight =>
      coqRestrictedPADirectAndEliminationRightCaseTemplate
  | CoqSameContextOrIntroductionLeft =>
      coqRestrictedPADirectOrIntroductionLeftCaseTemplate
  | CoqSameContextOrIntroductionRight =>
      coqRestrictedPADirectOrIntroductionRightCaseTemplate
  end.

Definition coqRestrictedPASameContextUnaryChildTerm
    (_ : CoqRestrictedPASameContextUnaryRule) : TemplateTerm := ttVar 2.

Definition coqRestrictedPASameContextUnaryWitnessContextTerm
    (_ : CoqRestrictedPASameContextUnaryRule) : TemplateTerm := ttVar 7.

Definition coqRestrictedPASameContextUnaryChildConclusionTerm
    (rule : CoqRestrictedPASameContextUnaryRule) : TemplateTerm :=
  match rule with
  | CoqSameContextAndEliminationLeft
  | CoqSameContextAndEliminationRight => ttVar 4
  | CoqSameContextOrIntroductionLeft => ttVar 6
  | CoqSameContextOrIntroductionRight => ttVar 5
  end.

Definition coqRestrictedPASameContextUnaryChildInterfaceTemplate
    (rule : CoqRestrictedPASameContextUnaryRule) : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    (coqRestrictedPASameContextUnaryChildTerm rule)
    (coqRestrictedPASameContextUnaryWitnessContextTerm rule)
    (coqRestrictedPASameContextUnaryChildConclusionTerm rule).

(** All seven antecedents are common.  The fresh variable at index zero is
    the common formula-coverage witness; inherited rule variables are hence
    renamed once. *)
Definition coqRestrictedPASameContextUnaryOpenedCoverageLawTemplate
    (rule : CoqRestrictedPASameContextUnaryRule) : TemplateFormula :=
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
                  (coqRestrictedPASameContextUnaryCaseTemplate rule))
                (templateFormulaRename S
                  (coqRestrictedPASameContextUnaryChildInterfaceTemplate
                    rule)))))))).

(** ------------------------------------------------------------------
    Rule-independent decoding of the parent certificates. *)

Record RawCoqRestrictedPASameContextUnaryOpenedParentFacts
    (M : RawPAModel) (variables : nat -> M)
    (parameters : TemplateParameterName -> M) : Prop := {
  rawCoqSameContextUnaryOpened_parentRestricted :
    RawCarrierRestrictedProofAt M
      (fun index => variables (S (index + 8)))
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      (variables 13);
  rawCoqSameContextUnaryOpened_parentAtomic :
    RawProofAtomicallyAdequate M (variables 13);
  rawCoqSameContextUnaryOpened_parentRuleCoverage :
    RawProofRuleCoverage M (variables 13);
  rawCoqSameContextUnaryOpened_parentFormulaCoverage :
    RawProofFormulaCoverage M (variables 13) (variables 0);
  rawCoqSameContextUnaryOpened_assignmentCoverage :
    RawCodedAssignmentDefinedThrough M
      (variables 10) (variables 9) (variables 0)
}.

Arguments RawCoqRestrictedPASameContextUnaryOpenedParentFacts
  M variables parameters : clear implicits.

Lemma raw_sameContextUnary_opened_parent_facts : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectAndIntroductionOpenedRestrictedTemplate ->
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectAndIntroductionOpenedAtomicTemplate ->
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectAndIntroductionOpenedRuleCoverageTemplate ->
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectAndIntroductionOpenedCommonCoverageTemplate ->
  RawCoqRestrictedPASameContextUnaryOpenedParentFacts
    M variables parameters.
Proof.
  intros M variables parameters predicates
    hrestricted hatomic hruleCoverage hcommonCoverage.

  unfold coqRestrictedPADirectAndIntroductionOpenedRestrictedTemplate
    in hrestricted.
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

  unfold coqRestrictedPADirectAndIntroductionOpenedAtomicTemplate in hatomic.
  rewrite rawTemplateFormulaSat_rename in hatomic.
  unfold coqRestrictedPADirectOrIntroductionLeftDeepAtomicTemplate in hatomic.
  rewrite rawTemplateFormulaSat_rawCoqTemplateRenameN in hatomic.
  rewrite rawTemplateFormulaSat_embedPA in hatomic.
  rewrite raw_sat_proofAtomicallyAdequateTermAt_iff in hatomic.
  cbn [raw_term_eval] in hatomic.

  unfold coqRestrictedPADirectAndIntroductionOpenedRuleCoverageTemplate
    in hruleCoverage.
  rewrite rawTemplateFormulaSat_rename in hruleCoverage.
  unfold coqRestrictedPADirectOrIntroductionLeftDeepRuleCoverageTemplate
    in hruleCoverage.
  rewrite rawTemplateFormulaSat_rawCoqTemplateRenameN in hruleCoverage.
  rewrite rawTemplateFormulaSat_embedPA in hruleCoverage.
  rewrite raw_sat_proofRuleCoverageTermAt_iff in hruleCoverage.
  cbn [raw_term_eval] in hruleCoverage.

  unfold coqRestrictedPADirectAndIntroductionOpenedCommonCoverageTemplate
    in hcommonCoverage.
  rewrite
    coqRestrictedPADirectOrIntroductionLeft_common_coverage_body_shape
    in hcommonCoverage.
  rewrite rawTemplateFormulaSat_embedPA in hcommonCoverage.
  cbn [raw_formula_sat] in hcommonCoverage.
  rewrite raw_sat_proofFormulaCoverageTermAt_iff,
    raw_sat_codedAssignmentDefinedThroughTermAt_iff in hcommonCoverage.
  cbn [raw_term_eval] in hcommonCoverage.
  destruct hcommonCoverage as [hformulaCoverage hassignmentCoverage].
  constructor; assumption.
Qed.

(** ------------------------------------------------------------------
    Semantic views of the two child layouts. *)

Definition coqRestrictedPASameContextAndEliminationChildInterfaceTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    (ttVar 2) (ttVar 7) (ttVar 4).

Definition coqRestrictedPASameContextOrIntroductionRightChildInterfaceTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    (ttVar 2) (ttVar 7) (ttVar 5).

Definition coqRestrictedPASameContextAndEliminationChildRestrictedTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildRestrictedTemplate
    (ttVar 2) (ttVar 7) (ttVar 4).

Definition coqRestrictedPASameContextAndEliminationChildEndpointTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildEndpointTemplate
    (ttVar 2) (ttVar 7) (ttVar 4).

Definition coqRestrictedPASameContextAndEliminationChildAdmissibleTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildAdmissibleTemplate
    (ttVar 2) (ttVar 7) (ttVar 4).

Definition coqRestrictedPASameContextOrIntroductionRightChildRestrictedTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildRestrictedTemplate
    (ttVar 2) (ttVar 7) (ttVar 5).

Definition coqRestrictedPASameContextOrIntroductionRightChildEndpointTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildEndpointTemplate
    (ttVar 2) (ttVar 7) (ttVar 5).

Definition coqRestrictedPASameContextOrIntroductionRightChildAdmissibleTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildAdmissibleTemplate
    (ttVar 2) (ttVar 7) (ttVar 5).

Lemma coqRestrictedPASameContextAndElimination_child_interface_shape :
  coqRestrictedPASameContextAndEliminationChildInterfaceTemplate =
  tfAnd
    (coqRestrictedPADirectAndIntroductionChildBelowTemplate (ttVar 2))
    (tfAnd
      coqRestrictedPASameContextAndEliminationChildRestrictedTemplate
      (tfAnd
        coqRestrictedPASameContextAndEliminationChildEndpointTemplate
        coqRestrictedPASameContextAndEliminationChildAdmissibleTemplate)).
Proof. reflexivity. Qed.

Lemma coqRestrictedPASameContextOrIntroductionRight_child_interface_shape :
  coqRestrictedPASameContextOrIntroductionRightChildInterfaceTemplate =
  tfAnd
    (coqRestrictedPADirectAndIntroductionChildBelowTemplate (ttVar 2))
    (tfAnd
      coqRestrictedPASameContextOrIntroductionRightChildRestrictedTemplate
      (tfAnd
        coqRestrictedPASameContextOrIntroductionRightChildEndpointTemplate
        coqRestrictedPASameContextOrIntroductionRightChildAdmissibleTemplate)).
Proof. reflexivity. Qed.

(** The strong-prefix selectors reduce to the same ordinary arithmetic
    predicates for both layouts.  These computation lemmas are deliberately
    kept local to the source boundary. *)
Lemma coqRestrictedPASameContext_child_below_shape :
  coqRestrictedPADirectAndIntroductionChildBelowTemplate (ttVar 2) =
  embedPAFormula (Formula.ltTermAt (tVar 2) (liftTerm 8 (tVar 4))).
Proof. reflexivity. Qed.

Lemma coqRestrictedPASameContextAndElimination_child_restricted_shape :
  coqRestrictedPASameContextAndEliminationChildRestrictedTemplate =
  tfAnd
    (restrictedTargetTemplateFormulaContext
      coqRestrictedPASoundnessLowerLevelTerm
      (restrictedTargetProofContext (tVar 2)))
    (tfAnd (embedPAFormula (proofAtomicallyAdequateTermAt (tVar 2)))
      (tfAnd (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 2)))
        (embedPAFormula (proofRuleCoverageTermAt (tVar 2))))).
Proof. reflexivity. Qed.

Lemma coqRestrictedPASameContextAndElimination_child_endpoint_shape :
  coqRestrictedPASameContextAndEliminationChildEndpointTemplate =
  embedPAFormula (proofRuleValidTermAt (tVar 2) (tVar 7) (tVar 4)).
Proof. reflexivity. Qed.

Lemma coqRestrictedPASameContextAndElimination_child_admissible_shape :
  coqRestrictedPASameContextAndEliminationChildAdmissibleTemplate =
  tfAnd
    (tfAnd (embedPAFormula
      (codedFormulaAtomicallyAdequateTermAt (tVar 4)))
      (tfAnd (embedPAFormula
        (codedAssignmentDefinedThroughTermAt (tVar 9) (tVar 8) (tVar 4)))
        (restrictedTargetTemplateFormulaContext
          coqRestrictedPASoundnessLowerLevelTerm
          (restrictedTargetFormulaQuantifierBoundedContext (tVar 4)))))
    (embedPAFormula (pEx (pAnd
      (proofFormulaCoverageTermAt (tVar 3) (tVar 0))
      (codedAssignmentDefinedThroughTermAt (tVar 10) (tVar 9) (tVar 0))))).
Proof. reflexivity. Qed.

Lemma coqRestrictedPASameContextOrIntroductionRight_child_restricted_shape :
  coqRestrictedPASameContextOrIntroductionRightChildRestrictedTemplate =
  tfAnd
    (restrictedTargetTemplateFormulaContext
      coqRestrictedPASoundnessLowerLevelTerm
      (restrictedTargetProofContext (tVar 2)))
    (tfAnd (embedPAFormula (proofAtomicallyAdequateTermAt (tVar 2)))
      (tfAnd (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 2)))
        (embedPAFormula (proofRuleCoverageTermAt (tVar 2))))).
Proof. reflexivity. Qed.

Lemma coqRestrictedPASameContextOrIntroductionRight_child_endpoint_shape :
  coqRestrictedPASameContextOrIntroductionRightChildEndpointTemplate =
  embedPAFormula (proofRuleValidTermAt (tVar 2) (tVar 7) (tVar 5)).
Proof. reflexivity. Qed.

Lemma coqRestrictedPASameContextOrIntroductionRight_child_admissible_shape :
  coqRestrictedPASameContextOrIntroductionRightChildAdmissibleTemplate =
  tfAnd
    (tfAnd (embedPAFormula
      (codedFormulaAtomicallyAdequateTermAt (tVar 5)))
      (tfAnd (embedPAFormula
        (codedAssignmentDefinedThroughTermAt (tVar 9) (tVar 8) (tVar 5)))
        (restrictedTargetTemplateFormulaContext
          coqRestrictedPASoundnessLowerLevelTerm
          (restrictedTargetFormulaQuantifierBoundedContext (tVar 5)))))
    (embedPAFormula (pEx (pAnd
      (proofFormulaCoverageTermAt (tVar 3) (tVar 0))
      (codedAssignmentDefinedThroughTermAt (tVar 10) (tVar 9) (tVar 0))))).
Proof. reflexivity. Qed.

Lemma raw_sameContextUnary_child_below_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    (coqRestrictedPADirectAndIntroductionChildBelowTemplate (ttVar 2)) <->
  rawLt M (variables 2) (variables 12).
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPASameContext_child_below_shape.
  rewrite rawTemplateFormulaSat_embedPA, raw_sat_ltTermAt_iff.
  cbn [raw_term_eval].
  repeat rewrite raw_term_eval_liftTerm.
  reflexivity.
Qed.

Lemma raw_sameContextAndElimination_child_restricted_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPASameContextAndEliminationChildRestrictedTemplate <->
  RawCarrierRestrictedProofAt M variables
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      (variables 2) /\
  RawProofAtomicallyAdequate M (variables 2) /\
  RawProofHasFormulaCoverage M (variables 2) /\
  RawProofRuleCoverage M (variables 2).
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPASameContextAndElimination_child_restricted_shape.
  cbn [rawTemplateFormulaSat].
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

Lemma raw_sameContextAndElimination_child_endpoint_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPASameContextAndEliminationChildEndpointTemplate <->
  RawProofRuleValid M (variables 2) (variables 7) (variables 4).
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPASameContextAndElimination_child_endpoint_shape.
  rewrite rawTemplateFormulaSat_embedPA,
    raw_sat_proofRuleValidTermAt_iff.
  cbn [raw_term_eval]. reflexivity.
Qed.

Lemma raw_sameContextAndElimination_child_admissible_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPASameContextAndEliminationChildAdmissibleTemplate <->
  RawCodedFormulaAtomicallyAdequate M (variables 4) /\
  RawCodedAssignmentDefinedThrough M
    (variables 9) (variables 8) (variables 4) /\
  RawCarrierFormulaQuantifierBounded M
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 4) /\
  exists coverageBound,
    RawProofFormulaCoverage M (variables 2) coverageBound /\
    RawCodedAssignmentDefinedThrough M
      (variables 9) (variables 8) coverageBound.
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPASameContextAndElimination_child_admissible_shape.
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

Lemma raw_sameContextAndElimination_child_interface_renamed_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    (templateFormulaRename S
      coqRestrictedPASameContextAndEliminationChildInterfaceTemplate) <->
  rawLt M (variables 3) (variables 13) /\
  RawCarrierRestrictedProofAt M (fun index => variables (S index))
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 3) /\
  RawProofAtomicallyAdequate M (variables 3) /\
  RawProofHasFormulaCoverage M (variables 3) /\
  RawProofRuleCoverage M (variables 3) /\
  RawProofRuleValid M (variables 3) (variables 8) (variables 5) /\
  RawCodedFormulaAtomicallyAdequate M (variables 5) /\
  RawCodedAssignmentDefinedThrough M
    (variables 10) (variables 9) (variables 5) /\
  RawCarrierFormulaQuantifierBounded M
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 5) /\
  exists coverageBound,
    RawProofFormulaCoverage M (variables 3) coverageBound /\
    RawCodedAssignmentDefinedThrough M
      (variables 10) (variables 9) coverageBound.
Proof.
  intros M variables parameters predicates.
  rewrite rawTemplateFormulaSat_rename.
  rewrite coqRestrictedPASameContextAndElimination_child_interface_shape.
  cbn [rawTemplateFormulaSat].
  rewrite raw_sameContextUnary_child_below_sat_iff,
    raw_sameContextAndElimination_child_restricted_sat_iff,
    raw_sameContextAndElimination_child_endpoint_sat_iff,
    raw_sameContextAndElimination_child_admissible_sat_iff.
  cbn. tauto.
Qed.

Lemma raw_sameContextOrIntroductionRight_child_restricted_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPASameContextOrIntroductionRightChildRestrictedTemplate <->
  RawCarrierRestrictedProofAt M variables
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      (variables 2) /\
  RawProofAtomicallyAdequate M (variables 2) /\
  RawProofHasFormulaCoverage M (variables 2) /\
  RawProofRuleCoverage M (variables 2).
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPASameContextOrIntroductionRight_child_restricted_shape.
  cbn [rawTemplateFormulaSat].
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

Lemma raw_sameContextOrIntroductionRight_child_endpoint_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPASameContextOrIntroductionRightChildEndpointTemplate <->
  RawProofRuleValid M (variables 2) (variables 7) (variables 5).
Proof.
  intros M variables parameters predicates.
  rewrite
    coqRestrictedPASameContextOrIntroductionRight_child_endpoint_shape.
  rewrite rawTemplateFormulaSat_embedPA,
    raw_sat_proofRuleValidTermAt_iff.
  cbn [raw_term_eval]. reflexivity.
Qed.

Lemma raw_sameContextOrIntroductionRight_child_admissible_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPASameContextOrIntroductionRightChildAdmissibleTemplate <->
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
  rewrite
    coqRestrictedPASameContextOrIntroductionRight_child_admissible_shape.
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

Lemma raw_sameContextOrIntroductionRight_child_interface_renamed_sat_iff :
  forall (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    (templateFormulaRename S
      coqRestrictedPASameContextOrIntroductionRightChildInterfaceTemplate) <->
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
  rewrite
    coqRestrictedPASameContextOrIntroductionRight_child_interface_shape.
  cbn [rawTemplateFormulaSat].
  rewrite raw_sameContextUnary_child_below_sat_iff,
    raw_sameContextOrIntroductionRight_child_restricted_sat_iff,
    raw_sameContextOrIntroductionRight_child_endpoint_sat_iff,
    raw_sameContextOrIntroductionRight_child_admissible_sat_iff.
  cbn. tauto.
Qed.

(** ------------------------------------------------------------------
    The four semantic rule instances. *)

Theorem raw_sameContextAndElimination_openedCoverageLaw_valid : forall
    (projection : RawAndProjection) (M : RawPAModel), RawPASatisfies M ->
  forall variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    (coqRestrictedPASameContextUnaryOpenedCoverageLawTemplate
      (match projection with
       | RawAndLeft => CoqSameContextAndEliminationLeft
       | RawAndRight => CoqSameContextAndEliminationRight
       end)).
Proof.
  intros projection M hPA variables parameters predicates.
  destruct projection;
    unfold coqRestrictedPASameContextUnaryOpenedCoverageLawTemplate;
    cbn [coqRestrictedPASameContextUnaryCaseTemplate
      coqRestrictedPASameContextUnaryChildInterfaceTemplate
      coqRestrictedPASameContextUnaryChildTerm
      coqRestrictedPASameContextUnaryWitnessContextTerm
      coqRestrictedPASameContextUnaryChildConclusionTerm
      rawTemplateFormulaSat];
    intros hrestricted hatomic _ hruleCoverage _ hcommonCoverage hcase.
  - pose proof (raw_sameContextUnary_opened_parent_facts M variables
      parameters predicates hrestricted hatomic hruleCoverage
      hcommonCoverage) as hparent.
    destruct hparent as
      [hparentRestricted hparentAtomic hparentRuleCoverage
        hparentFormulaCoverage hassignmentCoverage].
    rewrite rawTemplateFormulaSat_rename in hcase.
    rewrite coqRestrictedPADirectAndEliminationLeft_case_shape in hcase.
    cbn [rawTemplateFormulaSat] in hcase.
    destruct hcase as [hcode [_ [hformula [hendpoint _]]]].
    unfold coqRestrictedPADirectAndEliminationLeftCodeEqualityTemplate
      in hcode.
    rewrite rawTemplateFormulaSat_embedPA in hcode.
    cbn [raw_formula_sat raw_term_eval] in hcode.
    unfold coqRestrictedPADirectAndEliminationLeftFormulaCodeTemplate
      in hformula.
    rewrite rawTemplateFormulaSat_embedPA,
      raw_sat_formulaAndCodeTermAt_iff in hformula.
    cbn [raw_term_eval] in hformula.
    unfold coqRestrictedPADirectAndEliminationLeftChildEndpointTemplate
      in hendpoint.
    rewrite rawTemplateFormulaSat_embedPA,
      raw_sat_proofEndpointTermAt_iff in hendpoint.
    cbn [raw_term_eval] in hendpoint.
    rewrite hformula in hendpoint.
    destruct (raw_andElimination_child_interface M hPA
      (fun index => variables (S (index + 8)))
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      RawAndLeft (variables 13) (variables 0) (variables 8)
      (variables 7) (variables 6) (variables 3)
      (variables 10) (variables 9)
      hparentRestricted hparentAtomic hparentFormulaCoverage
      hparentRuleCoverage hcode hendpoint hassignmentCoverage) as
      [hbelow [hchildRestricted [hchildAtomic
        [hchildFormulaCoverage [hchildRuleCoverage [hchildRuleValid
          [hformulaAtomic [hformulaDefined hformulaBounded]]]]]]]].
    apply (proj2
      (raw_sameContextAndElimination_child_interface_renamed_sat_iff
        M variables parameters predicates)).
    rewrite hformula.
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
    rewrite coqRestrictedPADirectAndEliminationRight_case_shape in hcase.
    cbn [rawTemplateFormulaSat] in hcase.
    destruct hcase as [hcode [_ [hformula [hendpoint _]]]].
    unfold coqRestrictedPADirectAndEliminationRightCodeEqualityTemplate
      in hcode.
    rewrite rawTemplateFormulaSat_embedPA in hcode.
    cbn [raw_formula_sat raw_term_eval] in hcode.
    unfold coqRestrictedPADirectAndEliminationRightFormulaCodeTemplate
      in hformula.
    rewrite rawTemplateFormulaSat_embedPA,
      raw_sat_formulaAndCodeTermAt_iff in hformula.
    cbn [raw_term_eval] in hformula.
    unfold coqRestrictedPADirectAndEliminationRightChildEndpointTemplate
      in hendpoint.
    rewrite rawTemplateFormulaSat_embedPA,
      raw_sat_proofEndpointTermAt_iff in hendpoint.
    cbn [raw_term_eval] in hendpoint.
    rewrite hformula in hendpoint.
    destruct (raw_andElimination_child_interface M hPA
      (fun index => variables (S (index + 8)))
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      RawAndRight (variables 13) (variables 0) (variables 8)
      (variables 7) (variables 6) (variables 3)
      (variables 10) (variables 9)
      hparentRestricted hparentAtomic hparentFormulaCoverage
      hparentRuleCoverage hcode hendpoint hassignmentCoverage) as
      [hbelow [hchildRestricted [hchildAtomic
        [hchildFormulaCoverage [hchildRuleCoverage [hchildRuleValid
          [hformulaAtomic [hformulaDefined hformulaBounded]]]]]]]].
    apply (proj2
      (raw_sameContextAndElimination_child_interface_renamed_sat_iff
        M variables parameters predicates)).
    rewrite hformula.
    repeat split; try assumption.
    + exists (variables 0). exact hchildFormulaCoverage.
    + exists (variables 0). split; assumption.
Qed.

Theorem raw_sameContextOrIntroductionRight_openedCoverageLaw_valid : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    (coqRestrictedPASameContextUnaryOpenedCoverageLawTemplate
      CoqSameContextOrIntroductionRight).
Proof.
  intros M hPA variables parameters predicates.
  unfold coqRestrictedPASameContextUnaryOpenedCoverageLawTemplate.
  cbn [coqRestrictedPASameContextUnaryCaseTemplate
    coqRestrictedPASameContextUnaryChildInterfaceTemplate
    coqRestrictedPASameContextUnaryChildTerm
    coqRestrictedPASameContextUnaryWitnessContextTerm
    coqRestrictedPASameContextUnaryChildConclusionTerm
    rawTemplateFormulaSat].
  intros hrestricted hatomic _ hruleCoverage _ hcommonCoverage hcase.
  pose proof (raw_sameContextUnary_opened_parent_facts M variables
    parameters predicates hrestricted hatomic hruleCoverage
    hcommonCoverage) as hparent.
  destruct hparent as
    [hparentRestricted hparentAtomic hparentRuleCoverage
      hparentFormulaCoverage hassignmentCoverage].
  rewrite rawTemplateFormulaSat_rename in hcase.
  rewrite coqRestrictedPADirectOrIntroductionRight_case_shape in hcase.
  cbn [rawTemplateFormulaSat] in hcase.
  destruct hcase as [hcode [_ [hendpoint _]]].
  unfold coqRestrictedPADirectOrIntroductionRightCodeEqualityTemplate
    in hcode.
  rewrite rawTemplateFormulaSat_embedPA in hcode.
  cbn [raw_formula_sat raw_term_eval] in hcode.
  unfold coqRestrictedPADirectOrIntroductionRightChildEndpointTemplate
    in hendpoint.
  rewrite rawTemplateFormulaSat_embedPA,
    raw_sat_proofEndpointTermAt_iff in hendpoint.
  cbn [raw_term_eval] in hendpoint.
  destruct (raw_orIntroduction_child_interface M hPA
    (fun index => variables (S (index + 8)))
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    RawOrRight (variables 13) (variables 0) (variables 8)
    (variables 7) (variables 6) (variables 3)
    (variables 10) (variables 9)
    hparentRestricted hparentAtomic hparentFormulaCoverage
    hparentRuleCoverage hcode hendpoint hassignmentCoverage) as
    [hbelow [hchildRestricted [hchildAtomic
      [hchildFormulaCoverage [hchildRuleCoverage [hchildRuleValid
        [hformulaAtomic [hformulaDefined hformulaBounded]]]]]]]].
  apply (proj2
    (raw_sameContextOrIntroductionRight_child_interface_renamed_sat_iff
      M variables parameters predicates)).
  repeat split; try assumption.
  - exists (variables 0). exact hchildFormulaCoverage.
  - exists (variables 0). split; assumption.
Qed.

Theorem raw_sameContextUnary_openedCoverageLaw_valid : forall
    (rule : CoqRestrictedPASameContextUnaryRule)
    (M : RawPAModel), RawPASatisfies M ->
  forall variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    (coqRestrictedPASameContextUnaryOpenedCoverageLawTemplate rule).
Proof.
  intros rule M hPA variables parameters predicates.
  destruct rule.
  - exact (raw_sameContextAndElimination_openedCoverageLaw_valid
      RawAndLeft M hPA variables parameters predicates).
  - exact (raw_sameContextAndElimination_openedCoverageLaw_valid
      RawAndRight M hPA variables parameters predicates).
  - change (rawTemplateFormulaSat M variables parameters predicates
      coqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawTemplate).
    exact (raw_coqRestrictedPADirectOrIntroductionLeftOpenedCoverageLaw_valid
      M hPA variables parameters predicates).
  - exact (raw_sameContextOrIntroductionRight_openedCoverageLaw_valid
      M hPA variables parameters predicates).
Qed.

(** ------------------------------------------------------------------
    One reified and PA-provable source family. *)

Definition coqRestrictedPASameContextUnaryOpenedCoverageSourceBodyTemplate
    (rule : CoqRestrictedPASameContextUnaryRule) : TemplateFormula :=
  templateFormulaAbstractParameter
    coqRestrictedPASoundnessLowerLevelParameterName
    (coqRestrictedPASameContextUnaryOpenedCoverageLawTemplate rule).

Definition coqRestrictedPASameContextUnaryOpenedCoverageSourceBodyFormula
    (rule : CoqRestrictedPASameContextUnaryRule) : formula :=
  match templateFormulaAsPAFormula
    (coqRestrictedPASameContextUnaryOpenedCoverageSourceBodyTemplate rule)
  with
  | Some output => output
  | None => pBot
  end.

Definition coqRestrictedPASameContextUnaryOpenedCoverageSourceFormula
    (rule : CoqRestrictedPASameContextUnaryRule) : formula :=
  pAll
    (coqRestrictedPASameContextUnaryOpenedCoverageSourceBodyFormula rule).

Lemma coqRestrictedPASameContextUnaryOpenedCoverageSource_reifies :
  forall rule,
  templateFormulaAsPAFormula
    (coqRestrictedPASameContextUnaryOpenedCoverageSourceBodyTemplate rule) =
  Some
    (coqRestrictedPASameContextUnaryOpenedCoverageSourceBodyFormula rule).
Proof. intro rule. destruct rule; vm_compute; reflexivity. Qed.

Theorem coqRestrictedPASameContextUnaryOpenedCoverageSource_embed :
  forall rule,
  embedPAFormula
    (coqRestrictedPASameContextUnaryOpenedCoverageSourceBodyFormula rule) =
  coqRestrictedPASameContextUnaryOpenedCoverageSourceBodyTemplate rule.
Proof.
  intro rule. apply templateFormulaAsPAFormula_sound.
  apply coqRestrictedPASameContextUnaryOpenedCoverageSource_reifies.
Qed.

Theorem coqRestrictedPASameContextUnaryOpenedCoverageSource_open :
  forall rule,
  templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
    (embedPAFormula
      (coqRestrictedPASameContextUnaryOpenedCoverageSourceBodyFormula rule)) =
  coqRestrictedPASameContextUnaryOpenedCoverageLawTemplate rule.
Proof.
  intro rule.
  rewrite coqRestrictedPASameContextUnaryOpenedCoverageSource_embed.
  apply templateFormulaAbstractParameter_open.
Qed.

Theorem raw_sameContextUnary_openedCoverageSource_valid : forall
    rule (M : RawPAModel), RawPASatisfies M -> forall variables,
  raw_formula_sat M variables
    (coqRestrictedPASameContextUnaryOpenedCoverageSourceFormula rule).
Proof.
  intros rule M hPA variables.
  unfold coqRestrictedPASameContextUnaryOpenedCoverageSourceFormula.
  apply (raw_formula_sat_all_of_embedded_template_validity M
    (coqRestrictedPASameContextUnaryOpenedCoverageSourceBodyFormula rule)
    (fun _ : TemplateParameterName => raw_zero M)
    (fun (_ : TemplatePredicateName) (_ : list M) => True)).
  intros inner level.
  rewrite coqRestrictedPASameContextUnaryOpenedCoverageSource_embed.
  unfold coqRestrictedPASameContextUnaryOpenedCoverageSourceBodyTemplate.
  apply (proj2 (rawTemplateFormulaSat_abstractParameter M
    inner
    (fun _ : TemplateParameterName => raw_zero M)
    (fun (_ : TemplatePredicateName) (_ : list M) => True)
    coqRestrictedPASoundnessLowerLevelParameterName level
    (coqRestrictedPASameContextUnaryOpenedCoverageLawTemplate rule))).
  apply raw_sameContextUnary_openedCoverageLaw_valid. exact hPA.
Qed.

Theorem PA_proves_coqRestrictedPASameContextUnaryOpenedCoverageSource :
  forall rule,
  Formula.BProv Formula.Ax_s []
    (coqRestrictedPASameContextUnaryOpenedCoverageSourceFormula rule).
Proof.
  intro rule.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA
        (coqRestrictedPASameContextUnaryOpenedCoverageSourceFormula rule))).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA variables.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact (raw_sameContextUnary_openedCoverageSource_valid
        rule M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename Formula.Ax_s []
    (coqRestrictedPASameContextUnaryOpenedCoverageSourceFormula rule)
    (fun index => index) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

Lemma rawDirect_sameContextUnaryOpenedCoverageSourceBody_agreement : forall
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) rule,
  rawDirectTemplateFormula inputs
    (embedPAFormula
      (coqRestrictedPASameContextUnaryOpenedCoverageSourceBodyFormula rule)) =
  rawQuotedFormulaCode M
    (coqRestrictedPASameContextUnaryOpenedCoverageSourceBodyFormula rule).
Proof.
  intros M inputs rule. unfold rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

Theorem rawDirect_sameContextUnaryOpenedCoverageSource_substitution : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (inputs : RawCodedTemplateDirectStructuralInputs M) rule,
  RawCodedFormulaSingleSubstitution M
    (rawDirectTemplateTerm inputs coqRestrictedPASoundnessLowerLevelTerm)
    (rawQuotedFormulaCode M
      (coqRestrictedPASameContextUnaryOpenedCoverageSourceBodyFormula rule))
    (rawDirectTemplateFormula inputs
      (coqRestrictedPASameContextUnaryOpenedCoverageLawTemplate rule)).
Proof.
  intros M hPA inputs rule.
  pose proof (rawDirectTemplateFormula_open M hPA inputs
    (embedPAFormula
      (coqRestrictedPASameContextUnaryOpenedCoverageSourceBodyFormula rule))
    coqRestrictedPASoundnessLowerLevelTerm) as hopen.
  rewrite rawDirect_sameContextUnaryOpenedCoverageSourceBody_agreement
    in hopen.
  rewrite coqRestrictedPASameContextUnaryOpenedCoverageSource_open in hopen.
  exact hopen.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryChildInterfaceOpenedCoverageSource.
