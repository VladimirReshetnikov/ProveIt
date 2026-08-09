(**
  Template semantics and validity of the two-child opened-coverage law.

  This is one acyclic strict-check boundary of the And-I child compiler.
  Later stages import this module opaquely so Rocq need not recheck its proof
  terms while validating the next represented-proof construction.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  PolynomialPairInjectivity
  RawModelCompleteness
  RawCodedAssignment
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedContextLists
  RawCodedProofConstructors
  RawCodedProofDescent
  RawCodedProofTraversal
  RawCodedProofEndpoints
  RawCodedProofRules
  RawCodedProofAndIConstructor
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedRestrictedPAProof
  RawCodedRestrictedProofAdmissibility
  RawCodedCarrierRestrictedProofReroot
  RawCodedRestrictedPADerivationSoundnessRecursiveChildInterface
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedTargetTemplateSemantics
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
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
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildInterfaceSemanticCompilation.

Import ListNotations.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedProofAdmissibility.
Import PABoundedRawCodedCarrierRestrictedProofReroot.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessRecursiveChildInterface.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedTargetTemplateSemantics.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
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
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageValidity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionChildInterfaceSemanticCompilation.

(** ------------------------------------------------------------------
    Exact template pair produced under the coverage eigenvariable. *)

Definition coqRestrictedPADirectAndIntroductionLeftInterfaceResultTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    coqRestrictedPADirectAndIntroductionLeftChildTerm
    coqRestrictedPADirectAndIntroductionWitnessContextTerm
    coqRestrictedPADirectAndIntroductionLeftFormulaTerm.

Definition coqRestrictedPADirectAndIntroductionRightInterfaceResultTemplate
    : TemplateFormula :=
  coqRestrictedPADirectAndIntroductionChildInterfaceResultTemplate
    coqRestrictedPADirectAndIntroductionRightChildTerm
    coqRestrictedPADirectAndIntroductionWitnessContextTerm
    coqRestrictedPADirectAndIntroductionRightFormulaTerm.

Definition coqRestrictedPADirectAndIntroductionChildInterfacePairTemplate
    : TemplateFormula :=
  tfAnd
    coqRestrictedPADirectAndIntroductionLeftInterfaceResultTemplate
    coqRestrictedPADirectAndIntroductionRightInterfaceResultTemplate.

Definition coqRestrictedPADirectAndIntroductionCoverageEigenContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate ::
  templateContextShift
    (coqRestrictedPADirectStrongStepAndIntroductionReadyContext tail).

Arguments coqRestrictedPADirectAndIntroductionCoverageEigenContext
  tail : clear implicits.

(** Fold the nine immediate pieces before defining the law.  Besides making
    later reification certificates independently checkable, these names keep
    the law's implication/conjunction spine syntactically visible without a
    conversion through either child-interface body. *)
Definition coqRestrictedPADirectAndIntroductionOpenedRestrictedTemplate
    : TemplateFormula :=
  templateFormulaRename S
    coqRestrictedPADirectOrIntroductionLeftDeepRestrictedCoreTemplate.

Definition coqRestrictedPADirectAndIntroductionOpenedAtomicTemplate
    : TemplateFormula :=
  templateFormulaRename S
    coqRestrictedPADirectOrIntroductionLeftDeepAtomicTemplate.

Definition coqRestrictedPADirectAndIntroductionOpenedFormulaCoverageTemplate
    : TemplateFormula :=
  templateFormulaRename S
    coqRestrictedPADirectOrIntroductionLeftDeepHasCoverageTemplate.

Definition coqRestrictedPADirectAndIntroductionOpenedRuleCoverageTemplate
    : TemplateFormula :=
  templateFormulaRename S
    coqRestrictedPADirectOrIntroductionLeftDeepRuleCoverageTemplate.

Definition coqRestrictedPADirectAndIntroductionOpenedAdmissibleCoreTemplate
    : TemplateFormula :=
  templateFormulaRename S
    coqRestrictedPADirectOrIntroductionLeftDeepAdmissibleCoreTemplate.

Definition coqRestrictedPADirectAndIntroductionOpenedCommonCoverageTemplate
    : TemplateFormula :=
  coqRestrictedPADirectOrIntroductionLeftDeepCommonCoverageBodyTemplate.

Definition coqRestrictedPADirectAndIntroductionOpenedCaseTemplate
    : TemplateFormula :=
  templateFormulaRename S
    coqRestrictedPADirectAndIntroductionCaseTemplate.

Definition coqRestrictedPADirectAndIntroductionOpenedLeftResultTemplate
    : TemplateFormula :=
  templateFormulaRename S
    coqRestrictedPADirectAndIntroductionLeftInterfaceResultTemplate.

Definition coqRestrictedPADirectAndIntroductionOpenedRightResultTemplate
    : TemplateFormula :=
  templateFormulaRename S
    coqRestrictedPADirectAndIntroductionRightInterfaceResultTemplate.

Definition
    coqRestrictedPADirectAndIntroductionOpenedCoverageCompilerLawTemplate
    : TemplateFormula :=
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
              (tfImp coqRestrictedPADirectAndIntroductionOpenedCaseTemplate
                (tfAnd
                  coqRestrictedPADirectAndIntroductionOpenedLeftResultTemplate
                  coqRestrictedPADirectAndIntroductionOpenedRightResultTemplate))))))).

Definition
    RawCoqRestrictedPADirectAndIntroductionOpenedCoverageCompilerLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectAndIntroductionCoverageEigenContext tail))
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectAndIntroductionOpenedCoverageCompilerLawTemplate)
      root.

Arguments
  RawCoqRestrictedPADirectAndIntroductionOpenedCoverageCompilerLawRoot
  M hPA inputs tail : clear implicits.

(** ------------------------------------------------------------------
    Syntactic and semantic views of the right child.  The left child is
    definitionally the existing Or-I-left interface and reuses its audit. *)

Definition coqRestrictedPADirectAndIntroductionRightRestrictedCoreTemplate
    : TemplateFormula :=
  coqRestrictedPADirectTemplateAndLeft
    coqRestrictedPADirectAndIntroductionRightRestrictedTemplate.

Lemma coqRestrictedPADirectAndIntroduction_right_interface_shape :
  coqRestrictedPADirectAndIntroductionRightInterfaceResultTemplate =
  tfAnd coqRestrictedPADirectAndIntroductionRightBelowTemplate
    (tfAnd coqRestrictedPADirectAndIntroductionRightRestrictedTemplate
      (tfAnd
        coqRestrictedPADirectAndIntroductionRightPredicateEndpointTemplate
        coqRestrictedPADirectAndIntroductionRightAdmissibleTemplate)).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_right_restricted_shape :
  coqRestrictedPADirectAndIntroductionRightRestrictedTemplate =
  tfAnd coqRestrictedPADirectAndIntroductionRightRestrictedCoreTemplate
    (tfAnd
      (embedPAFormula (proofAtomicallyAdequateTermAt (tVar 1)))
      (tfAnd
        (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 1)))
        (embedPAFormula (proofRuleCoverageTermAt (tVar 1))))).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_right_restricted_core_shape :
  coqRestrictedPADirectAndIntroductionRightRestrictedCoreTemplate =
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetProofContext (tVar 1)).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_right_endpoint_shape :
  coqRestrictedPADirectAndIntroductionRightPredicateEndpointTemplate =
  embedPAFormula
    (proofRuleValidTermAt (tVar 1) (tVar 7) (tVar 5)).
Proof. reflexivity. Qed.

Lemma coqRestrictedPADirectAndIntroduction_right_admissible_shape :
  coqRestrictedPADirectAndIntroductionRightAdmissibleTemplate =
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
          (proofFormulaCoverageTermAt (tVar 2) (tVar 0))
          (codedAssignmentDefinedThroughTermAt
            (tVar 10) (tVar 9) (tVar 0))))).
Proof. reflexivity. Qed.

Lemma raw_andIntroduction_right_child_restricted_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectAndIntroductionRightRestrictedTemplate <->
  RawCarrierRestrictedProofAt M variables
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      (variables 1) /\
  RawProofAtomicallyAdequate M (variables 1) /\
  RawProofHasFormulaCoverage M (variables 1) /\
  RawProofRuleCoverage M (variables 1).
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPADirectAndIntroduction_right_restricted_shape.
  cbn [rawTemplateFormulaSat].
  rewrite coqRestrictedPADirectAndIntroduction_right_restricted_core_shape.
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

Lemma raw_andIntroduction_right_child_endpoint_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectAndIntroductionRightPredicateEndpointTemplate <->
  RawProofRuleValid M (variables 1) (variables 7) (variables 5).
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPADirectAndIntroduction_right_endpoint_shape.
  rewrite rawTemplateFormulaSat_embedPA.
  rewrite raw_sat_proofRuleValidTermAt_iff.
  cbn [raw_term_eval]. reflexivity.
Qed.

Lemma raw_andIntroduction_right_child_admissible_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectAndIntroductionRightAdmissibleTemplate <->
  RawCodedFormulaAtomicallyAdequate M (variables 5) /\
  RawCodedAssignmentDefinedThrough M
    (variables 9) (variables 8) (variables 5) /\
  RawCarrierFormulaQuantifierBounded M
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 5) /\
  exists coverageBound,
    RawProofFormulaCoverage M (variables 1) coverageBound /\
    RawCodedAssignmentDefinedThrough M
      (variables 9) (variables 8) coverageBound.
Proof.
  intros M variables parameters predicates.
  rewrite coqRestrictedPADirectAndIntroduction_right_admissible_shape.
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

Lemma raw_andIntroduction_right_child_interface_renamed_sat_iff : forall
    (M : RawPAModel) variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    (templateFormulaRename S
      coqRestrictedPADirectAndIntroductionRightInterfaceResultTemplate) <->
  rawLt M (variables 2) (variables 13) /\
  RawCarrierRestrictedProofAt M (fun index => variables (S index))
      (parameters coqRestrictedPASoundnessLowerLevelParameterName)
      (variables 2) /\
  RawProofAtomicallyAdequate M (variables 2) /\
  RawProofHasFormulaCoverage M (variables 2) /\
  RawProofRuleCoverage M (variables 2) /\
  RawProofRuleValid M (variables 2) (variables 8) (variables 6) /\
  RawCodedFormulaAtomicallyAdequate M (variables 6) /\
  RawCodedAssignmentDefinedThrough M
    (variables 10) (variables 9) (variables 6) /\
  RawCarrierFormulaQuantifierBounded M
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 6) /\
  exists coverageBound,
    RawProofFormulaCoverage M (variables 2) coverageBound /\
    RawCodedAssignmentDefinedThrough M
      (variables 10) (variables 9) coverageBound.
Proof.
  intros M variables parameters predicates.
  rewrite rawTemplateFormulaSat_rename.
  rewrite coqRestrictedPADirectAndIntroduction_right_interface_shape.
  cbn [rawTemplateFormulaSat].
  rewrite coqRestrictedPADirectAndIntroduction_right_below_shape.
  rewrite rawTemplateFormulaSat_embedPA, raw_sat_ltTermAt_iff.
  cbn [raw_term_eval].
  repeat rewrite raw_term_eval_liftTerm.
  rewrite raw_andIntroduction_right_child_restricted_sat_iff,
    raw_andIntroduction_right_child_endpoint_sat_iff,
    raw_andIntroduction_right_child_admissible_sat_iff.
  tauto.
Qed.

(** ------------------------------------------------------------------
    Raw validity of the seven-premise source. *)

Theorem
    raw_coqRestrictedPADirectAndIntroductionOpenedCoverageLaw_valid :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPADirectAndIntroductionOpenedCoverageCompilerLawTemplate.
Proof.
  intros M hPA variables parameters predicates.
  unfold
    coqRestrictedPADirectAndIntroductionOpenedCoverageCompilerLawTemplate,
    coqRestrictedPADirectAndIntroductionOpenedRestrictedTemplate,
    coqRestrictedPADirectAndIntroductionOpenedAtomicTemplate,
    coqRestrictedPADirectAndIntroductionOpenedFormulaCoverageTemplate,
    coqRestrictedPADirectAndIntroductionOpenedRuleCoverageTemplate,
    coqRestrictedPADirectAndIntroductionOpenedAdmissibleCoreTemplate,
    coqRestrictedPADirectAndIntroductionOpenedCommonCoverageTemplate,
    coqRestrictedPADirectAndIntroductionOpenedCaseTemplate,
    coqRestrictedPADirectAndIntroductionOpenedLeftResultTemplate,
    coqRestrictedPADirectAndIntroductionOpenedRightResultTemplate.
  cbn [rawTemplateFormulaSat].
  intros hrestricted hatomic hformulaCoverage hruleCoverage
    _hadmissibleCore hcommonCoverage hcase.

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

  rewrite rawTemplateFormulaSat_rename in hformulaCoverage.
  unfold coqRestrictedPADirectOrIntroductionLeftDeepHasCoverageTemplate
    in hformulaCoverage.
  rewrite rawTemplateFormulaSat_rawCoqTemplateRenameN in hformulaCoverage.
  rewrite rawTemplateFormulaSat_embedPA in hformulaCoverage.
  rewrite raw_sat_proofHasFormulaCoverageTermAt_iff in hformulaCoverage.
  cbn [raw_term_eval] in hformulaCoverage.

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
  destruct hcommonCoverage as [hparentCoverage hassignmentCoverage].

  rewrite rawTemplateFormulaSat_rename in hcase.
  rewrite coqRestrictedPADirectAndIntroduction_case_shape in hcase.
  cbn [rawTemplateFormulaSat] in hcase.
  destruct hcase as
    [hcode [_formulaAnd [hleftEndpoint [hrightEndpoint _terminal]]]].
  unfold coqRestrictedPADirectAndIntroductionCodeEqualityTemplate in hcode.
  rewrite rawTemplateFormulaSat_embedPA in hcode.
  cbn [raw_formula_sat raw_term_eval] in hcode.
  unfold coqRestrictedPADirectAndIntroductionLeftEndpointTemplate
    in hleftEndpoint.
  rewrite rawTemplateFormulaSat_embedPA in hleftEndpoint.
  rewrite raw_sat_proofEndpointTermAt_iff in hleftEndpoint.
  cbn [raw_term_eval] in hleftEndpoint.
  unfold coqRestrictedPADirectAndIntroductionRightEndpointTemplate
    in hrightEndpoint.
  rewrite rawTemplateFormulaSat_embedPA in hrightEndpoint.
  rewrite raw_sat_proofEndpointTermAt_iff in hrightEndpoint.
  cbn [raw_term_eval] in hrightEndpoint.

  pose proof (raw_andIntroduction_child_interface M hPA
    (fun index => variables (S (index + 8)))
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 13) (variables 0) (variables 8)
    (variables 7) (variables 6) (variables 3) (variables 2)
    (variables 3) (variables 7) (variables 10) (variables 9)
    hrestricted hatomic hparentCoverage hruleCoverage hcode
    (or_introl eq_refl) hleftEndpoint hassignmentCoverage) as hleft.
  pose proof (raw_andIntroduction_child_interface M hPA
    (fun index => variables (S (index + 8)))
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 13) (variables 0) (variables 8)
    (variables 7) (variables 6) (variables 3) (variables 2)
    (variables 2) (variables 6) (variables 10) (variables 9)
    hrestricted hatomic hparentCoverage hruleCoverage hcode
    (or_intror (or_introl eq_refl)) hrightEndpoint hassignmentCoverage)
    as hright.

  cbn [rawTemplateFormulaSat]. split.
  - apply (proj2
      (raw_orIntroductionLeft_child_interface_renamed_sat_iff
        M variables parameters predicates)).
    destruct hleft as
      [hbelow [hchildRestricted [hchildAtomic [hchildHasCoverage
        [hchildRuleCoverage [hchildRuleValid
          [hformulaAtomic [hformulaDefined hformulaBounded]]]]]]]].
    split; [exact hbelow |].
    split; [exact hchildRestricted |].
    split; [exact hchildAtomic |].
    split; [exists (variables 0); exact hchildHasCoverage |].
    split; [exact hchildRuleCoverage |].
    split; [exact hchildRuleValid |].
    split; [exact hformulaAtomic |].
    split; [exact hformulaDefined |].
    split; [exact hformulaBounded |].
    exists (variables 0). split.
    + exact hchildHasCoverage.
    + exact hassignmentCoverage.
  - apply (proj2
      (raw_andIntroduction_right_child_interface_renamed_sat_iff
        M variables parameters predicates)).
    destruct hright as
      [hbelow [hchildRestricted [hchildAtomic [hchildHasCoverage
        [hchildRuleCoverage [hchildRuleValid
          [hformulaAtomic [hformulaDefined hformulaBounded]]]]]]]].
    split; [exact hbelow |].
    split; [exact hchildRestricted |].
    split; [exact hchildAtomic |].
    split; [exists (variables 0); exact hchildHasCoverage |].
    split; [exact hchildRuleCoverage |].
    split; [exact hchildRuleValid |].
    split; [exact hformulaAtomic |].
    split; [exact hformulaDefined |].
    split; [exact hformulaBounded |].
    exists (variables 0). split.
    + exact hchildHasCoverage.
    + exact hassignmentCoverage.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
