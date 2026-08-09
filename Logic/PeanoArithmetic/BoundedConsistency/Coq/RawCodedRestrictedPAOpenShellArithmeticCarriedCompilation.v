(**
  Carried arithmetic roots for the direct restricted-consistency shell.

  The admissibility, endpoint boundedness, and endpoint-context adequacy
  facts are ordinary PA theorems, but a represented proof of any one may use
  a finite standard PA-axiom prefix absent from the caller's witnessed base.
  Consequently the honest result is growing: it returns the extended
  witnessed base and proves the requested root in the *exact* bridge-body
  context rebuilt over that base.

  This module also proves the binder-safe transport needed to carry an
  already constructed bridge-body root through a later witnessed extension.
  That transport is important when the two fixed PA theorems select different
  standard prefixes.  No formula is decoded and no semantic truth is turned
  directly into a local proof.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawModelCompleteness
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedAssignment
  RawCodedAssignmentTotality
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedNumeralTermCode
  RawCodedFixedLevelTruthTotality
  RawCodedProofAllEConstructor
  RawCodedProofEndpoints
  RawCodedProofAtomicAdequacy
  RawCodedProofAtomicAdequacyStandard
  RawCodedProofFormulaCoverage
  RawCodedProofRules
  RawCodedRestrictedPAProof
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofUniversalElimination
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedTemplateParameterAbstraction
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedTargetTemplateSemantics
  RawCodedCarrierRestrictedProofReroot
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedPAProjectedFieldRefutation
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridge
  RawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenShell
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenIntegration.

Import ListNotations.

Module PABoundedRawCodedRestrictedPAOpenShellArithmeticCarriedCompilation.

Import PA.
Import PABoundedCodedProof.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofUniversalElimination.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedTargetTemplateSemantics.
Import PABoundedRawCodedCarrierRestrictedProofReroot.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedPAProjectedFieldRefutation.
Import PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridge.
Import PABoundedRawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenShell.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenIntegration.

(** ------------------------------------------------------------------
    Fixed endpoint-context arithmetic laws. *)

Definition coqRestrictedPAOpenEndpointOccurrenceTemplate : TemplateFormula :=
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetProofContext (tVar 1)).

(** The carrier endpoint theorem already stores context boundedness together
    with conclusion boundedness.  The older public projection selected only
    the latter; this is its equally direct first projection. *)
Theorem raw_carrierRestrictedProof_endpoint_context_bounded : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail level root,
  RawCarrierRestrictedProofAt M tail level root ->
  forall context conclusion,
  RawProofEndpoint M root context conclusion ->
  RawCarrierContextAllBounded M level context.
Proof.
  intros M hPA tail level root
    (supportCode & supportStep & [htraversal hrootSupported])
    context conclusion hendpoint.
  destruct htraversal as [hdefined hnodes].
  pose proof (hnodes root
    (raw_assignment_lt_self_succ M hPA root)
    hrootSupported) as hrootNodeAt.
  apply (proj1 (raw_carrierRestrictedProofNodeAt_iff M tail level
    root supportCode supportStep)) in hrootNodeAt.
  destruct hrootNodeAt as [_ [_ [_ hendpointOccurrences]]].
  exact (proj1 (hendpointOccurrences context conclusion hendpoint)).
Qed.

Definition coqRestrictedPAOpenEndpointContextBoundedLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPAOpenEndpointOccurrenceTemplate
    (tfImp coqRestrictedPAOpenShellEndpointTemplate
      coqRestrictedPAOpenShellContextBoundedTemplate).

Theorem raw_coqRestrictedPAOpenEndpointContextBoundedLawTemplate_valid :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPAOpenEndpointContextBoundedLawTemplate.
Proof.
  intros M hPA variables parameters predicates.
  unfold coqRestrictedPAOpenEndpointContextBoundedLawTemplate,
    coqRestrictedPAOpenEndpointOccurrenceTemplate,
    coqRestrictedPAOpenShellEndpointTemplate,
    coqRestrictedPAOpenShellContextBoundedTemplate.
  cbn [rawTemplateFormulaSat].
  unfold coqRestrictedPASoundnessLowerLevelTerm.
  rewrite rawTemplateFormulaSat_restrictedTarget_parameter;
    [|apply restrictedTargetProofContext_seal_free].
  rewrite raw_carrierRestrictedProofContextSat_iff.
  rewrite rawTemplateFormulaSat_embedPA.
  rewrite raw_sat_proofRuleValidTermAt_iff.
  rewrite rawTemplateFormulaSat_restrictedTarget_parameter;
    [|apply restrictedTargetContextAllBoundedContext_seal_free].
  rewrite raw_restrictedTargetContextAllBoundedContextSat_iff.
  cbn [raw_term_eval].
  intros hrestricted hrule.
  exact (raw_carrierRestrictedProof_endpoint_context_bounded M hPA
    variables
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 1) hrestricted (variables 0) (rawFormulaBotCode M)
    (raw_proofRuleValid_endpoint M (variables 1) (variables 0)
      (rawFormulaBotCode M) hrule)).
Qed.

Definition coqRestrictedPAOpenEndpointContextBoundedSourceBodyTemplate
    : TemplateFormula :=
  templateFormulaAbstractParameter
    coqRestrictedPASoundnessLowerLevelParameterName
    coqRestrictedPAOpenEndpointContextBoundedLawTemplate.

Definition coqRestrictedPAOpenEndpointContextBoundedSourceBodyFormula
    : formula :=
  match templateFormulaAsPAFormula
    coqRestrictedPAOpenEndpointContextBoundedSourceBodyTemplate with
  | Some output => output
  | None => pBot
  end.

Definition coqRestrictedPAOpenEndpointContextBoundedSourceFormula
    : formula :=
  pAll coqRestrictedPAOpenEndpointContextBoundedSourceBodyFormula.

Lemma coqRestrictedPAOpenEndpointContextBoundedSource_reifies :
  templateFormulaAsPAFormula
    coqRestrictedPAOpenEndpointContextBoundedSourceBodyTemplate =
  Some coqRestrictedPAOpenEndpointContextBoundedSourceBodyFormula.
Proof. vm_compute. reflexivity. Qed.

Theorem coqRestrictedPAOpenEndpointContextBoundedSource_embed :
  embedPAFormula coqRestrictedPAOpenEndpointContextBoundedSourceBodyFormula =
  coqRestrictedPAOpenEndpointContextBoundedSourceBodyTemplate.
Proof.
  apply templateFormulaAsPAFormula_sound.
  exact coqRestrictedPAOpenEndpointContextBoundedSource_reifies.
Qed.

Theorem coqRestrictedPAOpenEndpointContextBoundedSource_open :
  templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
    (embedPAFormula
      coqRestrictedPAOpenEndpointContextBoundedSourceBodyFormula) =
  coqRestrictedPAOpenEndpointContextBoundedLawTemplate.
Proof.
  rewrite coqRestrictedPAOpenEndpointContextBoundedSource_embed.
  unfold coqRestrictedPAOpenEndpointContextBoundedSourceBodyTemplate.
  apply templateFormulaAbstractParameter_open.
Qed.

Theorem raw_coqRestrictedPAOpenEndpointContextBoundedSourceFormula_valid :
    forall (M : RawPAModel), RawPASatisfies M -> forall variables,
  raw_formula_sat M variables
    coqRestrictedPAOpenEndpointContextBoundedSourceFormula.
Proof.
  intros M hPA variables.
  unfold coqRestrictedPAOpenEndpointContextBoundedSourceFormula.
  cbn [raw_formula_sat]. intro level.
  pose (parameters :=
    (fun _ : TemplateParameterName => raw_zero M)).
  pose (predicates :=
    (fun (_ : TemplatePredicateName) (_ : list M) => True)).
  apply (proj1 (rawTemplateFormulaSat_embedPA M
    (scons M level variables) parameters predicates
    coqRestrictedPAOpenEndpointContextBoundedSourceBodyFormula)).
  rewrite coqRestrictedPAOpenEndpointContextBoundedSource_embed.
  unfold coqRestrictedPAOpenEndpointContextBoundedSourceBodyTemplate.
  apply (proj2 (rawTemplateFormulaSat_abstractParameter M
    variables parameters predicates
    coqRestrictedPASoundnessLowerLevelParameterName level
    coqRestrictedPAOpenEndpointContextBoundedLawTemplate)).
  exact (raw_coqRestrictedPAOpenEndpointContextBoundedLawTemplate_valid
    M hPA variables
    (fun name =>
      if templateParameterName_eq_dec name
        coqRestrictedPASoundnessLowerLevelParameterName
      then level else parameters name)
    predicates).
Qed.

Theorem PA_proves_coqRestrictedPAOpenEndpointContextBoundedSourceFormula :
  Formula.BProv Formula.Ax_s []
    coqRestrictedPAOpenEndpointContextBoundedSourceFormula.
Proof.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA
        coqRestrictedPAOpenEndpointContextBoundedSourceFormula)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA variables.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact
        (raw_coqRestrictedPAOpenEndpointContextBoundedSourceFormula_valid
          M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename Formula.Ax_s []
    coqRestrictedPAOpenEndpointContextBoundedSourceFormula
    (fun index => index) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

(** Context atomic adequacy is a second fixed arithmetic projection.  Its
    conclusion deliberately selects the context half, not the endpoint-
    formula half exposed by the older compilation module. *)
Definition restrictedPAOpenEndpointContextAtomicAdequacyFormula : formula :=
  pImp
    (proofAtomicallyAdequateTermAt (tVar 1))
    (pImp
      (proofRuleValidTermAt
        (tVar 1) (tVar 0) rawFormulaBotCodeTerm)
      (contextAllAtomicallyAdequateTermAt (tVar 0))).

Lemma raw_sat_restrictedPAOpenEndpointContextAtomicAdequacyFormula_iff :
    forall (M : RawPAModel) e,
  raw_formula_sat M e
    restrictedPAOpenEndpointContextAtomicAdequacyFormula <->
  (RawProofAtomicallyAdequate M (e 1) ->
   RawProofRuleValid M (e 1) (e 0) (rawFormulaBotCode M) ->
   RawContextAllAtomicallyAdequate M (e 0)).
Proof.
  intros M e.
  unfold restrictedPAOpenEndpointContextAtomicAdequacyFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofAtomicallyAdequateTermAt_iff.
  setoid_rewrite raw_sat_proofRuleValidTermAt_iff.
  setoid_rewrite raw_sat_contextAllAtomicallyAdequateTermAt_iff.
  cbn [raw_term_eval scons]. tauto.
Qed.

Theorem restrictedPAOpenEndpointContextAtomicAdequacyFormula_raw_valid :
    forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    restrictedPAOpenEndpointContextAtomicAdequacyFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_restrictedPAOpenEndpointContextAtomicAdequacyFormula_iff M e)).
  intros hatomic hrule.
  exact (proj1
    (raw_proofAtomicallyAdequate_root_endpoint M hPA
      (e 1) hatomic (e 0) (rawFormulaBotCode M)
      (raw_proofRuleValid_endpoint M (e 1) (e 0)
        (rawFormulaBotCode M) hrule))).
Qed.

Theorem PA_proves_restrictedPAOpenEndpointContextAtomicAdequacyFormula :
  Formula.BProv Formula.Ax_s []
    restrictedPAOpenEndpointContextAtomicAdequacyFormula.
Proof.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA
        restrictedPAOpenEndpointContextAtomicAdequacyFormula)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA e.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact
        (restrictedPAOpenEndpointContextAtomicAdequacyFormula_raw_valid
          M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename Formula.Ax_s []
    restrictedPAOpenEndpointContextAtomicAdequacyFormula
    (fun index => index) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

Definition coqRestrictedPAOpenEndpointContextAtomicAdequacyLawTemplate
    : TemplateFormula :=
  embedPAFormula restrictedPAOpenEndpointContextAtomicAdequacyFormula.

Lemma coqRestrictedPAOpenEndpointContextAtomicAdequacyLawTemplate_shape :
  coqRestrictedPAOpenEndpointContextAtomicAdequacyLawTemplate =
  tfImp
    (embedPAFormula (proofAtomicallyAdequateTermAt (tVar 1)))
    (tfImp coqRestrictedPAOpenShellEndpointTemplate
      coqRestrictedPAOpenShellContextAdequateTemplate).
Proof. reflexivity. Qed.

(** The last arithmetic root required by the open shell says that bottom is
    admissible at the canonical zero assignment and that the same assignment
    covers one proof-wide formula bound.  The following view keeps the exact
    result of the shell's five substitutions readable. *)
Definition coqRestrictedPAOpenShellAdmissibleExpandedTemplate
    : TemplateFormula :=
  tfAnd
    (tfAnd
      (embedPAFormula
        (codedFormulaAtomicallyAdequateTermAt rawFormulaBotCodeTerm))
      (tfAnd
        (embedPAFormula
          (codedAssignmentDefinedThroughTermAt
            tZero tZero rawFormulaBotCodeTerm))
        (restrictedTargetTemplateFormulaContext
          coqRestrictedPASoundnessLowerLevelTerm
          (restrictedTargetFormulaQuantifierBoundedContext
            rawFormulaBotCodeTerm))))
    (embedPAFormula
      (pEx
        (pAnd
          (proofFormulaCoverageTermAt (tVar 2) (tVar 0))
          (codedAssignmentDefinedThroughTermAt
            tZero tZero (tVar 0))))).

Lemma coqRestrictedPAOpenShellAdmissibleTemplate_expanded :
  coqRestrictedPAOpenShellAdmissibleTemplate =
  coqRestrictedPAOpenShellAdmissibleExpandedTemplate.
Proof. vm_compute. reflexivity. Qed.

(** Four already-projected fields suffice: carrier restriction supplies the
    endpoint rank, proof-wide atomic adequacy supplies the endpoint syntax,
    proof-wide formula coverage supplies a common bound, and rule validity
    identifies the displayed bottom endpoint. *)
Definition coqRestrictedPAOpenShellAdmissibilityLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPAOpenEndpointOccurrenceTemplate
    (tfImp
      (embedPAFormula (proofAtomicallyAdequateTermAt (tVar 1)))
      (tfImp
        (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 1)))
        (tfImp coqRestrictedPAOpenShellEndpointTemplate
          coqRestrictedPAOpenShellAdmissibleTemplate))).

Theorem raw_coqRestrictedPAOpenShellAdmissibilityLawTemplate_valid :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqRestrictedPAOpenShellAdmissibilityLawTemplate.
Proof.
  intros M hPA variables parameters predicates.
  unfold coqRestrictedPAOpenShellAdmissibilityLawTemplate.
  cbn [rawTemplateFormulaSat].
  intros hrestricted hatomic hcoverage hrule.
  unfold coqRestrictedPAOpenEndpointOccurrenceTemplate in hrestricted.
  unfold coqRestrictedPASoundnessLowerLevelTerm in hrestricted.
  rewrite rawTemplateFormulaSat_restrictedTarget_parameter in hrestricted;
    [|apply restrictedTargetProofContext_seal_free].
  apply (proj1 (raw_carrierRestrictedProofContextSat_iff M variables
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (tVar 1))) in hrestricted.
  cbn [raw_term_eval] in hrestricted.
  rewrite rawTemplateFormulaSat_embedPA,
    raw_sat_proofAtomicallyAdequateTermAt_iff in hatomic.
  cbn [raw_term_eval] in hatomic.
  rewrite rawTemplateFormulaSat_embedPA,
    raw_sat_proofHasFormulaCoverageTermAt_iff in hcoverage.
  cbn [raw_term_eval] in hcoverage.
  unfold coqRestrictedPAOpenShellEndpointTemplate in hrule.
  vm_compute in hrule.
  rewrite rawTemplateFormulaSat_embedPA,
    raw_sat_proofRuleValidTermAt_iff in hrule.
  cbn [raw_term_eval] in hrule.
  rewrite coqRestrictedPAOpenShellAdmissibleTemplate_expanded.
  unfold coqRestrictedPAOpenShellAdmissibleExpandedTemplate.
  cbn [rawTemplateFormulaSat].
  repeat rewrite rawTemplateFormulaSat_embedPA.
  rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff,
    raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  unfold coqRestrictedPASoundnessLowerLevelTerm.
  rewrite rawTemplateFormulaSat_restrictedTarget_parameter;
    [|apply restrictedTargetFormulaQuantifierBoundedContext_seal_free].
  rewrite raw_restrictedTargetFormulaQuantifierBoundedContextSat_iff.
  cbn [raw_formula_sat raw_term_eval scons].
  setoid_rewrite raw_sat_proofFormulaCoverageTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  cbn [raw_term_eval scons].
  pose proof (raw_proofRuleValid_endpoint M (variables 1) (variables 0)
    (rawFormulaBotCode M) hrule) as hendpoint.
  pose proof (raw_proofAtomicallyAdequate_root_endpoint M hPA
    (variables 1) hatomic (variables 0) (rawFormulaBotCode M) hendpoint)
    as [_ hbottomAtomic].
  pose proof (raw_carrierRestrictedProof_endpoint_formula_bounded M hPA
    variables
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 1) hrestricted (variables 0) (rawFormulaBotCode M)
    hendpoint) as hbottomBounded.
  destruct hcoverage as [coverageBound hcoverage].
  repeat split.
  - exact hbottomAtomic.
  - exact (raw_codedZeroAssignment_defined_all M hPA
      (rawFormulaBotCode M)).
  - exact hbottomBounded.
  - exists coverageBound. split; [exact hcoverage |].
    exact (raw_codedZeroAssignment_defined_all M hPA coverageBound).
Qed.

Definition coqRestrictedPAOpenShellAdmissibilitySourceBodyTemplate
    : TemplateFormula :=
  templateFormulaAbstractParameter
    coqRestrictedPASoundnessLowerLevelParameterName
    coqRestrictedPAOpenShellAdmissibilityLawTemplate.

Definition coqRestrictedPAOpenShellAdmissibilitySourceBodyFormula
    : formula :=
  match templateFormulaAsPAFormula
    coqRestrictedPAOpenShellAdmissibilitySourceBodyTemplate with
  | Some output => output
  | None => pBot
  end.

Definition coqRestrictedPAOpenShellAdmissibilitySourceFormula
    : formula :=
  pAll coqRestrictedPAOpenShellAdmissibilitySourceBodyFormula.

Lemma coqRestrictedPAOpenShellAdmissibilitySource_reifies :
  templateFormulaAsPAFormula
    coqRestrictedPAOpenShellAdmissibilitySourceBodyTemplate =
  Some coqRestrictedPAOpenShellAdmissibilitySourceBodyFormula.
Proof. vm_compute. reflexivity. Qed.

Theorem coqRestrictedPAOpenShellAdmissibilitySource_embed :
  embedPAFormula coqRestrictedPAOpenShellAdmissibilitySourceBodyFormula =
  coqRestrictedPAOpenShellAdmissibilitySourceBodyTemplate.
Proof.
  apply templateFormulaAsPAFormula_sound.
  exact coqRestrictedPAOpenShellAdmissibilitySource_reifies.
Qed.

Theorem coqRestrictedPAOpenShellAdmissibilitySource_open :
  templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
    (embedPAFormula
      coqRestrictedPAOpenShellAdmissibilitySourceBodyFormula) =
  coqRestrictedPAOpenShellAdmissibilityLawTemplate.
Proof.
  rewrite coqRestrictedPAOpenShellAdmissibilitySource_embed.
  unfold coqRestrictedPAOpenShellAdmissibilitySourceBodyTemplate.
  apply templateFormulaAbstractParameter_open.
Qed.

Theorem raw_coqRestrictedPAOpenShellAdmissibilitySourceFormula_valid :
    forall (M : RawPAModel), RawPASatisfies M -> forall variables,
  raw_formula_sat M variables
    coqRestrictedPAOpenShellAdmissibilitySourceFormula.
Proof.
  intros M hPA variables.
  unfold coqRestrictedPAOpenShellAdmissibilitySourceFormula.
  cbn [raw_formula_sat]. intro level.
  pose (parameters :=
    (fun _ : TemplateParameterName => raw_zero M)).
  pose (predicates :=
    (fun (_ : TemplatePredicateName) (_ : list M) => True)).
  apply (proj1 (rawTemplateFormulaSat_embedPA M
    (scons M level variables) parameters predicates
    coqRestrictedPAOpenShellAdmissibilitySourceBodyFormula)).
  rewrite coqRestrictedPAOpenShellAdmissibilitySource_embed.
  unfold coqRestrictedPAOpenShellAdmissibilitySourceBodyTemplate.
  apply (proj2 (rawTemplateFormulaSat_abstractParameter M
    variables parameters predicates
    coqRestrictedPASoundnessLowerLevelParameterName level
    coqRestrictedPAOpenShellAdmissibilityLawTemplate)).
  exact (raw_coqRestrictedPAOpenShellAdmissibilityLawTemplate_valid
    M hPA variables
    (fun name =>
      if templateParameterName_eq_dec name
        coqRestrictedPASoundnessLowerLevelParameterName
      then level else parameters name)
    predicates).
Qed.

Theorem PA_proves_coqRestrictedPAOpenShellAdmissibilitySourceFormula :
  Formula.BProv Formula.Ax_s []
    coqRestrictedPAOpenShellAdmissibilitySourceFormula.
Proof.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA
        coqRestrictedPAOpenShellAdmissibilitySourceFormula)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA variables.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact
        (raw_coqRestrictedPAOpenShellAdmissibilitySourceFormula_valid
          M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename Formula.Ax_s []
    coqRestrictedPAOpenShellAdmissibilitySourceFormula
    (fun index => index) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

(** ------------------------------------------------------------------
    Compile each fixed law over a caller-owned witnessed base. *)

Theorem raw_codedPALocalProof_restrictedPAOpenEndpointContextBoundedLaw_on_witnessed_base :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenEndpointContextBoundedLawTemplate)
      root.
Proof.
  intros M hPA inputs baseWitnessList baseContext hbase.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
    M hPA translation
    (rawDirectStructuralTemplatePAAgreement M hPA inputs)
    baseWitnessList baseContext
    coqRestrictedPAOpenEndpointContextBoundedSourceFormula
    hbase PA_proves_coqRestrictedPAOpenEndpointContextBoundedSourceFormula)
    as (prefix & sourceRoot & hextended & hsource).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext).
  assert (hall : RawCodedPALocalProofOf M extendedContext
      (rawFormulaAllCode M
        (rawQuotedFormulaCode M
          coqRestrictedPAOpenEndpointContextBoundedSourceBodyFormula))
      sourceRoot).
  {
    unfold extendedContext, translation in *.
    change (RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      (rawQuotedFormulaCode M
        coqRestrictedPAOpenEndpointContextBoundedSourceFormula)
      sourceRoot).
    rewrite <- (rawTemplateFormula_embedPA
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      coqRestrictedPAOpenEndpointContextBoundedSourceFormula).
    exact hsource.
  }
  pose proof (raw_codedPALocalProofOf_allE M hPA extendedContext
    (rawQuotedFormulaCode M
      coqRestrictedPAOpenEndpointContextBoundedSourceBodyFormula)
    (rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm)
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenEndpointContextBoundedLawTemplate)
    sourceRoot hall
    (rawDirectTemplateFormula_open M hPA inputs
      (embedPAFormula
        coqRestrictedPAOpenEndpointContextBoundedSourceBodyFormula)
      coqRestrictedPASoundnessLowerLevelTerm)) as hopen.
  rewrite coqRestrictedPAOpenEndpointContextBoundedSource_embed in hopen.
  rewrite coqRestrictedPAOpenEndpointContextBoundedSource_open in hopen.
  exists prefix,
    (rawProofAllERoot M extendedContext
      (rawQuotedFormulaCode M
        coqRestrictedPAOpenEndpointContextBoundedSourceBodyFormula)
      (rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm)
      sourceRoot).
  split; [exact hextended | exact hopen].
Qed.

Theorem raw_codedPALocalProof_restrictedPAOpenShellAdmissibilityLaw_on_witnessed_base :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellAdmissibilityLawTemplate)
      root.
Proof.
  intros M hPA inputs baseWitnessList baseContext hbase.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
    M hPA translation
    (rawDirectStructuralTemplatePAAgreement M hPA inputs)
    baseWitnessList baseContext
    coqRestrictedPAOpenShellAdmissibilitySourceFormula
    hbase PA_proves_coqRestrictedPAOpenShellAdmissibilitySourceFormula)
    as (prefix & sourceRoot & hextended & hsource).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext).
  assert (hall : RawCodedPALocalProofOf M extendedContext
      (rawFormulaAllCode M
        (rawQuotedFormulaCode M
          coqRestrictedPAOpenShellAdmissibilitySourceBodyFormula))
      sourceRoot).
  {
    unfold extendedContext, translation in *.
    change (RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      (rawQuotedFormulaCode M
        coqRestrictedPAOpenShellAdmissibilitySourceFormula)
      sourceRoot).
    rewrite <- (rawTemplateFormula_embedPA
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      coqRestrictedPAOpenShellAdmissibilitySourceFormula).
    exact hsource.
  }
  pose proof (raw_codedPALocalProofOf_allE M hPA extendedContext
    (rawQuotedFormulaCode M
      coqRestrictedPAOpenShellAdmissibilitySourceBodyFormula)
    (rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm)
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellAdmissibilityLawTemplate)
    sourceRoot hall
    (rawDirectTemplateFormula_open M hPA inputs
      (embedPAFormula
        coqRestrictedPAOpenShellAdmissibilitySourceBodyFormula)
      coqRestrictedPASoundnessLowerLevelTerm)) as hopen.
  rewrite coqRestrictedPAOpenShellAdmissibilitySource_embed in hopen.
  rewrite coqRestrictedPAOpenShellAdmissibilitySource_open in hopen.
  exists prefix,
    (rawProofAllERoot M extendedContext
      (rawQuotedFormulaCode M
        coqRestrictedPAOpenShellAdmissibilitySourceBodyFormula)
      (rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm)
      sourceRoot).
  split; [exact hextended | exact hopen].
Qed.

Theorem raw_codedPALocalProof_restrictedPAOpenEndpointContextAtomicAdequacyLaw_on_witnessed_base :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenEndpointContextAtomicAdequacyLawTemplate)
      root.
Proof.
  intros M hPA inputs baseWitnessList baseContext hbase.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
    M hPA translation
    (rawDirectStructuralTemplatePAAgreement M hPA inputs)
    baseWitnessList baseContext
    restrictedPAOpenEndpointContextAtomicAdequacyFormula
    hbase PA_proves_restrictedPAOpenEndpointContextAtomicAdequacyFormula)
    as (prefix & root & hextended & hroot).
  exists prefix, root. split; [exact hextended |].
  change (RawCodedPALocalProofOf M
    (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
    (rawTemplateFormula translation
      (embedPAFormula
        restrictedPAOpenEndpointContextAtomicAdequacyFormula)) root).
  exact hroot.
Qed.

(** ------------------------------------------------------------------
    Exact bridge-body transport. *)

Theorem raw_codedPALocalProof_to_restrictedPABridgeBodyDirectContext :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    level numeralCode witnessList baseContext conclusion root,
  RawNumeralTermCodeAt M (raw_succ M level) numeralCode ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M baseContext conclusion root ->
  exists transportedRoot,
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode baseContext)
      conclusion transportedRoot.
Proof.
  intros M hPA inputs level numeralCode witnessList baseContext
    conclusion root hnumeral hwitness hroot.
  destruct (raw_codedPALocalProof_to_restrictedPABridgeContext
    M hPA (raw_succ M level) numeralCode witnessList baseContext
    conclusion root hnumeral hwitness
    (raw_restrictedPAProofFieldsCode_atomically_adequate
      M hPA level numeralCode hnumeral)
    hroot) as [bridgeRoot hbridge].
  exact (raw_coqRestrictedPAOpenShell_prepend_universal
    M hPA inputs numeralCode witnessList baseContext
    conclusion bridgeRoot hwitness hbridge).
Qed.

(** Rebuild a proof below the same five bridge heads after the witnessed PA
    tail grows.  Readiness is lifted head-by-head from the witnessed target;
    no independent adequacy claim about the possibly nonstandard heads is
    needed. *)
Theorem raw_codedPALocalProof_same_restrictedPABridgeBody_witnessedTail_transport :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    numeralCode oldWitnessList oldBase newWitnessList newBase
    conclusion root,
  RawCodedPAAxiomWitnessContext M oldWitnessList oldBase ->
  RawCodedPAAxiomWitnessContext M newWitnessList newBase ->
  RawContextListIncluded M oldBase newBase ->
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
      M inputs numeralCode oldBase)
    conclusion root ->
  exists transportedRoot,
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode newBase)
      conclusion transportedRoot.
Proof.
  intros M hPA inputs numeralCode oldWitnessList oldBase
    newWitnessList newBase conclusion root hold hnew hincluded hroot.
  set (oldShift3 := rawRestrictedPAProofAssumptionIteratedShiftCode
    M numeralCode 3).
  set (oldShift2 := rawRestrictedPAProofAfterWitnessIteratedShiftCode
    M numeralCode 2).
  set (oldShift1 := rawRestrictedPAProofAfterProofIteratedShiftCode
    M numeralCode 1).
  set (fields := rawRestrictedPAProofFieldsCode M numeralCode).
  set (universal :=
    rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs).
  assert (holdReal : RawContextListRealizable M oldBase).
  { exact (raw_codedPAAxiomWitnessContext_context_realizable
      M oldWitnessList oldBase hold). }
  assert (hnewReal : RawContextListRealizable M newBase).
  { exact (raw_codedPAAxiomWitnessContext_context_realizable
      M newWitnessList newBase hnew). }
  assert (hready0 : RawContextBinderReady M oldBase newBase).
  { exact (raw_contextBinderReady_witnessed_target M hPA
      oldBase newBase newWitnessList hincluded hnew). }
  assert (hready1 : RawContextBinderReady M
      (rawListNode M oldShift3 oldBase)
      (rawListNode M oldShift3 newBase)).
  { exact (raw_contextBinderReady_cons M hPA oldBase newBase oldShift3
      holdReal hnewReal hready0). }
  assert (hold1 : RawContextListRealizable M
      (rawListNode M oldShift3 oldBase)).
  { exact (raw_contextList_cons_realizable M hPA oldBase oldShift3 holdReal). }
  assert (hnew1 : RawContextListRealizable M
      (rawListNode M oldShift3 newBase)).
  { exact (raw_contextList_cons_realizable M hPA newBase oldShift3 hnewReal). }
  assert (hready2 : RawContextBinderReady M
      (rawListNode M oldShift2 (rawListNode M oldShift3 oldBase))
      (rawListNode M oldShift2 (rawListNode M oldShift3 newBase))).
  { exact (raw_contextBinderReady_cons M hPA _ _ oldShift2
      hold1 hnew1 hready1). }
  assert (hold2 : RawContextListRealizable M
      (rawListNode M oldShift2 (rawListNode M oldShift3 oldBase))).
  { exact (raw_contextList_cons_realizable M hPA _ oldShift2 hold1). }
  assert (hnew2 : RawContextListRealizable M
      (rawListNode M oldShift2 (rawListNode M oldShift3 newBase))).
  { exact (raw_contextList_cons_realizable M hPA _ oldShift2 hnew1). }
  assert (hready3 : RawContextBinderReady M
      (rawListNode M oldShift1
        (rawListNode M oldShift2 (rawListNode M oldShift3 oldBase)))
      (rawListNode M oldShift1
        (rawListNode M oldShift2 (rawListNode M oldShift3 newBase)))).
  { exact (raw_contextBinderReady_cons M hPA _ _ oldShift1
      hold2 hnew2 hready2). }
  assert (hold3 : RawContextListRealizable M
      (rawListNode M oldShift1
        (rawListNode M oldShift2 (rawListNode M oldShift3 oldBase)))).
  { exact (raw_contextList_cons_realizable M hPA _ oldShift1 hold2). }
  assert (hnew3 : RawContextListRealizable M
      (rawListNode M oldShift1
        (rawListNode M oldShift2 (rawListNode M oldShift3 newBase)))).
  { exact (raw_contextList_cons_realizable M hPA _ oldShift1 hnew2). }
  assert (hready4 : RawContextBinderReady M
      (rawListNode M fields
        (rawListNode M oldShift1
          (rawListNode M oldShift2 (rawListNode M oldShift3 oldBase))))
      (rawListNode M fields
        (rawListNode M oldShift1
          (rawListNode M oldShift2 (rawListNode M oldShift3 newBase))))).
  { exact (raw_contextBinderReady_cons M hPA _ _ fields
      hold3 hnew3 hready3). }
  assert (hold4 : RawContextListRealizable M
      (rawListNode M fields
        (rawListNode M oldShift1
          (rawListNode M oldShift2 (rawListNode M oldShift3 oldBase))))).
  { exact (raw_contextList_cons_realizable M hPA _ fields hold3). }
  assert (hnew4 : RawContextListRealizable M
      (rawListNode M fields
        (rawListNode M oldShift1
          (rawListNode M oldShift2 (rawListNode M oldShift3 newBase))))).
  { exact (raw_contextList_cons_realizable M hPA _ fields hnew3). }
  assert (hready5 : RawContextBinderReady M
      (rawListNode M universal
        (rawListNode M fields
          (rawListNode M oldShift1
            (rawListNode M oldShift2 (rawListNode M oldShift3 oldBase)))))
      (rawListNode M universal
        (rawListNode M fields
          (rawListNode M oldShift1
            (rawListNode M oldShift2 (rawListNode M oldShift3 newBase)))))).
  { exact (raw_contextBinderReady_cons M hPA _ _ universal
      hold4 hnew4 hready4). }
  assert (hincluded5 : RawContextListIncluded M
      (rawListNode M universal
        (rawListNode M fields
          (rawListNode M oldShift1
            (rawListNode M oldShift2 (rawListNode M oldShift3 oldBase)))))
      (rawListNode M universal
        (rawListNode M fields
          (rawListNode M oldShift1
            (rawListNode M oldShift2 (rawListNode M oldShift3 newBase)))))).
  {
    repeat apply (raw_contextListIncluded_cons M hPA);
      try assumption; try reflexivity.
  }
  apply (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
    M hPA
    (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
      M inputs numeralCode oldBase)
    (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
      M inputs numeralCode newBase)
    conclusion root).
  - unfold rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode,
      rawCoqRestrictedPAConsistencyBridgeContextCode,
      rawRestrictedPAFieldsContextCode,
      rawRestrictedPACanonicalShiftedProofContextCode,
      rawRestrictedPAShiftedProofContextCode.
    fold oldShift3 oldShift2 oldShift1 fields universal.
    exact (raw_contextList_cons_realizable M hPA _ universal hold4).
  - unfold rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode,
      rawCoqRestrictedPAConsistencyBridgeContextCode,
      rawRestrictedPAFieldsContextCode,
      rawRestrictedPACanonicalShiftedProofContextCode,
      rawRestrictedPAShiftedProofContextCode.
    fold oldShift3 oldShift2 oldShift1 fields universal.
    exact (raw_contextList_cons_realizable M hPA _ universal hnew4).
  - unfold rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode,
      rawCoqRestrictedPAConsistencyBridgeContextCode,
      rawRestrictedPAFieldsContextCode,
      rawRestrictedPACanonicalShiftedProofContextCode,
      rawRestrictedPAShiftedProofContextCode.
    fold oldShift3 oldShift2 oldShift1 fields universal.
    exact hincluded5.
  - unfold rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode,
      rawCoqRestrictedPAConsistencyBridgeContextCode,
      rawRestrictedPAFieldsContextCode,
      rawRestrictedPACanonicalShiftedProofContextCode,
      rawRestrictedPAShiftedProofContextCode.
    fold oldShift3 oldShift2 oldShift1 fields universal.
    exact hready5.
  - exact hroot.
Qed.

(** ------------------------------------------------------------------
    Premise projection and the two growing arithmetic endpoints. *)

Lemma raw_coqRestrictedPAOpenEndpointOccurrenceTemplate_code : forall
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    numeralCode,
  rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
  rawDirectTemplateFormula inputs
      coqRestrictedPAOpenEndpointOccurrenceTemplate =
  rawRestrictedPAOccurrenceBoundFieldCode M numeralCode.
Proof.
  intros M inputs numeralCode hlevel.
  unfold coqRestrictedPAOpenEndpointOccurrenceTemplate,
    rawRestrictedPAOccurrenceBoundFieldCode,
    rawDirectTemplateFormula, rawDirectTemplateTerm in *.
  rewrite rawStructuralWith_restrictedTargetTemplateFormulaContext.
  now rewrite hlevel.
Qed.

Lemma raw_coqRestrictedPAOpenEndpointAtomicPremise_code : forall
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
      (embedPAFormula (proofAtomicallyAdequateTermAt (tVar 1))) =
  rawRestrictedPAAtomicAdequacyFieldCode M.
Proof.
  intros M inputs.
  unfold rawRestrictedPAAtomicAdequacyFieldCode,
    rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

Lemma raw_coqRestrictedPAOpenFormulaCoveragePremise_code : forall
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
      (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 1))) =
  rawRestrictedPAFormulaCoverageFieldCode M.
Proof.
  intros M inputs.
  unfold rawRestrictedPAFormulaCoverageFieldCode,
    rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

Theorem raw_coqRestrictedPAOpenShell_formula_coverage_premise_root : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    numeralCode witnessList baseContext,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  exists formulaCoverageRoot,
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode baseContext)
      (rawDirectTemplateFormula inputs
        (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 1))))
      formulaCoverageRoot.
Proof.
  intros M hPA inputs numeralCode witnessList baseContext hwitness.
  set (shiftedProofContext :=
    rawRestrictedPACanonicalShiftedProofContextCode
      M baseContext numeralCode).
  assert (hshiftedReal : RawContextListRealizable M shiftedProofContext).
  {
    unfold shiftedProofContext,
      rawRestrictedPACanonicalShiftedProofContextCode,
      rawRestrictedPAShiftedProofContextCode.
    repeat apply (raw_contextList_cons_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable
      M witnessList baseContext hwitness).
  }
  pose proof (raw_restrictedPAFieldProjectionPackage M hPA
    numeralCode shiftedProofContext hshiftedReal) as hprojections.
  destruct hprojections as [_ _ _ _ hformula _ _].
  rewrite <- raw_coqRestrictedPAOpenFormulaCoveragePremise_code
    in hformula.
  destruct (raw_coqRestrictedPAOpenShell_prepend_universal
    M hPA inputs numeralCode witnessList baseContext _ _
    hwitness hformula) as [formulaCoverageRoot hformulaBody].
  exists formulaCoverageRoot. exact hformulaBody.
Qed.

Theorem raw_coqRestrictedPAOpenShell_arithmetic_premise_roots : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    numeralCode witnessList baseContext,
  rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  exists occurrenceRoot atomicRoot endpointRoot,
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode baseContext)
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenEndpointOccurrenceTemplate)
      occurrenceRoot /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode baseContext)
      (rawDirectTemplateFormula inputs
        (embedPAFormula (proofAtomicallyAdequateTermAt (tVar 1))))
      atomicRoot /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode baseContext)
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellEndpointTemplate)
      endpointRoot.
Proof.
  intros M hPA inputs numeralCode witnessList baseContext hlevel hwitness.
  set (shiftedProofContext :=
    rawRestrictedPACanonicalShiftedProofContextCode
      M baseContext numeralCode).
  assert (hshiftedReal : RawContextListRealizable M shiftedProofContext).
  {
    unfold shiftedProofContext,
      rawRestrictedPACanonicalShiftedProofContextCode,
      rawRestrictedPAShiftedProofContextCode.
    repeat apply (raw_contextList_cons_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable
      M witnessList baseContext hwitness).
  }
  pose proof (raw_restrictedPAFieldProjectionPackage M hPA
    numeralCode shiftedProofContext hshiftedReal) as hprojections.
  destruct hprojections as
    [_ _ hoccurrence hatomic _ _ hendpoint].
  rewrite <- (raw_coqRestrictedPAOpenEndpointOccurrenceTemplate_code
    M inputs numeralCode hlevel) in hoccurrence.
  rewrite <- raw_coqRestrictedPAOpenEndpointAtomicPremise_code in hatomic.
  rewrite <- raw_coqRestrictedPAOpenShell_endpoint_code in hendpoint.
  destruct (raw_coqRestrictedPAOpenShell_prepend_universal
    M hPA inputs numeralCode witnessList baseContext _ _
    hwitness hoccurrence) as [occurrenceRoot hoccurrenceBody].
  destruct (raw_coqRestrictedPAOpenShell_prepend_universal
    M hPA inputs numeralCode witnessList baseContext _ _
    hwitness hatomic) as [atomicRoot hatomicBody].
  destruct (raw_coqRestrictedPAOpenShell_prepend_universal
    M hPA inputs numeralCode witnessList baseContext _ _
    hwitness hendpoint) as [endpointRoot hendpointBody].
  exists occurrenceRoot, atomicRoot, endpointRoot.
  exact (conj hoccurrenceBody (conj hatomicBody hendpointBody)).
Qed.

Theorem raw_coqRestrictedPAOpenShell_admissible_growing : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    level numeralCode witnessList baseContext,
  RawNumeralTermCodeAt M (raw_succ M level) numeralCode ->
  rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  exists prefix admissibleRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M prefix witnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode
        (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext))
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellAdmissibleTemplate)
      admissibleRoot.
Proof.
  intros M hPA inputs level numeralCode witnessList baseContext
    hnumeral hlevel hwitness.
  destruct
    (raw_codedPALocalProof_restrictedPAOpenShellAdmissibilityLaw_on_witnessed_base
      M hPA inputs witnessList baseContext hwitness)
    as (prefix & lawRoot & hextended & hlaw).
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M prefix witnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext).
  destruct (raw_codedPALocalProof_to_restrictedPABridgeBodyDirectContext
    M hPA inputs level numeralCode extendedWitnessList extendedContext
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellAdmissibilityLawTemplate)
    lawRoot hnumeral hextended hlaw) as [bodyLawRoot hbodyLaw].
  destruct (raw_coqRestrictedPAOpenShell_arithmetic_premise_roots
    M hPA inputs numeralCode extendedWitnessList extendedContext
    hlevel hextended) as
    (occurrenceRoot & atomicRoot & endpointRoot &
      hoccurrence & hatomic & hendpoint).
  destruct (raw_coqRestrictedPAOpenShell_formula_coverage_premise_root
    M hPA inputs numeralCode extendedWitnessList extendedContext
    hextended) as [formulaCoverageRoot hformulaCoverage].
  unfold coqRestrictedPAOpenShellAdmissibilityLawTemplate in hbodyLaw.
  rewrite !rawDirectTemplateFormula_imp_code in hbodyLaw.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
      M inputs numeralCode extendedContext)
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenEndpointOccurrenceTemplate)
    (rawFormulaImpCode M
      (rawDirectTemplateFormula inputs
        (embedPAFormula (proofAtomicallyAdequateTermAt (tVar 1))))
      (rawFormulaImpCode M
        (rawDirectTemplateFormula inputs
          (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 1))))
        (rawFormulaImpCode M
          (rawDirectTemplateFormula inputs
            coqRestrictedPAOpenShellEndpointTemplate)
          (rawDirectTemplateFormula inputs
            coqRestrictedPAOpenShellAdmissibleTemplate))))
    bodyLawRoot occurrenceRoot hbodyLaw hoccurrence) as hafterOccurrence.
  lazymatch type of hafterOccurrence with
  | RawCodedPALocalProofOf _ _ _ ?afterOccurrenceRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA
        (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
          M inputs numeralCode extendedContext)
        (rawDirectTemplateFormula inputs
          (embedPAFormula (proofAtomicallyAdequateTermAt (tVar 1))))
        (rawFormulaImpCode M
          (rawDirectTemplateFormula inputs
            (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 1))))
          (rawFormulaImpCode M
            (rawDirectTemplateFormula inputs
              coqRestrictedPAOpenShellEndpointTemplate)
            (rawDirectTemplateFormula inputs
              coqRestrictedPAOpenShellAdmissibleTemplate)))
        afterOccurrenceRoot atomicRoot hafterOccurrence hatomic)
        as hafterAtomic
  end.
  lazymatch type of hafterAtomic with
  | RawCodedPALocalProofOf _ _ _ ?afterAtomicRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA
        (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
          M inputs numeralCode extendedContext)
        (rawDirectTemplateFormula inputs
          (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 1))))
        (rawFormulaImpCode M
          (rawDirectTemplateFormula inputs
            coqRestrictedPAOpenShellEndpointTemplate)
          (rawDirectTemplateFormula inputs
            coqRestrictedPAOpenShellAdmissibleTemplate))
        afterAtomicRoot formulaCoverageRoot
        hafterAtomic hformulaCoverage) as hafterCoverage
  end.
  lazymatch type of hafterCoverage with
  | RawCodedPALocalProofOf _ _ _ ?afterCoverageRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA
        (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
          M inputs numeralCode extendedContext)
        (rawDirectTemplateFormula inputs
          coqRestrictedPAOpenShellEndpointTemplate)
        (rawDirectTemplateFormula inputs
          coqRestrictedPAOpenShellAdmissibleTemplate)
        afterCoverageRoot endpointRoot hafterCoverage hendpoint)
        as hadmissible;
      lazymatch type of hadmissible with
      | RawCodedPALocalProofOf _ _ _ ?admissibleRoot =>
          exists prefix, admissibleRoot;
          split; [exact hextended |];
          split;
          [ exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
              M hPA prefix baseContext)
          | unfold extendedContext in hadmissible; exact hadmissible ]
      end
  end.
Qed.

Theorem raw_coqRestrictedPAOpenShell_context_bounded_growing : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    level numeralCode witnessList baseContext,
  RawNumeralTermCodeAt M (raw_succ M level) numeralCode ->
  rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  exists prefix contextBoundedRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M prefix witnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode
        (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext))
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellContextBoundedTemplate)
      contextBoundedRoot.
Proof.
  intros M hPA inputs level numeralCode witnessList baseContext
    hnumeral hlevel hwitness.
  destruct
    (raw_codedPALocalProof_restrictedPAOpenEndpointContextBoundedLaw_on_witnessed_base
      M hPA inputs witnessList baseContext hwitness)
    as (prefix & lawRoot & hextended & hlaw).
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M prefix witnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext).
  destruct (raw_codedPALocalProof_to_restrictedPABridgeBodyDirectContext
    M hPA inputs level numeralCode extendedWitnessList extendedContext
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenEndpointContextBoundedLawTemplate)
    lawRoot hnumeral hextended hlaw) as [bodyLawRoot hbodyLaw].
  destruct (raw_coqRestrictedPAOpenShell_arithmetic_premise_roots
    M hPA inputs numeralCode extendedWitnessList extendedContext
    hlevel hextended) as
    (occurrenceRoot & atomicRoot & endpointRoot &
      hoccurrence & hatomic & hendpoint).
  unfold coqRestrictedPAOpenEndpointContextBoundedLawTemplate in hbodyLaw.
  rewrite !rawDirectTemplateFormula_imp_code in hbodyLaw.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
      M inputs numeralCode extendedContext)
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenEndpointOccurrenceTemplate)
    (rawFormulaImpCode M
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellEndpointTemplate)
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellContextBoundedTemplate))
    bodyLawRoot occurrenceRoot hbodyLaw hoccurrence) as hafterOccurrence.
  lazymatch type of hafterOccurrence with
  | RawCodedPALocalProofOf _ _ _ ?afterOccurrenceRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA
        (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
          M inputs numeralCode extendedContext)
        (rawDirectTemplateFormula inputs
          coqRestrictedPAOpenShellEndpointTemplate)
        (rawDirectTemplateFormula inputs
          coqRestrictedPAOpenShellContextBoundedTemplate)
        afterOccurrenceRoot endpointRoot hafterOccurrence hendpoint)
        as hbounded;
      lazymatch type of hbounded with
      | RawCodedPALocalProofOf _ _ _ ?boundedRoot =>
          exists prefix, boundedRoot;
          split; [exact hextended |];
          split;
          [ exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
              M hPA prefix baseContext)
          | unfold extendedContext in hbounded; exact hbounded ]
      end
  end.
Qed.

Theorem raw_coqRestrictedPAOpenShell_context_adequate_growing : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    level numeralCode witnessList baseContext,
  RawNumeralTermCodeAt M (raw_succ M level) numeralCode ->
  rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  exists prefix contextAdequateRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M prefix witnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode
        (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext))
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellContextAdequateTemplate)
      contextAdequateRoot.
Proof.
  intros M hPA inputs level numeralCode witnessList baseContext
    hnumeral hlevel hwitness.
  destruct
    (raw_codedPALocalProof_restrictedPAOpenEndpointContextAtomicAdequacyLaw_on_witnessed_base
      M hPA inputs witnessList baseContext hwitness)
    as (prefix & lawRoot & hextended & hlaw).
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M prefix witnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext).
  destruct (raw_codedPALocalProof_to_restrictedPABridgeBodyDirectContext
    M hPA inputs level numeralCode extendedWitnessList extendedContext
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenEndpointContextAtomicAdequacyLawTemplate)
    lawRoot hnumeral hextended hlaw) as [bodyLawRoot hbodyLaw].
  destruct (raw_coqRestrictedPAOpenShell_arithmetic_premise_roots
    M hPA inputs numeralCode extendedWitnessList extendedContext
    hlevel hextended) as
    (occurrenceRoot & atomicRoot & endpointRoot &
      hoccurrence & hatomic & hendpoint).
  rewrite coqRestrictedPAOpenEndpointContextAtomicAdequacyLawTemplate_shape,
    !rawDirectTemplateFormula_imp_code in hbodyLaw.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
      M inputs numeralCode extendedContext)
    (rawDirectTemplateFormula inputs
      (embedPAFormula (proofAtomicallyAdequateTermAt (tVar 1))))
    (rawFormulaImpCode M
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellEndpointTemplate)
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellContextAdequateTemplate))
    bodyLawRoot atomicRoot hbodyLaw hatomic) as hafterAtomic.
  lazymatch type of hafterAtomic with
  | RawCodedPALocalProofOf _ _ _ ?afterAtomicRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA
        (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
          M inputs numeralCode extendedContext)
        (rawDirectTemplateFormula inputs
          coqRestrictedPAOpenShellEndpointTemplate)
        (rawDirectTemplateFormula inputs
          coqRestrictedPAOpenShellContextAdequateTemplate)
        afterAtomicRoot endpointRoot hafterAtomic hendpoint)
        as hadequate;
      lazymatch type of hadequate with
      | RawCodedPALocalProofOf _ _ _ ?adequateRoot =>
          exists prefix, adequateRoot;
          split; [exact hextended |];
          split;
          [ exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
              M hPA prefix baseContext)
          | unfold extendedContext in hadequate; exact hadequate ]
      end
  end.
Qed.

(** Synchronize both growing results.  The second theorem grows the base
    chosen by the first; the first root is then transported below the same
    five bridge heads over the final witnessed tail. *)
Theorem raw_coqRestrictedPAOpenShell_context_bounds_and_adequacy_growing :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    level numeralCode witnessList baseContext,
  RawNumeralTermCodeAt M (raw_succ M level) numeralCode ->
  rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  exists boundedPrefix adequatePrefix contextBoundedRoot contextAdequateRoot,
    let boundedWitnessList :=
      rawStandardPAAxiomWitnessPrefixWitnessListCode M
        boundedPrefix witnessList in
    let boundedContext :=
      rawStandardPAAxiomWitnessPrefixContextCode M
        boundedPrefix baseContext in
    let finalWitnessList :=
      rawStandardPAAxiomWitnessPrefixWitnessListCode M
        adequatePrefix boundedWitnessList in
    let finalContext :=
      rawStandardPAAxiomWitnessPrefixContextCode M
        adequatePrefix boundedContext in
    RawCodedPAAxiomWitnessContext M finalWitnessList finalContext /\
    RawContextListIncluded M baseContext finalContext /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode finalContext)
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellContextBoundedTemplate)
      contextBoundedRoot /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode finalContext)
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellContextAdequateTemplate)
      contextAdequateRoot.
Proof.
  intros M hPA inputs level numeralCode witnessList baseContext
    hnumeral hlevel hwitness.
  destruct (raw_coqRestrictedPAOpenShell_context_bounded_growing
    M hPA inputs level numeralCode witnessList baseContext
    hnumeral hlevel hwitness) as
    (boundedPrefix & boundedRoot & hboundedWitness &
      hbaseBoundedIncluded & hbounded).
  set (boundedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      boundedPrefix witnessList).
  set (boundedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      boundedPrefix baseContext).
  destruct (raw_coqRestrictedPAOpenShell_context_adequate_growing
    M hPA inputs level numeralCode boundedWitnessList boundedContext
    hnumeral hlevel hboundedWitness) as
    (adequatePrefix & adequateRoot & hfinalWitness &
      hboundedFinalIncluded & hadequate).
  set (finalWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      adequatePrefix boundedWitnessList).
  set (finalContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      adequatePrefix boundedContext).
  destruct
    (raw_codedPALocalProof_same_restrictedPABridgeBody_witnessedTail_transport
      M hPA inputs numeralCode boundedWitnessList boundedContext
      finalWitnessList finalContext
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellContextBoundedTemplate)
      boundedRoot hboundedWitness hfinalWitness
      hboundedFinalIncluded hbounded)
    as [transportedBoundedRoot htransportedBounded].
  exists boundedPrefix, adequatePrefix,
    transportedBoundedRoot, adequateRoot.
  cbn zeta.
  split; [exact hfinalWitness |].
  split.
  - intros member hmember.
    exact (hboundedFinalIncluded member
      (hbaseBoundedIncluded member hmember)).
  - split; [exact htransportedBounded | exact hadequate].
Qed.

End PABoundedRawCodedRestrictedPAOpenShellArithmeticCarriedCompilation.
