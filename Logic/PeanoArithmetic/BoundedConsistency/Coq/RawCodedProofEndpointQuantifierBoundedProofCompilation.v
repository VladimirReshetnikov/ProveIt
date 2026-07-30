(**
  Represented projection of the hierarchy bound at a proof endpoint.

  A restricted proof stores, at every displayed endpoint, that the endpoint
  formula belongs to the selected Sigma/Pi hierarchy level.  The level may
  be a nonstandard element of an arbitrary PA model, so it must not be
  decoded to a Rocq natural before compiling the projection.

  We instead express the projection as a template law with one named level
  parameter.  Parameter abstraction turns that law into one ordinary PA
  formula with a leading universal quantifier.  Arithmetic completeness
  proves the fixed source once; represented All-E later substitutes the
  direct carrier-valued level term.  Thus the final local proof is an honest
  coded PA derivation, not a semantic truth-to-proof callback.
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
  RawCodedProofAllEConstructor
  RawCodedProofEndpoints
  RawCodedProofRules
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofUniversalElimination
  RawCodedPAAxiomWitness
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedTargetTemplateContext
  RawCodedRestrictedTargetTemplateSemantics
  RawCodedCarrierRestrictedProofReroot
  RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedTemplateSemantics
  RawCodedTemplateParameterAbstraction
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPAAxiomWitnessPrefix.

Import ListNotations.

Module PABoundedRawCodedProofEndpointQuantifierBoundedProofCompilation.

Import PA.
Import PABoundedCodedProof.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofUniversalElimination.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedRestrictedTargetTemplateSemantics.
Import PABoundedRawCodedCarrierRestrictedProofReroot.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateSemantics.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPAAxiomWitnessPrefix.

(** Variables two, one, and zero are respectively the proof root, endpoint
    context, and endpoint conclusion.  The hierarchy level remains a named
    template parameter until the represented universal-elimination step. *)
Definition coqProofEndpointQuantifierBoundedLawTemplate : TemplateFormula :=
  tfImp
    (restrictedTargetTemplateFormulaContext
      coqRestrictedPASoundnessLowerLevelTerm
      (restrictedTargetProofContext (tVar 2)))
    (tfImp
      (embedPAFormula
        (proofEndpointTermAt (tVar 2) (tVar 1) (tVar 0)))
      (restrictedTargetTemplateFormulaContext
        coqRestrictedPASoundnessLowerLevelTerm
        (restrictedTargetFormulaQuantifierBoundedContext (tVar 0)))).

(** Stable views used by proof-code clients.  These hide the large
    restricted-target encodings and expose only the two-premise implication
    interface. *)
Definition coqProofEndpointQuantifierBoundedRestrictedPremise
    : TemplateFormula :=
  templateImpAntecedent coqProofEndpointQuantifierBoundedLawTemplate.

Definition coqProofEndpointQuantifierBoundedEndpointPremise
    : TemplateFormula :=
  templateImpAntecedent
    (templateImpConsequent coqProofEndpointQuantifierBoundedLawTemplate).

Definition coqProofEndpointQuantifierBoundedConclusion
    : TemplateFormula :=
  templateImpConsequent
    (templateImpConsequent coqProofEndpointQuantifierBoundedLawTemplate).

Lemma coqProofEndpointQuantifierBoundedLawTemplate_imp2_shape :
  coqProofEndpointQuantifierBoundedLawTemplate =
  tfImp coqProofEndpointQuantifierBoundedRestrictedPremise
    (tfImp coqProofEndpointQuantifierBoundedEndpointPremise
      coqProofEndpointQuantifierBoundedConclusion).
Proof. reflexivity. Qed.

Lemma coqProofEndpointQuantifierBoundedRestrictedPremise_view :
  coqProofEndpointQuantifierBoundedRestrictedPremise =
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetProofContext (tVar 2)).
Proof. reflexivity. Qed.

Lemma coqProofEndpointQuantifierBoundedEndpointPremise_view :
  coqProofEndpointQuantifierBoundedEndpointPremise =
  embedPAFormula (proofEndpointTermAt (tVar 2) (tVar 1) (tVar 0)).
Proof. reflexivity. Qed.

Lemma coqProofEndpointQuantifierBoundedConclusion_view :
  coqProofEndpointQuantifierBoundedConclusion =
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetFormulaQuantifierBoundedContext (tVar 0)).
Proof. reflexivity. Qed.

(** Semantic statement of the law.  Notice that [level] is an arbitrary
    carrier element and [variables] supplies the tail used to interpret the
    restricted-proof certificate. *)
Theorem raw_coqProofEndpointQuantifierBoundedLawTemplate_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqProofEndpointQuantifierBoundedLawTemplate.
Proof.
  intros M hPA variables parameters predicates.
  unfold coqProofEndpointQuantifierBoundedLawTemplate.
  cbn [rawTemplateFormulaSat].
  unfold coqRestrictedPASoundnessLowerLevelTerm.
  rewrite rawTemplateFormulaSat_restrictedTarget_parameter;
    [|apply restrictedTargetProofContext_seal_free].
  rewrite raw_carrierRestrictedProofContextSat_iff.
  rewrite rawTemplateFormulaSat_embedPA.
  rewrite raw_sat_proofEndpointTermAt_iff.
  rewrite rawTemplateFormulaSat_restrictedTarget_parameter;
    [|apply restrictedTargetFormulaQuantifierBoundedContext_seal_free].
  rewrite raw_restrictedTargetFormulaQuantifierBoundedContextSat_iff.
  cbn [raw_term_eval].
  intros hrestricted hendpoint.
  exact (raw_carrierRestrictedProof_endpoint_formula_bounded M hPA
    variables
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 2) hrestricted
    (variables 1) (variables 0) hendpoint).
Qed.

(** Abstract precisely the named level parameter.  Existing de Bruijn
    variables are shifted by the abstraction operation, so opening the body
    at the same named parameter recovers the law definitionally. *)
Definition coqProofEndpointQuantifierBoundedSourceBodyTemplate
    : TemplateFormula :=
  templateFormulaAbstractParameter
    coqRestrictedPASoundnessLowerLevelParameterName
    coqProofEndpointQuantifierBoundedLawTemplate.

Definition coqProofEndpointQuantifierBoundedSourceBodyFormula : formula :=
  match templateFormulaAsPAFormula
    coqProofEndpointQuantifierBoundedSourceBodyTemplate with
  | Some output => output
  | None => pBot
  end.

Definition coqProofEndpointQuantifierBoundedSourceFormula : formula :=
  pAll coqProofEndpointQuantifierBoundedSourceBodyFormula.

Lemma coqProofEndpointQuantifierBoundedSource_reifies :
  templateFormulaAsPAFormula
    coqProofEndpointQuantifierBoundedSourceBodyTemplate =
  Some coqProofEndpointQuantifierBoundedSourceBodyFormula.
Proof. vm_compute. reflexivity. Qed.

Theorem coqProofEndpointQuantifierBoundedSource_embed :
  embedPAFormula coqProofEndpointQuantifierBoundedSourceBodyFormula =
  coqProofEndpointQuantifierBoundedSourceBodyTemplate.
Proof.
  apply templateFormulaAsPAFormula_sound.
  exact coqProofEndpointQuantifierBoundedSource_reifies.
Qed.

Theorem coqProofEndpointQuantifierBoundedSource_open :
  templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
    (embedPAFormula coqProofEndpointQuantifierBoundedSourceBodyFormula) =
  coqProofEndpointQuantifierBoundedLawTemplate.
Proof.
  rewrite coqProofEndpointQuantifierBoundedSource_embed.
  apply templateFormulaAbstractParameter_open.
Qed.

(** The universally quantified ordinary source is valid in every raw PA
    model, including at nonstandard values of its leading binder. *)
Theorem raw_coqProofEndpointQuantifierBoundedSourceFormula_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall variables,
  raw_formula_sat M variables
    coqProofEndpointQuantifierBoundedSourceFormula.
Proof.
  intros M hPA variables.
  unfold coqProofEndpointQuantifierBoundedSourceFormula.
  cbn [raw_formula_sat]. intro level.
  pose (parameters :=
    (fun _ : TemplateParameterName => raw_zero M)).
  pose (predicates :=
    (fun (_ : TemplatePredicateName) (_ : list M) => True)).
  apply (proj1 (rawTemplateFormulaSat_embedPA M
    (scons M level variables) parameters predicates
    coqProofEndpointQuantifierBoundedSourceBodyFormula)).
  rewrite coqProofEndpointQuantifierBoundedSource_embed.
  unfold coqProofEndpointQuantifierBoundedSourceBodyTemplate.
  apply (proj2 (rawTemplateFormulaSat_abstractParameter M
    variables parameters predicates
    coqRestrictedPASoundnessLowerLevelParameterName level
    coqProofEndpointQuantifierBoundedLawTemplate)).
  apply raw_coqProofEndpointQuantifierBoundedLawTemplate_valid.
  exact hPA.
Qed.

(** Completeness is used only for this fixed standard arithmetic source.
    Sealing and reopening permits the source to retain its three endpoint
    variables while producing an empty-context PA derivation. *)
Theorem PA_proves_coqProofEndpointQuantifierBoundedSourceFormula :
  Formula.BProv Formula.Ax_s []
    coqProofEndpointQuantifierBoundedSourceFormula.
Proof.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA coqProofEndpointQuantifierBoundedSourceFormula)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA variables.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact (raw_coqProofEndpointQuantifierBoundedSourceFormula_valid
        M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename Formula.Ax_s []
    coqProofEndpointQuantifierBoundedSourceFormula
    (fun index => index) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

(** Direct structural translation agrees with quotation on the abstracted
    PA source body. *)
Lemma rawDirect_proofEndpointQuantifierBoundedSourceBody_agreement : forall
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
    (embedPAFormula coqProofEndpointQuantifierBoundedSourceBodyFormula) =
  rawQuotedFormulaCode M
    coqProofEndpointQuantifierBoundedSourceBodyFormula.
Proof.
  intros M inputs.
  unfold rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

(** Exact represented substitution trace used by the generic universal
    source compiler.  Its target is the direct raw code of the original
    parameterized endpoint law. *)
Theorem rawDirect_proofEndpointQuantifierBoundedSource_substitution : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedFormulaSingleSubstitution M
    (rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm)
    (rawQuotedFormulaCode M
      coqProofEndpointQuantifierBoundedSourceBodyFormula)
    (rawDirectTemplateFormula inputs
      coqProofEndpointQuantifierBoundedLawTemplate).
Proof.
  intros M hPA inputs.
  pose proof (rawDirectTemplateFormula_open M hPA inputs
    (embedPAFormula coqProofEndpointQuantifierBoundedSourceBodyFormula)
    coqRestrictedPASoundnessLowerLevelTerm) as hopen.
  rewrite rawDirect_proofEndpointQuantifierBoundedSourceBody_agreement
    in hopen.
  rewrite coqProofEndpointQuantifierBoundedSource_open in hopen.
  exact hopen.
Qed.

(** Compile the parameterized implication over any witnessed caller base.
    The returned standard axiom prefix is the finite support of the fixed PA
    derivation; no hypothesis requires that the carrier level be standard. *)
Theorem raw_codedPALocalProof_proofEndpointQuantifierBoundedLaw_on_witnessed_base :
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
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawDirectTemplateFormula inputs
        coqProofEndpointQuantifierBoundedLawTemplate)
      root.
Proof.
  intros M hPA inputs baseWitnessList baseContext hbase.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
    M hPA translation
    (rawDirectStructuralTemplatePAAgreement M hPA inputs)
    baseWitnessList baseContext
    coqProofEndpointQuantifierBoundedSourceFormula
    hbase PA_proves_coqProofEndpointQuantifierBoundedSourceFormula)
    as (witnesses & sourceRoot & hextended & hsource).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext).
  assert (hall : RawCodedPALocalProofOf M extendedContext
      (rawFormulaAllCode M
        (rawQuotedFormulaCode M
          coqProofEndpointQuantifierBoundedSourceBodyFormula))
      sourceRoot).
  {
    unfold extendedContext, translation in *.
    change (RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawQuotedFormulaCode M
        coqProofEndpointQuantifierBoundedSourceFormula)
      sourceRoot).
    rewrite <- (rawTemplateFormula_embedPA
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      coqProofEndpointQuantifierBoundedSourceFormula).
    exact hsource.
  }
  pose proof (raw_codedPALocalProofOf_allE M hPA extendedContext
    (rawQuotedFormulaCode M
      coqProofEndpointQuantifierBoundedSourceBodyFormula)
    (rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm)
    (rawDirectTemplateFormula inputs
      coqProofEndpointQuantifierBoundedLawTemplate)
    sourceRoot hall
    (rawDirect_proofEndpointQuantifierBoundedSource_substitution
      M hPA inputs)) as hinstance.
  exists witnesses,
    (rawProofAllERoot M extendedContext
      (rawQuotedFormulaCode M
        coqProofEndpointQuantifierBoundedSourceBodyFormula)
      (rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm)
      sourceRoot).
  split; [exact hextended | exact hinstance].
Qed.

(** Apply the represented law to caller-owned roots.  Compilation of the
    fixed PA source may extend the witnessed base by a finite standard axiom
    prefix.  Both incoming roots are transported to that exact context before
    the two checked implication-elimination nodes are assembled. *)
Theorem
    raw_codedPALocalProof_proofEndpointQuantifierBounded_of_roots_on_witnessed_extension :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext restrictedRoot endpointRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqProofEndpointQuantifierBoundedRestrictedPremise)
    restrictedRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqProofEndpointQuantifierBoundedEndpointPremise)
    endpointRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) resultRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawDirectTemplateFormula inputs
        coqProofEndpointQuantifierBoundedConclusion)
      resultRoot.
Proof.
  intros M hPA inputs baseWitnessList baseContext
    restrictedRoot endpointRoot hbase hrestricted hendpoint.
  destruct
    (raw_codedPALocalProof_proofEndpointQuantifierBoundedLaw_on_witnessed_base
      M hPA inputs baseWitnessList baseContext hbase)
    as (witnesses & implicationRoot & hextended & himplication).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses baseWitnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  assert (hincluded : RawContextListIncluded M baseContext extendedContext).
  {
    unfold extendedContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA witnesses baseContext).
  }
  assert (hrestrictedOnEmptyPrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext [])
      (rawDirectTemplateFormula inputs
        coqProofEndpointQuantifierBoundedRestrictedPremise)
      restrictedRoot).
  {
    cbn [rawTemplateContextCodeOnTail]. exact hrestricted.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext []
      (rawDirectTemplateFormula inputs
        coqProofEndpointQuantifierBoundedRestrictedPremise)
      restrictedRoot hbase hextended hincluded
      hrestrictedOnEmptyPrefix)
    as [transportedRestrictedRoot htransportedRestricted].
  cbn [rawTemplateContextCodeOnTail] in htransportedRestricted.
  assert (hendpointOnEmptyPrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext [])
      (rawDirectTemplateFormula inputs
        coqProofEndpointQuantifierBoundedEndpointPremise)
      endpointRoot).
  {
    cbn [rawTemplateContextCodeOnTail]. exact hendpoint.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext []
      (rawDirectTemplateFormula inputs
        coqProofEndpointQuantifierBoundedEndpointPremise)
      endpointRoot hbase hextended hincluded hendpointOnEmptyPrefix)
    as [transportedEndpointRoot htransportedEndpoint].
  cbn [rawTemplateContextCodeOnTail] in htransportedEndpoint.
  change (RawCodedPALocalProofOf M extendedContext
    (rawTemplateFormula translation
      coqProofEndpointQuantifierBoundedLawTemplate)
    implicationRoot) in himplication.
  rewrite coqProofEndpointQuantifierBoundedLawTemplate_imp2_shape
    in himplication.
  rewrite !rawTemplateFormula_imp in himplication.
  pose proof (raw_codedPALocalProofOf_impE M hPA extendedContext
    (rawDirectTemplateFormula inputs
      coqProofEndpointQuantifierBoundedRestrictedPremise)
    (rawFormulaImpCode M
      (rawDirectTemplateFormula inputs
        coqProofEndpointQuantifierBoundedEndpointPremise)
      (rawDirectTemplateFormula inputs
        coqProofEndpointQuantifierBoundedConclusion))
    implicationRoot transportedRestrictedRoot
    himplication htransportedRestricted) as hafterRestricted.
  lazymatch type of hafterRestricted with
  | RawCodedPALocalProofOf _ _ _ ?afterRestrictedRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA extendedContext
        (rawDirectTemplateFormula inputs
          coqProofEndpointQuantifierBoundedEndpointPremise)
        (rawDirectTemplateFormula inputs
          coqProofEndpointQuantifierBoundedConclusion)
        afterRestrictedRoot transportedEndpointRoot
        hafterRestricted htransportedEndpoint) as hresult;
      lazymatch type of hresult with
      | RawCodedPALocalProofOf _ _ _ ?resultRoot =>
          exists witnesses, resultRoot;
          split; [exact hextended |];
          split; [exact hincluded | exact hresult]
      end
  end.
Qed.

(** ------------------------------------------------------------------
    Strong-step specialization.

    Four endpoint witnesses have already been introduced in the direct
    soundness shell.  Consequently the proof, context, and conclusion are
    variables four, three, and two.  Defining this fixed specialization
    directly is important: filling the restricted-target level hole with a
    free PA term would be captured beneath its internal binders, while
    closing and reopening all endpoint variables causes prohibitively large
    proof-term normalization.  Only the named level parameter is abstracted
    here, exactly as in the smaller three-variable interface above. *)

Definition coqStrongStepProofEndpointQuantifierBoundedLawTemplate
    : TemplateFormula :=
  tfImp
    (restrictedTargetTemplateFormulaContext
      coqRestrictedPASoundnessLowerLevelTerm
      (restrictedTargetProofContext (tVar 4)))
    (tfImp
      (embedPAFormula
        (proofRuleValidTermAt (tVar 4) (tVar 3) (tVar 2)))
      (restrictedTargetTemplateFormulaContext
        coqRestrictedPASoundnessLowerLevelTerm
        (restrictedTargetFormulaQuantifierBoundedContext (tVar 2)))).

Definition coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise
    : TemplateFormula :=
  templateImpAntecedent
    coqStrongStepProofEndpointQuantifierBoundedLawTemplate.

Definition coqStrongStepProofEndpointQuantifierBoundedEndpointPremise
    : TemplateFormula :=
  templateImpAntecedent
    (templateImpConsequent
      coqStrongStepProofEndpointQuantifierBoundedLawTemplate).

Definition coqStrongStepProofEndpointQuantifierBoundedConclusion
    : TemplateFormula :=
  templateImpConsequent
    (templateImpConsequent
      coqStrongStepProofEndpointQuantifierBoundedLawTemplate).

Lemma coqStrongStepProofEndpointQuantifierBoundedLawTemplate_imp2_shape :
  coqStrongStepProofEndpointQuantifierBoundedLawTemplate =
  tfImp coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise
    (tfImp coqStrongStepProofEndpointQuantifierBoundedEndpointPremise
      coqStrongStepProofEndpointQuantifierBoundedConclusion).
Proof. reflexivity. Qed.

Lemma coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise_view :
  coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise =
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetProofContext (tVar 4)).
Proof. reflexivity. Qed.

Lemma coqStrongStepProofEndpointQuantifierBoundedEndpointPremise_view :
  coqStrongStepProofEndpointQuantifierBoundedEndpointPremise =
  embedPAFormula (proofRuleValidTermAt (tVar 4) (tVar 3) (tVar 2)).
Proof. reflexivity. Qed.

(** Rule validity carries the same eight displayed fields as the endpoint
    relation and merely adds constructor-local side conditions.  Forgetting
    those side conditions therefore yields the endpoint fact needed by the
    carrier restricted-proof theorem. *)
Lemma raw_proofRuleValid_endpoint : forall (M : RawPAModel)
    code context conclusion,
  RawProofRuleValid M code context conclusion ->
  RawProofEndpoint M code context conclusion.
Proof.
  intros M code context conclusion
    (rowContext & a & b & c & t & child1 & child2 & child3 &
      hcontext & hrule).
  exists rowContext, a, b, c, t, child1, child2, child3.
  split; [exact hcontext |].
  unfold RawProofRuleValidCases in hrule.
  unfold RawProofEndpointCases.
  tauto.
Qed.

Lemma coqStrongStepProofEndpointQuantifierBoundedConclusion_view :
  coqStrongStepProofEndpointQuantifierBoundedConclusion =
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetFormulaQuantifierBoundedContext (tVar 2)).
Proof. reflexivity. Qed.

Theorem raw_coqStrongStepProofEndpointQuantifierBoundedLawTemplate_valid :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    variables parameters predicates,
  rawTemplateFormulaSat M variables parameters predicates
    coqStrongStepProofEndpointQuantifierBoundedLawTemplate.
Proof.
  intros M hPA variables parameters predicates.
  unfold coqStrongStepProofEndpointQuantifierBoundedLawTemplate.
  cbn [rawTemplateFormulaSat].
  unfold coqRestrictedPASoundnessLowerLevelTerm.
  rewrite rawTemplateFormulaSat_restrictedTarget_parameter;
    [|apply restrictedTargetProofContext_seal_free].
  rewrite raw_carrierRestrictedProofContextSat_iff.
  rewrite rawTemplateFormulaSat_embedPA.
  rewrite raw_sat_proofRuleValidTermAt_iff.
  rewrite rawTemplateFormulaSat_restrictedTarget_parameter;
    [|apply restrictedTargetFormulaQuantifierBoundedContext_seal_free].
  rewrite raw_restrictedTargetFormulaQuantifierBoundedContextSat_iff.
  cbn [raw_term_eval].
  intros hrestricted hrule.
  exact (raw_carrierRestrictedProof_endpoint_formula_bounded M hPA
    variables
    (parameters coqRestrictedPASoundnessLowerLevelParameterName)
    (variables 4) hrestricted
    (variables 3) (variables 2)
    (raw_proofRuleValid_endpoint M (variables 4)
      (variables 3) (variables 2) hrule)).
Qed.

Definition coqStrongStepProofEndpointQuantifierBoundedSourceBodyTemplate
    : TemplateFormula :=
  templateFormulaAbstractParameter
    coqRestrictedPASoundnessLowerLevelParameterName
    coqStrongStepProofEndpointQuantifierBoundedLawTemplate.

Definition coqStrongStepProofEndpointQuantifierBoundedSourceBodyFormula
    : formula :=
  match templateFormulaAsPAFormula
    coqStrongStepProofEndpointQuantifierBoundedSourceBodyTemplate with
  | Some output => output
  | None => pBot
  end.

Definition coqStrongStepProofEndpointQuantifierBoundedSourceFormula
    : formula :=
  pAll coqStrongStepProofEndpointQuantifierBoundedSourceBodyFormula.

Lemma coqStrongStepProofEndpointQuantifierBoundedSource_reifies :
  templateFormulaAsPAFormula
    coqStrongStepProofEndpointQuantifierBoundedSourceBodyTemplate =
  Some coqStrongStepProofEndpointQuantifierBoundedSourceBodyFormula.
Proof. vm_compute. reflexivity. Qed.

Theorem coqStrongStepProofEndpointQuantifierBoundedSource_embed :
  embedPAFormula
    coqStrongStepProofEndpointQuantifierBoundedSourceBodyFormula =
  coqStrongStepProofEndpointQuantifierBoundedSourceBodyTemplate.
Proof.
  apply templateFormulaAsPAFormula_sound.
  exact coqStrongStepProofEndpointQuantifierBoundedSource_reifies.
Qed.

Theorem coqStrongStepProofEndpointQuantifierBoundedSource_open :
  templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
    (embedPAFormula
      coqStrongStepProofEndpointQuantifierBoundedSourceBodyFormula) =
  coqStrongStepProofEndpointQuantifierBoundedLawTemplate.
Proof.
  rewrite coqStrongStepProofEndpointQuantifierBoundedSource_embed.
  apply templateFormulaAbstractParameter_open.
Qed.

Theorem raw_coqStrongStepProofEndpointQuantifierBoundedSourceFormula_valid :
  forall (M : RawPAModel), RawPASatisfies M -> forall variables,
  raw_formula_sat M variables
    coqStrongStepProofEndpointQuantifierBoundedSourceFormula.
Proof.
  intros M hPA variables.
  unfold coqStrongStepProofEndpointQuantifierBoundedSourceFormula.
  cbn [raw_formula_sat]. intro level.
  pose (parameters :=
    (fun _ : TemplateParameterName => raw_zero M)).
  pose (predicates :=
    (fun (_ : TemplatePredicateName) (_ : list M) => True)).
  apply (proj1 (rawTemplateFormulaSat_embedPA M
    (scons M level variables) parameters predicates
    coqStrongStepProofEndpointQuantifierBoundedSourceBodyFormula)).
  rewrite coqStrongStepProofEndpointQuantifierBoundedSource_embed.
  unfold coqStrongStepProofEndpointQuantifierBoundedSourceBodyTemplate.
  apply (proj2 (rawTemplateFormulaSat_abstractParameter M
    variables parameters predicates
    coqRestrictedPASoundnessLowerLevelParameterName level
    coqStrongStepProofEndpointQuantifierBoundedLawTemplate)).
  apply raw_coqStrongStepProofEndpointQuantifierBoundedLawTemplate_valid.
  exact hPA.
Qed.

Theorem PA_proves_coqStrongStepProofEndpointQuantifierBoundedSourceFormula :
  Formula.BProv Formula.Ax_s []
    coqStrongStepProofEndpointQuantifierBoundedSourceFormula.
Proof.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA
        coqStrongStepProofEndpointQuantifierBoundedSourceFormula)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA variables.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact
        (raw_coqStrongStepProofEndpointQuantifierBoundedSourceFormula_valid
          M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename Formula.Ax_s []
    coqStrongStepProofEndpointQuantifierBoundedSourceFormula
    (fun index => index) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

End PABoundedRawCodedProofEndpointQuantifierBoundedProofCompilation.
