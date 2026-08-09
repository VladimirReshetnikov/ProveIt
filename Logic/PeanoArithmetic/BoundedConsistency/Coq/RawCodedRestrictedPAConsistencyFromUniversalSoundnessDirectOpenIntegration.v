(**
  Connect the direct finite open shell to the literal candidate context.

  The shell module isolates the nine formulas used by the final
  consistency argument, but its generic application theorem deliberately
  accepts all nine represented roots at once.  Here we construct the six
  roots which are already forced by the bridge context:

  - the universal soundness assumption;
  - the two selected truth-coherence laws;
  - the full restricted-proof premise assembled from four checker fields;
  - the bottom endpoint; and
  - the witnessed PA-axiom context.

  Only three genuinely arithmetic conclusions remain: admissibility of
  bottom at the zero assignment, boundedness of the exposed endpoint
  context, and atomic adequacy of that context.  They are recorded as one
  sharp residual package below.

  The proof applies universal elimination and implication elimination
  directly in the caller's context.  Consequently it does not require the
  stronger atomic-adequacy side condition used when the closed shell theorem
  is weakened from the empty context.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedFormulaOperations
  RawCodedProofAtomicAdequacy
  RawCodedProofFormulaCoverage
  RawCodedProofRuleCoverage
  RawCodedProofRules
  RawCodedRestrictedPAProof
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofAndIntroduction
  RawCodedPALocalProofAdjoinedContextTransport
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedPAConsistencyShiftOrbit
  RawCodedRestrictedPAProjectedFieldRefutation
  RawCodedRestrictedPAFieldProjections
  RawCodedRestrictedTargetTemplateContext
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenShell.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenIntegration.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofFormulaCoverage.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPALocalProofAdjoinedContextTransport.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedPAConsistencyShiftOrbit.
Import PABoundedRawCodedRestrictedPAProjectedFieldRefutation.
Import PABoundedRawCodedRestrictedPAFieldProjections.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenShell.

(** Exact finite openings used by the same-context logical composition. *)
Lemma coqRestrictedPAOpenShell_soundness_open_many :
  templateUniversalOpenMany
    coqRestrictedPADerivationSoundnessUniversalTemplate
    coqRestrictedPAOpenShellSoundnessReplacements =
  Some coqRestrictedPAOpenShellSoundnessInstanceTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPAOpenShell_context_truth_open_many :
  templateUniversalOpenMany
    coqRestrictedPAAxiomContextsTruthTemplate
    coqRestrictedPAOpenShellContextTruthReplacements =
  Some coqRestrictedPAOpenShellContextTruthLawInstanceTemplate.
Proof. vm_compute. reflexivity. Qed.

(** Universal soundness has no free de Bruijn variable.  Named parameters
    and opaque predicate names are unaffected by [templateFormulaRename], so
    its represented unit shift is literally a self-shift. *)
Lemma coqRestrictedPAOpenShell_universal_shift_identity :
  templateFormulaRename S
    coqRestrictedPADerivationSoundnessUniversalTemplate =
  coqRestrictedPADerivationSoundnessUniversalTemplate.
Proof. vm_compute. reflexivity. Qed.

(** Stable checker-field view of the instantiated restricted-proof premise. *)
Lemma coqRestrictedPAOpenShell_restricted_proof_shape :
  coqRestrictedPAOpenShellRestrictedProofTemplate =
  tfAnd
    (restrictedTargetTemplateFormulaContext
      coqRestrictedPASoundnessLowerLevelTerm
      (restrictedTargetProofContext (tVar 1)))
    (tfAnd
      (embedPAFormula (proofAtomicallyAdequateTermAt (tVar 1)))
      (tfAnd
        (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 1)))
        (embedPAFormula (proofRuleCoverageTermAt (tVar 1))))).
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPAOpenShell_endpoint_field_shape :
  coqRestrictedPAOpenShellEndpointTemplate =
  embedPAFormula
    (proofRuleValidTermAt
      (tVar 1) (tVar 0) rawFormulaBotCodeTerm).
Proof. vm_compute. reflexivity. Qed.

(** Small direct-translation equations used to identify the projected raw
    checker fields.  Keeping them polymorphic avoids normalizing the large
    instantiated soundness formula. *)
Lemma rawDirectTemplateFormula_and_code : forall
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    left right,
  rawDirectTemplateFormula inputs (tfAnd left right) =
  rawFormulaAndCode M
    (rawDirectTemplateFormula inputs left)
    (rawDirectTemplateFormula inputs right).
Proof. reflexivity. Qed.

Lemma rawDirectTemplateFormula_embedPA_code : forall
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    formula,
  rawDirectTemplateFormula inputs (embedPAFormula formula) =
  rawQuotedFormulaCode M formula.
Proof.
  intros M inputs formula.
  unfold rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

Lemma raw_coqRestrictedPAOpenShell_restricted_proof_code : forall
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    numeralCode,
  rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
  rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellRestrictedProofTemplate =
  rawFormulaAndCode M
    (rawRestrictedPAOccurrenceBoundFieldCode M numeralCode)
    (rawFormulaAndCode M
      (rawRestrictedPAAtomicAdequacyFieldCode M)
      (rawFormulaAndCode M
        (rawRestrictedPAFormulaCoverageFieldCode M)
        (rawRestrictedPARuleCoverageFieldCode M))).
Proof.
  intros M inputs numeralCode hlevel.
  rewrite coqRestrictedPAOpenShell_restricted_proof_shape,
    !rawDirectTemplateFormula_and_code.
  unfold rawDirectTemplateFormula at 1.
  rewrite rawStructuralWith_restrictedTargetTemplateFormulaContext.
  fold (rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm).
  rewrite hlevel.
  unfold rawRestrictedPAOccurrenceBoundFieldCode,
    rawRestrictedPAAtomicAdequacyFieldCode,
    rawRestrictedPAFormulaCoverageFieldCode,
    rawRestrictedPARuleCoverageFieldCode.
  rewrite !rawDirectTemplateFormula_embedPA_code.
  reflexivity.
Qed.

Lemma raw_coqRestrictedPAOpenShell_endpoint_code : forall
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellEndpointTemplate =
  rawRestrictedPABottomEndpointFieldCode M.
Proof.
  intros M inputs.
  rewrite coqRestrictedPAOpenShell_endpoint_field_shape,
    rawDirectTemplateFormula_embedPA_code.
  reflexivity.
Qed.

Lemma raw_coqRestrictedPAOpenShell_witnessed_context_code : forall
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellWitnessedContextTemplate =
  rawRestrictedPAAxiomContextFieldCode M.
Proof.
  intros M inputs.
  unfold coqRestrictedPAOpenShellWitnessedContextTemplate,
    rawRestrictedPAAxiomContextFieldCode.
  apply rawDirectTemplateFormula_embedPA_code.
Qed.

(** The residual contains no truth principle and no already projected
    checker field.  These are precisely the three arithmetic local roots
    not obtained by propositional assembly from the seven-field head. *)
Definition RawCoqRestrictedPAOpenShellArithmeticResidual
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    (context admissibleRoot contextBoundedRoot contextAdequateRoot : M)
    : Prop :=
  RawCodedPALocalProofOf M context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellAdmissibleTemplate)
    admissibleRoot /\
  RawCodedPALocalProofOf M context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellContextBoundedTemplate)
    contextBoundedRoot /\
  RawCodedPALocalProofOf M context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellContextAdequateTemplate)
    contextAdequateRoot.

Arguments RawCoqRestrictedPAOpenShellArithmeticResidual
  M inputs context admissibleRoot contextBoundedRoot contextAdequateRoot
  : clear implicits.

(** The canonical proof-field tail is a literal three-head extension of the
    witnessed base.  Its realizability therefore needs no formula-shift
    functionality or numeral-code hypothesis. *)
Lemma raw_coqRestrictedPAConsistencyBridgeContext_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    witnessList baseContext numeralCode,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawContextListRealizable M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext).
Proof.
  intros M hPA witnessList baseContext numeralCode hwitness.
  unfold rawCoqRestrictedPAConsistencyBridgeContextCode,
    rawRestrictedPAFieldsContextCode,
    rawRestrictedPACanonicalShiftedProofContextCode,
    rawRestrictedPAShiftedProofContextCode.
  repeat apply (raw_contextList_cons_realizable M hPA).
  exact (raw_codedPAAxiomWitnessContext_context_realizable
    M witnessList baseContext hwitness).
Qed.

(** Four conjunction projections are reassembled into the exact restricted
    premise.  Endpoint and witnessed-context roots are the corresponding
    direct projections.  This consumes no arithmetic theorem. *)
Theorem raw_coqRestrictedPAOpenShell_projected_roots : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    numeralCode witnessList baseContext,
  rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  exists restrictedProofRoot endpointRoot witnessedContextRoot : M,
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode baseContext)
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellRestrictedProofTemplate)
      restrictedProofRoot /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode baseContext)
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellEndpointTemplate)
      endpointRoot /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode baseContext)
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellWitnessedContextTemplate)
      witnessedContextRoot.
Proof.
  intros M hPA inputs numeralCode witnessList baseContext hlevel hwitness.
  set (shiftedProofContext :=
    rawRestrictedPACanonicalShiftedProofContextCode
      M baseContext numeralCode).
  assert (hshiftedProofRealizable :
      RawContextListRealizable M shiftedProofContext).
  {
    unfold shiftedProofContext,
      rawRestrictedPACanonicalShiftedProofContextCode,
      rawRestrictedPAShiftedProofContextCode.
    repeat apply (raw_contextList_cons_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable
      M witnessList baseContext hwitness).
  }
  pose proof (raw_restrictedPAFieldProjectionPackage M hPA
    numeralCode shiftedProofContext hshiftedProofRealizable) as hprojections.
  destruct hprojections as
    [hcertificate haxiom hoccurrence hatomic hformula hrule hendpoint].
  pose proof (raw_codedPALocalProofOf_andI M hPA
    (rawRestrictedPAFieldsContextCode M numeralCode shiftedProofContext)
    (rawRestrictedPAFormulaCoverageFieldCode M)
    (rawRestrictedPARuleCoverageFieldCode M)
    (rawRestrictedPAFormulaCoverageProjectionRoot
      M numeralCode shiftedProofContext)
    (rawRestrictedPARuleCoverageProjectionRoot
      M numeralCode shiftedProofContext)
    hformula hrule) as hformulaAndRule.
  lazymatch type of hformulaAndRule with
  | RawCodedPALocalProofOf _ _ _ ?formulaAndRuleRoot =>
      pose proof (raw_codedPALocalProofOf_andI M hPA
        (rawRestrictedPAFieldsContextCode M numeralCode shiftedProofContext)
        (rawRestrictedPAAtomicAdequacyFieldCode M)
        (rawFormulaAndCode M
          (rawRestrictedPAFormulaCoverageFieldCode M)
          (rawRestrictedPARuleCoverageFieldCode M))
        (rawRestrictedPAAtomicAdequacyProjectionRoot
          M numeralCode shiftedProofContext)
        formulaAndRuleRoot hatomic hformulaAndRule) as hatomicAndRest
  end.
  lazymatch type of hatomicAndRest with
  | RawCodedPALocalProofOf _ _ _ ?atomicAndRestRoot =>
      pose proof (raw_codedPALocalProofOf_andI M hPA
        (rawRestrictedPAFieldsContextCode M numeralCode shiftedProofContext)
        (rawRestrictedPAOccurrenceBoundFieldCode M numeralCode)
        (rawFormulaAndCode M
          (rawRestrictedPAAtomicAdequacyFieldCode M)
          (rawFormulaAndCode M
            (rawRestrictedPAFormulaCoverageFieldCode M)
            (rawRestrictedPARuleCoverageFieldCode M)))
        (rawRestrictedPAOccurrenceBoundProjectionRoot
          M numeralCode shiftedProofContext)
        atomicAndRestRoot hoccurrence hatomicAndRest) as hrestricted
  end.
  rewrite <- (raw_coqRestrictedPAOpenShell_restricted_proof_code
    M inputs numeralCode hlevel) in hrestricted.
  rewrite <- raw_coqRestrictedPAOpenShell_endpoint_code in hendpoint.
  rewrite <- raw_coqRestrictedPAOpenShell_witnessed_context_code in haxiom.
  exists _, _, _.
  unfold shiftedProofContext in *.
  exact (conj hrestricted (conj hendpoint haxiom)).
Qed.

(** The direct universal formula is closed, hence may be prepended while a
    checked proof over the bridge context is rebuilt underneath it. *)
Theorem raw_coqRestrictedPAOpenShell_prepend_universal : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    numeralCode witnessList baseContext conclusion root,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    conclusion root ->
  exists transportedRoot : M,
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode baseContext)
      conclusion transportedRoot.
Proof.
  intros M hPA inputs numeralCode witnessList baseContext
    conclusion root hwitness hroot.
  pose proof (rawDirectTemplateFormula_shift M hPA inputs
    coqRestrictedPADerivationSoundnessUniversalTemplate) as huniversalShift.
  rewrite coqRestrictedPAOpenShell_universal_shift_identity
    in huniversalShift.
  rewrite <- !raw_coqRestrictedPADerivationSoundnessUniversalDirectCode_view
    in huniversalShift.
  destruct (raw_codedPALocalProof_prepend_closed_context M hPA
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    conclusion root
    (raw_coqRestrictedPAConsistencyBridgeContext_realizable M hPA
      witnessList baseContext numeralCode hwitness)
    huniversalShift hroot) as [transportedRoot htransported].
  exists transportedRoot.
  unfold rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode.
  exact htransported.
Qed.

(** Assemble all nine shell roots while exposing only the three arithmetic
    residuals.  Five bridge-context roots are rebuilt below the newly
    adjoined universal assumption; the universal root itself is its genuine
    assumption leaf. *)
Theorem raw_coqRestrictedPAOpenShell_roots_of_support_and_arithmetic : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot
      admissibleRoot contextBoundedRoot contextAdequateRoot,
  rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
  RawCoqRestrictedPASelectedAxiomContextTruthDirectSupport M inputs
    numeralCode witnessList baseContext nextAxiomSoundness
    nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot ->
  RawCoqRestrictedPAOpenShellArithmeticResidual M inputs
    (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
      M inputs numeralCode baseContext)
    admissibleRoot contextBoundedRoot contextAdequateRoot ->
  exists universalRoot contextTruthLawRootInBody
      bottomRefutationRootInBody restrictedProofRootInBody
      endpointRootInBody witnessedContextRootInBody : M,
    RawCoqRestrictedPAOpenShellRoots M inputs
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode baseContext)
      universalRoot contextTruthLawRootInBody bottomRefutationRootInBody
      restrictedProofRootInBody endpointRootInBody admissibleRoot
      witnessedContextRootInBody contextBoundedRoot contextAdequateRoot.
Proof.
  intros M hPA inputs numeralCode witnessList baseContext
    nextAxiomSoundness nextAxiomSoundnessRoot coherenceRoot
    bottomRefutationRoot admissibleRoot contextBoundedRoot
    contextAdequateRoot hlevel hsupport harithmetic.
  pose proof hsupport as hsupportCopy.
  destruct hsupportCopy as
    [hwitness [_ [_ hbottomRefutation]]].
  destruct harithmetic as [hadmissible [hbounded hadequate]].
  pose proof
    (raw_coqRestrictedPAAxiomContextsTruthDirect_of_selected_support
      M hPA inputs numeralCode witnessList baseContext
      nextAxiomSoundness nextAxiomSoundnessRoot coherenceRoot
      bottomRefutationRoot hsupport) as hcontextTruthLaw.
  destruct (raw_coqRestrictedPAOpenShell_projected_roots
    M hPA inputs numeralCode witnessList baseContext hlevel hwitness)
    as (restrictedProofRoot & endpointRoot & witnessedContextRoot &
      hrestricted & hendpoint & hwitnessed).

  destruct (raw_coqRestrictedPAOpenShell_prepend_universal
    M hPA inputs numeralCode witnessList baseContext
    (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs)
    (rawCoqRestrictedPAAxiomContextsTruthDirectRoot M inputs
      numeralCode baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot)
    hwitness hcontextTruthLaw)
    as [contextTruthLawRootInBody hcontextTruthLawInBody].
  destruct (raw_coqRestrictedPAOpenShell_prepend_universal
    M hPA inputs numeralCode witnessList baseContext
    (rawCoqRestrictedPABottomTruthRefutationDirectCode M inputs)
    bottomRefutationRoot hwitness hbottomRefutation)
    as [bottomRefutationRootInBody hbottomRefutationInBody].
  destruct (raw_coqRestrictedPAOpenShell_prepend_universal
    M hPA inputs numeralCode witnessList baseContext
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellRestrictedProofTemplate)
    restrictedProofRoot hwitness hrestricted)
    as [restrictedProofRootInBody hrestrictedInBody].
  destruct (raw_coqRestrictedPAOpenShell_prepend_universal
    M hPA inputs numeralCode witnessList baseContext
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellEndpointTemplate)
    endpointRoot hwitness hendpoint)
    as [endpointRootInBody hendpointInBody].
  destruct (raw_coqRestrictedPAOpenShell_prepend_universal
    M hPA inputs numeralCode witnessList baseContext
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellWitnessedContextTemplate)
    witnessedContextRoot hwitness hwitnessed)
    as [witnessedContextRootInBody hwitnessedInBody].

  set (bodyContext :=
    rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
      M inputs numeralCode baseContext).
  assert (huniversal : RawCodedPALocalProofOf M bodyContext
      (rawDirectTemplateFormula inputs
        coqRestrictedPADerivationSoundnessUniversalTemplate)
      (rawProofAssumptionRoot M bodyContext
        (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode
          M inputs))).
  {
    unfold bodyContext,
      rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode.
    rewrite <- raw_coqRestrictedPADerivationSoundnessUniversalDirectCode_view.
    exact (raw_codedPALocalProofOf_assumption M hPA
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M numeralCode baseContext)
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      (raw_coqRestrictedPAConsistencyBridgeContext_realizable M hPA
        witnessList baseContext numeralCode hwitness)).
  }
  exists
    (rawProofAssumptionRoot M bodyContext
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)),
    contextTruthLawRootInBody, bottomRefutationRootInBody,
    restrictedProofRootInBody, endpointRootInBody,
    witnessedContextRootInBody.
  unfold bodyContext in huniversal.
  unfold rawCoqRestrictedPAAxiomContextsTruthDirectCode in
    hcontextTruthLawInBody.
  unfold rawCoqRestrictedPABottomTruthRefutationDirectCode in
    hbottomRefutationInBody.
  exact (conj huniversal
    (conj hcontextTruthLawInBody
      (conj hbottomRefutationInBody
        (conj hrestrictedInBody
          (conj hendpointInBody
            (conj hadmissible
              (conj hwitnessedInBody (conj hbounded hadequate)))))))).
Qed.

(** The direct shell contradiction immediately yields the exact restricted
    consistency target by represented bottom elimination.  This is the
    child expected by the pre-existing implication-introduction wrapper. *)
Theorem
    raw_coqRestrictedPAConsistencyFromUniversalSoundnessDirect_child_of_arithmetic
    : forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot
      admissibleRoot contextBoundedRoot contextAdequateRoot,
  rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
  RawCoqRestrictedPASelectedAxiomContextTruthDirectSupport M inputs
    numeralCode witnessList baseContext nextAxiomSoundness
    nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot ->
  RawCoqRestrictedPAOpenShellArithmeticResidual M inputs
    (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
      M inputs numeralCode baseContext)
    admissibleRoot contextBoundedRoot contextAdequateRoot ->
  exists child : M,
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode baseContext)
      (rawRestrictedTargetFormulaContextCode M numeralCode
        restrictedPAConsistencyFormulaContext)
      child.
Proof.
  intros M hPA inputs numeralCode witnessList baseContext
    nextAxiomSoundness nextAxiomSoundnessRoot coherenceRoot
    bottomRefutationRoot admissibleRoot contextBoundedRoot
    contextAdequateRoot hlevel hsupport harithmetic.
  destruct
    (raw_coqRestrictedPAOpenShell_roots_of_support_and_arithmetic
      M hPA inputs numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot
      admissibleRoot contextBoundedRoot contextAdequateRoot
      hlevel hsupport harithmetic)
    as (universalRoot & contextTruthLawRoot & bottomLawRoot &
      restrictedRoot & endpointRoot & witnessedRoot & hroots).
  destruct (raw_coqRestrictedPAOpenShell_bottom_same_context
    M hPA inputs
    (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
      M inputs numeralCode baseContext)
    universalRoot contextTruthLawRoot bottomLawRoot
    restrictedRoot endpointRoot admissibleRoot witnessedRoot
    contextBoundedRoot contextAdequateRoot hroots)
    as [bottomRoot hbottom].
  exists (rawProofBotERoot M
    (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
      M inputs numeralCode baseContext)
    (rawRestrictedTargetFormulaContextCode M numeralCode
      restrictedPAConsistencyFormulaContext)
    bottomRoot).
  exact (raw_codedPALocalProofOf_botE M hPA
    (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
      M inputs numeralCode baseContext)
    bottomRoot hbottom
    (rawRestrictedTargetFormulaContextCode M numeralCode
      restrictedPAConsistencyFormulaContext)).
Qed.

(** Compiler form of the exact remaining work.  In particular this is not a
    renamed open compiler: it returns only the three arithmetic roots, while
    the theorem above constructs and applies the other six roots and performs
    the final explosion itself. *)
Definition
    RawCoqRestrictedPAConsistencyFromUniversalSoundnessDirectArithmeticCompiler
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot,
    rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
    RawCoqRestrictedPASelectedAxiomContextTruthDirectSupport M inputs
      numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot ->
    exists admissibleRoot contextBoundedRoot contextAdequateRoot : M,
      RawCoqRestrictedPAOpenShellArithmeticResidual M inputs
        (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
          M inputs numeralCode baseContext)
        admissibleRoot contextBoundedRoot contextAdequateRoot.

Arguments
  RawCoqRestrictedPAConsistencyFromUniversalSoundnessDirectArithmeticCompiler
  M inputs : clear implicits.

Theorem
    raw_coqRestrictedPAConsistencyFromUniversalSoundnessDirectOpenCompiler_of_arithmetic
    : forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPAConsistencyFromUniversalSoundnessDirectArithmeticCompiler
    M inputs ->
  RawCoqRestrictedPAConsistencyFromUniversalSoundnessDirectOpenCompiler
    M inputs.
Proof.
  intros M hPA inputs harithmetic numeralCode witnessList baseContext
    nextAxiomSoundness nextAxiomSoundnessRoot coherenceRoot
    bottomRefutationRoot hlevel hsupport.
  destruct (harithmetic numeralCode witnessList baseContext
    nextAxiomSoundness nextAxiomSoundnessRoot coherenceRoot
    bottomRefutationRoot hlevel hsupport)
    as (admissibleRoot & contextBoundedRoot & contextAdequateRoot &
      hresidual).
  exact
    (raw_coqRestrictedPAConsistencyFromUniversalSoundnessDirect_child_of_arithmetic
      M hPA inputs numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot
      admissibleRoot contextBoundedRoot contextAdequateRoot
      hlevel hsupport hresidual).
Qed.

(** Apply the shell directly in one literal context.  This is stronger than
    weakening its closed curried theorem: no atomic-adequacy certificate for
    the surrounding context is needed, because every All-E and Imp-E node is
    constructed where its premise roots already live. *)
Theorem raw_coqRestrictedPAOpenShell_bottom_same_context : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    context universalRoot contextTruthLawRoot bottomRefutationRoot
      restrictedProofRoot endpointRoot admissibleRoot witnessedContextRoot
      contextBoundedRoot contextAdequateRoot,
  RawCoqRestrictedPAOpenShellRoots M inputs context
    universalRoot contextTruthLawRoot bottomRefutationRoot
    restrictedProofRoot endpointRoot admissibleRoot witnessedContextRoot
    contextBoundedRoot contextAdequateRoot ->
  exists bottomRoot : M,
    RawCodedPALocalProofOf M context (rawFormulaBotCode M) bottomRoot.
Proof.
  intros M hPA inputs context universalRoot contextTruthLawRoot
    bottomRefutationRoot restrictedProofRoot endpointRoot admissibleRoot
    witnessedContextRoot contextBoundedRoot contextAdequateRoot hroots.
  destruct hroots as
    [huniversal [hcontextLaw [hbottomLaw [hrestricted [hendpoint
      [hadmissible [hwitnessed [hbounded hadequate]]]]]]]].
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).

  destruct (raw_codedPALocalProofOf_templateUniversalOpenMany
    M hPA translation context
    coqRestrictedPADerivationSoundnessUniversalTemplate
    coqRestrictedPAOpenShellSoundnessReplacements
    coqRestrictedPAOpenShellSoundnessInstanceTemplate
    universalRoot coqRestrictedPAOpenShell_soundness_open_many
    huniversal) as [soundnessInstanceRoot hsoundnessInstance].
  change (RawCodedPALocalProofOf M context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellSoundnessInstanceTemplate)
    soundnessInstanceRoot) in hsoundnessInstance.
  rewrite coqRestrictedPAOpenShell_soundness_instance_shape,
    !rawDirectTemplateFormula_imp_code in hsoundnessInstance.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellRestrictedProofTemplate)
    (rawFormulaImpCode M
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellEndpointTemplate)
      (rawFormulaImpCode M
        (rawDirectTemplateFormula inputs
          coqRestrictedPAOpenShellAdmissibleTemplate)
        (rawFormulaImpCode M
          (rawDirectTemplateFormula inputs
            coqRestrictedPAOpenShellContextTruthTemplate)
          (rawDirectTemplateFormula inputs
            coqRestrictedPAOpenShellConclusionTruthTemplate))))
    soundnessInstanceRoot restrictedProofRoot
    hsoundnessInstance hrestricted) as hsoundnessAfterRestricted.
  lazymatch type of hsoundnessAfterRestricted with
  | RawCodedPALocalProofOf _ _ _ ?afterRestrictedRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA context
        (rawDirectTemplateFormula inputs
          coqRestrictedPAOpenShellEndpointTemplate)
        (rawFormulaImpCode M
          (rawDirectTemplateFormula inputs
            coqRestrictedPAOpenShellAdmissibleTemplate)
          (rawFormulaImpCode M
            (rawDirectTemplateFormula inputs
              coqRestrictedPAOpenShellContextTruthTemplate)
            (rawDirectTemplateFormula inputs
              coqRestrictedPAOpenShellConclusionTruthTemplate)))
        afterRestrictedRoot endpointRoot
        hsoundnessAfterRestricted hendpoint) as hsoundnessAfterEndpoint
  end.
  lazymatch type of hsoundnessAfterEndpoint with
  | RawCodedPALocalProofOf _ _ _ ?afterEndpointRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA context
        (rawDirectTemplateFormula inputs
          coqRestrictedPAOpenShellAdmissibleTemplate)
        (rawFormulaImpCode M
          (rawDirectTemplateFormula inputs
            coqRestrictedPAOpenShellContextTruthTemplate)
          (rawDirectTemplateFormula inputs
            coqRestrictedPAOpenShellConclusionTruthTemplate))
        afterEndpointRoot admissibleRoot
        hsoundnessAfterEndpoint hadmissible) as hsoundnessAfterAdmissible
  end.

  destruct (raw_codedPALocalProofOf_templateUniversalOpenMany
    M hPA translation context
    coqRestrictedPAAxiomContextsTruthTemplate
    coqRestrictedPAOpenShellContextTruthReplacements
    coqRestrictedPAOpenShellContextTruthLawInstanceTemplate
    contextTruthLawRoot coqRestrictedPAOpenShell_context_truth_open_many
    hcontextLaw) as [contextTruthInstanceRoot hcontextTruthInstance].
  change (RawCodedPALocalProofOf M context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellContextTruthLawInstanceTemplate)
    contextTruthInstanceRoot) in hcontextTruthInstance.
  rewrite coqRestrictedPAOpenShell_context_truth_instance_shape,
    !rawDirectTemplateFormula_imp_code in hcontextTruthInstance.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellWitnessedContextTemplate)
    (rawFormulaImpCode M
      (rawDirectTemplateFormula inputs
        coqRestrictedPAOpenShellContextBoundedTemplate)
      (rawFormulaImpCode M
        (rawDirectTemplateFormula inputs
          coqRestrictedPAOpenShellContextAdequateTemplate)
        (rawDirectTemplateFormula inputs
          coqRestrictedPAOpenShellContextTruthTemplate)))
    contextTruthInstanceRoot witnessedContextRoot
    hcontextTruthInstance hwitnessed) as hcontextAfterWitnessed.
  lazymatch type of hcontextAfterWitnessed with
  | RawCodedPALocalProofOf _ _ _ ?afterWitnessedRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA context
        (rawDirectTemplateFormula inputs
          coqRestrictedPAOpenShellContextBoundedTemplate)
        (rawFormulaImpCode M
          (rawDirectTemplateFormula inputs
            coqRestrictedPAOpenShellContextAdequateTemplate)
          (rawDirectTemplateFormula inputs
            coqRestrictedPAOpenShellContextTruthTemplate))
        afterWitnessedRoot contextBoundedRoot
        hcontextAfterWitnessed hbounded) as hcontextAfterBounded
  end.
  lazymatch type of hcontextAfterBounded with
  | RawCodedPALocalProofOf _ _ _ ?afterBoundedRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA context
        (rawDirectTemplateFormula inputs
          coqRestrictedPAOpenShellContextAdequateTemplate)
        (rawDirectTemplateFormula inputs
          coqRestrictedPAOpenShellContextTruthTemplate)
        afterBoundedRoot contextAdequateRoot
        hcontextAfterBounded hadequate) as hcontextTruth
  end.
  lazymatch type of hsoundnessAfterAdmissible with
  | RawCodedPALocalProofOf _ _ _ ?afterAdmissibleRoot =>
      lazymatch type of hcontextTruth with
      | RawCodedPALocalProofOf _ _ _ ?contextTruthRoot =>
          pose proof (raw_codedPALocalProofOf_impE M hPA context
            (rawDirectTemplateFormula inputs
              coqRestrictedPAOpenShellContextTruthTemplate)
            (rawDirectTemplateFormula inputs
              coqRestrictedPAOpenShellConclusionTruthTemplate)
            afterAdmissibleRoot contextTruthRoot
            hsoundnessAfterAdmissible hcontextTruth) as hconclusionTruth
      end
  end.
  rewrite coqRestrictedPAOpenShell_bottom_refutation_shape,
    rawDirectTemplateFormula_imp_code in hbottomLaw.
  lazymatch type of hconclusionTruth with
  | RawCodedPALocalProofOf _ _ _ ?conclusionTruthRoot =>
      exists (rawProofImpERoot M context
        (rawDirectTemplateFormula inputs
          coqRestrictedPAOpenShellConclusionTruthTemplate)
        (rawFormulaBotCode M)
        bottomRefutationRoot conclusionTruthRoot);
      exact (raw_codedPALocalProofOf_impE M hPA context
        (rawDirectTemplateFormula inputs
          coqRestrictedPAOpenShellConclusionTruthTemplate)
        (rawFormulaBotCode M)
        bottomRefutationRoot conclusionTruthRoot
        hbottomLaw hconclusionTruth)
  end.
Qed.

End
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenIntegration.
