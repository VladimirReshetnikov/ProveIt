(**
  Represented strong-step instance of endpoint hierarchy boundedness.

  The semantic law and its fixed PA source live in
  [RawCodedProofEndpointQuantifierBoundedProofCompilation].  This module
  compiles that source at the concrete four-witness binder layout used by
  direct restricted-derivation soundness.  Keeping the compilation layer
  separate also lets Rocq reuse the already checked, comparatively large
  reified source while this context-safe application code evolves.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedProofAllEConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofUniversalElimination
  RawCodedRestrictedPAProof
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPAAxiomWitnessPrefix
  RawCodedProofEndpointQuantifierBoundedProofCompilation.

Import ListNotations.

Module PABoundedRawCodedStrongStepProofEndpointQuantifierBoundedProofCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofUniversalElimination.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedProofEndpointQuantifierBoundedProofCompilation.

(** Direct quotation of the reified, arbitrarily renamed source body. *)
Lemma
    rawDirect_strongStepProofEndpointQuantifierBoundedRenamedSourceBody_agreement :
  forall (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) renaming,
  rawDirectTemplateFormula inputs
    (embedPAFormula
      (coqStrongStepProofEndpointQuantifierBoundedRenamedSourceBodyFormula
        renaming)) =
  rawQuotedFormulaCode M
    (coqStrongStepProofEndpointQuantifierBoundedRenamedSourceBodyFormula
      renaming).
Proof.
  intros M inputs renaming.
  unfold rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

(** The represented [All-E] trace commutes with ambient renaming because the
    level parameter is abstracted only after that renaming has been applied. *)
Theorem
    rawDirect_strongStepProofEndpointQuantifierBoundedRenamedSource_substitution :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) renaming,
  RawCodedFormulaSingleSubstitution M
    (rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm)
    (rawQuotedFormulaCode M
      (coqStrongStepProofEndpointQuantifierBoundedRenamedSourceBodyFormula
        renaming))
    (rawDirectTemplateFormula inputs
      (templateFormulaRename renaming
        coqStrongStepProofEndpointQuantifierBoundedLawTemplate)).
Proof.
  intros M hPA inputs renaming.
  pose proof (rawDirectTemplateFormula_open M hPA inputs
    (embedPAFormula
      (coqStrongStepProofEndpointQuantifierBoundedRenamedSourceBodyFormula
        renaming))
    coqRestrictedPASoundnessLowerLevelTerm) as hopen.
  rewrite
    rawDirect_strongStepProofEndpointQuantifierBoundedRenamedSourceBody_agreement
    in hopen.
  rewrite
    coqStrongStepProofEndpointQuantifierBoundedRenamedSource_open in hopen.
  exact hopen.
Qed.

(** Compile the quantifier-bounded endpoint law after any ambient variable
    renaming.  This is the proof-producing resource required beneath nested
    direct-shell binders; no independently postulated renamed law root is
    needed. *)
Theorem
    raw_codedPALocalProof_strongStepProofEndpointQuantifierBoundedRenamedLaw_on_witnessed_base :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) renaming
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
        (templateFormulaRename renaming
          coqStrongStepProofEndpointQuantifierBoundedLawTemplate))
      root.
Proof.
  intros M hPA inputs renaming baseWitnessList baseContext hbase.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
    M hPA translation
    (rawDirectStructuralTemplatePAAgreement M hPA inputs)
    baseWitnessList baseContext
    (coqStrongStepProofEndpointQuantifierBoundedRenamedSourceFormula
      renaming)
    hbase
    (PA_proves_coqStrongStepProofEndpointQuantifierBoundedRenamedSourceFormula
      renaming))
    as (witnesses & sourceRoot & hextended & hsource).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext).
  assert (hall : RawCodedPALocalProofOf M extendedContext
      (rawFormulaAllCode M
        (rawQuotedFormulaCode M
          (coqStrongStepProofEndpointQuantifierBoundedRenamedSourceBodyFormula
            renaming)))
      sourceRoot).
  {
    unfold extendedContext, translation in *.
    change (RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawQuotedFormulaCode M
        (coqStrongStepProofEndpointQuantifierBoundedRenamedSourceFormula
          renaming))
      sourceRoot).
    rewrite <- (rawTemplateFormula_embedPA
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (coqStrongStepProofEndpointQuantifierBoundedRenamedSourceFormula
        renaming)).
    exact hsource.
  }
  pose proof (raw_codedPALocalProofOf_allE M hPA extendedContext
    (rawQuotedFormulaCode M
      (coqStrongStepProofEndpointQuantifierBoundedRenamedSourceBodyFormula
        renaming))
    (rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename renaming
        coqStrongStepProofEndpointQuantifierBoundedLawTemplate))
    sourceRoot hall
    (rawDirect_strongStepProofEndpointQuantifierBoundedRenamedSource_substitution
      M hPA inputs renaming)) as hinstance.
  exists witnesses,
    (rawProofAllERoot M extendedContext
      (rawQuotedFormulaCode M
        (coqStrongStepProofEndpointQuantifierBoundedRenamedSourceBodyFormula
          renaming))
      (rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm)
      sourceRoot).
  split; [exact hextended | exact hinstance].
Qed.

(** Direct structural translation agrees with ordinary PA quotation on the
    fixed abstracted source body. *)
Lemma rawDirect_strongStepProofEndpointQuantifierBoundedSourceBody_agreement :
  forall (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
    (embedPAFormula
      coqStrongStepProofEndpointQuantifierBoundedSourceBodyFormula) =
  rawQuotedFormulaCode M
    coqStrongStepProofEndpointQuantifierBoundedSourceBodyFormula.
Proof.
  intros M inputs.
  unfold rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

(** This is the represented All-E trace.  It substitutes the direct code of
    the possibly nonstandard named level into the one abstracted binder and
    produces the concrete [#4/#3/#2] endpoint law. *)
Theorem rawDirect_strongStepProofEndpointQuantifierBoundedSource_substitution :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedFormulaSingleSubstitution M
    (rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm)
    (rawQuotedFormulaCode M
      coqStrongStepProofEndpointQuantifierBoundedSourceBodyFormula)
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointQuantifierBoundedLawTemplate).
Proof.
  intros M hPA inputs.
  pose proof (rawDirectTemplateFormula_open M hPA inputs
    (embedPAFormula
      coqStrongStepProofEndpointQuantifierBoundedSourceBodyFormula)
    coqRestrictedPASoundnessLowerLevelTerm) as hopen.
  rewrite
    rawDirect_strongStepProofEndpointQuantifierBoundedSourceBody_agreement
    in hopen.
  rewrite coqStrongStepProofEndpointQuantifierBoundedSource_open in hopen.
  exact hopen.
Qed.

(** Compile the strong-step law over any caller-owned witnessed base.  The
    only context extension is the finite standard PA-axiom prefix supporting
    the fixed metatheoretic derivation. *)
Theorem
    raw_codedPALocalProof_strongStepProofEndpointQuantifierBoundedLaw_on_witnessed_base :
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
        coqStrongStepProofEndpointQuantifierBoundedLawTemplate)
      root.
Proof.
  intros M hPA inputs baseWitnessList baseContext hbase.
  destruct
    (raw_codedPALocalProof_strongStepProofEndpointQuantifierBoundedRenamedLaw_on_witnessed_base
      M hPA inputs (fun index => index)
      baseWitnessList baseContext hbase)
    as (witnesses & root & hextended & hroot).
  rewrite templateFormulaRename_id in hroot.
  exists witnesses, root.
  split; assumption.
Qed.

(** Apply the concrete law to caller-owned roots.  Both roots are moved to
    the exact witnessed extension selected by the fixed source compiler;
    the result is therefore immediately composable with the other
    strong-step evidence compilers sharing that extension discipline. *)
Theorem
    raw_codedPALocalProof_strongStepProofEndpointQuantifierBounded_of_roots_on_witnessed_extension :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext restrictedRoot endpointRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise)
    restrictedRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointQuantifierBoundedEndpointPremise)
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
        coqStrongStepProofEndpointQuantifierBoundedConclusion)
      resultRoot.
Proof.
  intros M hPA inputs baseWitnessList baseContext
    restrictedRoot endpointRoot hbase hrestricted hendpoint.
  destruct
    (raw_codedPALocalProof_strongStepProofEndpointQuantifierBoundedLaw_on_witnessed_base
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
        coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise)
      restrictedRoot).
  {
    cbn [rawTemplateContextCodeOnTail]. exact hrestricted.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext []
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise)
      restrictedRoot hbase hextended hincluded
      hrestrictedOnEmptyPrefix)
    as [transportedRestrictedRoot htransportedRestricted].
  cbn [rawTemplateContextCodeOnTail] in htransportedRestricted.
  assert (hendpointOnEmptyPrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext [])
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedEndpointPremise)
      endpointRoot).
  {
    cbn [rawTemplateContextCodeOnTail]. exact hendpoint.
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext []
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedEndpointPremise)
      endpointRoot hbase hextended hincluded hendpointOnEmptyPrefix)
    as [transportedEndpointRoot htransportedEndpoint].
  cbn [rawTemplateContextCodeOnTail] in htransportedEndpoint.
  change (RawCodedPALocalProofOf M extendedContext
    (rawTemplateFormula translation
      coqStrongStepProofEndpointQuantifierBoundedLawTemplate)
    implicationRoot) in himplication.
  rewrite coqStrongStepProofEndpointQuantifierBoundedLawTemplate_imp2_shape
    in himplication.
  rewrite !rawTemplateFormula_imp in himplication.
  pose proof (raw_codedPALocalProofOf_impE M hPA extendedContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise)
    (rawFormulaImpCode M
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedEndpointPremise)
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedConclusion))
    implicationRoot transportedRestrictedRoot
    himplication htransportedRestricted) as hafterRestricted.
  lazymatch type of hafterRestricted with
  | RawCodedPALocalProofOf _ _ _ ?afterRestrictedRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA extendedContext
        (rawDirectTemplateFormula inputs
          coqStrongStepProofEndpointQuantifierBoundedEndpointPremise)
        (rawDirectTemplateFormula inputs
          coqStrongStepProofEndpointQuantifierBoundedConclusion)
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

End PABoundedRawCodedStrongStepProofEndpointQuantifierBoundedProofCompilation.
