(**
  Represented endpoint atomic adequacy at the direct strong-step binders.

  The general endpoint compiler accepts a proof-endpoint premise.  The direct
  soundness shell exposes the stronger rule-validity premise instead.  This
  fixed law consumes that exact premise, forgets its constructor-local side
  conditions semantically, and compiles the resulting implication as an
  ordinary coded PA derivation at variables [#4], [#3], and [#2].
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality
  RawCodedProofAtomicAdequacy
  RawCodedProofRules
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPAAxiomWitnessPrefix
  RawCodedProofEndpointQuantifierBoundedProofCompilation.

Import ListNotations.

Module PABoundedRawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedProofEndpointQuantifierBoundedProofCompilation.

(** The two outer assignment slots remain unused at this point in the direct
    shell, hence the proof/context/conclusion indices [4], [3], and [2]. *)
Definition strongStepProofEndpointAtomicAdequacyFormula : formula :=
  pImp
    (proofAtomicallyAdequateTermAt (tVar 4))
    (pImp
      (proofRuleValidTermAt (tVar 4) (tVar 3) (tVar 2))
      (codedFormulaAtomicallyAdequateTermAt (tVar 2))).

Lemma raw_sat_strongStepProofEndpointAtomicAdequacyFormula_iff : forall
    (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e strongStepProofEndpointAtomicAdequacyFormula <->
  (RawProofAtomicallyAdequate M (e 4) ->
   RawProofRuleValid M (e 4) (e 3) (e 2) ->
   RawCodedFormulaAtomicallyAdequate M (e 2)).
Proof.
  intros M e.
  unfold strongStepProofEndpointAtomicAdequacyFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_proofAtomicallyAdequateTermAt_iff.
  setoid_rewrite raw_sat_proofRuleValidTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaAtomicallyAdequateTermAt_iff.
  cbn [raw_term_eval scons]. tauto.
Qed.

Theorem strongStepProofEndpointAtomicAdequacyFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e strongStepProofEndpointAtomicAdequacyFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_strongStepProofEndpointAtomicAdequacyFormula_iff M e)).
  intros hatomic hrule.
  exact (proj2
    (raw_proofAtomicallyAdequate_root_endpoint M hPA (e 4) hatomic
      (e 3) (e 2)
      (raw_proofRuleValid_endpoint M (e 4) (e 3) (e 2) hrule))).
Qed.

(** Completeness is applied only to this fixed standard arithmetic formula.
    Sealing and reopening preserves its five free shell variables without
    introducing any carrier-valued syntax into the metatheoretic proof. *)
Theorem PA_proves_strongStepProofEndpointAtomicAdequacyFormula :
  Formula.BProv Formula.Ax_s []
    strongStepProofEndpointAtomicAdequacyFormula.
Proof.
  assert (hclosed : Formula.BProv Formula.Ax_s []
      (Formula.sealPA strongStepProofEndpointAtomicAdequacyFormula)).
  {
    apply PA_BProv_of_raw_valid.
    - apply Formula.sealPA_sentence.
    - intros M hPA e.
      apply raw_formula_sat_sealPA_of_valid.
      intro inner.
      exact
        (strongStepProofEndpointAtomicAdequacyFormula_raw_valid
          M hPA inner).
  }
  pose proof (Formula.BProv_sealPA_allE_rename Formula.Ax_s []
    strongStepProofEndpointAtomicAdequacyFormula
    (fun index => index) hclosed) as hopen.
  now rewrite Formula.rename_id in hopen.
Qed.

Definition coqStrongStepProofEndpointAtomicAdequacyLawTemplate
    : TemplateFormula :=
  embedPAFormula strongStepProofEndpointAtomicAdequacyFormula.

Definition coqStrongStepProofEndpointAtomicAdequacyAtomicPremise
    : TemplateFormula :=
  templateImpAntecedent
    coqStrongStepProofEndpointAtomicAdequacyLawTemplate.

Definition coqStrongStepProofEndpointAtomicAdequacyRulePremise
    : TemplateFormula :=
  templateImpAntecedent (templateImpConsequent
    coqStrongStepProofEndpointAtomicAdequacyLawTemplate).

Definition coqStrongStepProofEndpointAtomicAdequacyConclusion
    : TemplateFormula :=
  templateImpConsequent (templateImpConsequent
    coqStrongStepProofEndpointAtomicAdequacyLawTemplate).

Lemma coqStrongStepProofEndpointAtomicAdequacyLawTemplate_imp2_shape :
  coqStrongStepProofEndpointAtomicAdequacyLawTemplate =
  tfImp coqStrongStepProofEndpointAtomicAdequacyAtomicPremise
    (tfImp coqStrongStepProofEndpointAtomicAdequacyRulePremise
      coqStrongStepProofEndpointAtomicAdequacyConclusion).
Proof. reflexivity. Qed.

Lemma coqStrongStepProofEndpointAtomicAdequacyAtomicPremise_view :
  coqStrongStepProofEndpointAtomicAdequacyAtomicPremise =
  embedPAFormula (proofAtomicallyAdequateTermAt (tVar 4)).
Proof. reflexivity. Qed.

Lemma coqStrongStepProofEndpointAtomicAdequacyRulePremise_view :
  coqStrongStepProofEndpointAtomicAdequacyRulePremise =
  embedPAFormula (proofRuleValidTermAt (tVar 4) (tVar 3) (tVar 2)).
Proof. reflexivity. Qed.

Lemma coqStrongStepProofEndpointAtomicAdequacyConclusion_view :
  coqStrongStepProofEndpointAtomicAdequacyConclusion =
  embedPAFormula (codedFormulaAtomicallyAdequateTermAt (tVar 2)).
Proof. reflexivity. Qed.

Theorem
    raw_codedPALocalProof_strongStepProofEndpointAtomicAdequacyLaw_on_witnessed_base :
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
        coqStrongStepProofEndpointAtomicAdequacyLawTemplate)
      root.
Proof.
  intros M hPA inputs baseWitnessList baseContext hbase.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
    M hPA translation
    (rawDirectStructuralTemplatePAAgreement M hPA inputs)
    baseWitnessList baseContext
    strongStepProofEndpointAtomicAdequacyFormula
    hbase PA_proves_strongStepProofEndpointAtomicAdequacyFormula)
    as (witnesses & root & hextended & hroot).
  exists witnesses, root. split; [exact hextended |].
  change (RawCodedPALocalProofOf M
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext)
    (rawTemplateFormula translation
      (embedPAFormula strongStepProofEndpointAtomicAdequacyFormula)) root).
  exact hroot.
Qed.

(** Transport both caller roots through the selected standard prefix and
    perform the two represented implication eliminations. *)
Theorem
    raw_codedPALocalProof_strongStepProofEndpointAtomicAdequacy_of_roots_on_witnessed_extension :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext atomicRoot ruleRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
    atomicRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyRulePremise)
    ruleRoot ->
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
        coqStrongStepProofEndpointAtomicAdequacyConclusion)
      resultRoot.
Proof.
  intros M hPA inputs baseWitnessList baseContext
    atomicRoot ruleRoot hbase hatomic hrule.
  destruct
    (raw_codedPALocalProof_strongStepProofEndpointAtomicAdequacyLaw_on_witnessed_base
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
  assert (hatomicOnEmptyPrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext [])
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
      atomicRoot).
  { cbn [rawTemplateContextCodeOnTail]. exact hatomic. }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext []
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
      atomicRoot hbase hextended hincluded hatomicOnEmptyPrefix)
    as [transportedAtomicRoot htransportedAtomic].
  cbn [rawTemplateContextCodeOnTail] in htransportedAtomic.
  assert (hruleOnEmptyPrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext [])
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)
      ruleRoot).
  { cbn [rawTemplateContextCodeOnTail]. exact hrule. }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext []
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)
      ruleRoot hbase hextended hincluded hruleOnEmptyPrefix)
    as [transportedRuleRoot htransportedRule].
  cbn [rawTemplateContextCodeOnTail] in htransportedRule.
  change (RawCodedPALocalProofOf M extendedContext
    (rawTemplateFormula translation
      coqStrongStepProofEndpointAtomicAdequacyLawTemplate)
    implicationRoot) in himplication.
  rewrite coqStrongStepProofEndpointAtomicAdequacyLawTemplate_imp2_shape
    in himplication.
  rewrite !rawTemplateFormula_imp in himplication.
  pose proof (raw_codedPALocalProofOf_impE M hPA extendedContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
    (rawFormulaImpCode M
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyConclusion))
    implicationRoot transportedAtomicRoot
    himplication htransportedAtomic) as hafterAtomic.
  lazymatch type of hafterAtomic with
  | RawCodedPALocalProofOf _ _ _ ?afterAtomicRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA extendedContext
        (rawDirectTemplateFormula inputs
          coqStrongStepProofEndpointAtomicAdequacyRulePremise)
        (rawDirectTemplateFormula inputs
          coqStrongStepProofEndpointAtomicAdequacyConclusion)
        afterAtomicRoot transportedRuleRoot
        hafterAtomic htransportedRule) as hresult;
      lazymatch type of hresult with
      | RawCodedPALocalProofOf _ _ _ ?resultRoot =>
          exists witnesses, resultRoot;
          split; [exact hextended |];
          split; [exact hincluded | exact hresult]
      end
  end.
Qed.

End PABoundedRawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.
