(**
  Synchronize the two represented endpoint invariants needed by dynamic truth.

  The rank-domain and atomic-adequacy laws are intentionally independent fixed
  PA theorems and may select different finite axiom-witness prefixes.  This
  module composes those prefixes, transports the first result through the
  second extension, and exposes both roots in one literal witnessed context.
  A final wrapper projects the two restricted-proof fields from the direct
  shell's conjunction, so clients need supply only that assumption and the
  common rule-validity root.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFormulaOperationCrossTraceFunctionality
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedProofAtomicAdequacy
  RawCodedProofRules
  RawCodedProofRuleCoverage
  RawCodedRestrictedPAProof
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedFixedLevelTruthTotality
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPAAxiomWitnessPrefix
  RawCodedLtSuccCasesProofCompilation
  RawCodedPAGrowingTemplateConjunction
  RawCodedRestrictedTargetTemplateContext
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthLocalAdmissibilityCompilation
  RawCodedProofEndpointQuantifierBoundedProofCompilation
  RawCodedStrongStepProofEndpointQuantifierBoundedProofCompilation
  RawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.

Import ListNotations.

Module PABoundedRawCodedStrongStepProofEndpointEvidenceCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationCrossTraceFunctionality.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedPAGrowingTemplateConjunction.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthLocalAdmissibilityCompilation.
Import
  PABoundedRawCodedStrongStepProofEndpointQuantifierBoundedProofCompilation.
Import
  PABoundedRawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.
Import PABoundedRawCodedProofEndpointQuantifierBoundedProofCompilation.

(** Both exact laws consume the same shell rule-validity formula. *)
Lemma coqStrongStepEndpointEvidence_rule_premises_agree :
  coqStrongStepProofEndpointAtomicAdequacyRulePremise =
  coqStrongStepProofEndpointQuantifierBoundedEndpointPremise.
Proof. reflexivity. Qed.

(** The restricted proof premise is a conjunction of its hierarchy core and
    three proof-wide certificates.  These stable equalities let the wrapper
    use two ordinary represented And-E steps without unfolding either large
    encoded predicate at client sites. *)
Lemma coqRestrictedPADerivationSoundnessRestrictedProofTemplate_view :
  coqRestrictedPADerivationSoundnessRestrictedProofTemplate =
  tfAnd coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise
    (tfAnd coqStrongStepProofEndpointAtomicAdequacyAtomicPremise
      (tfAnd
        (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 4)))
        (embedPAFormula (proofRuleCoverageTermAt (tVar 4))))).
Proof. reflexivity. Qed.

(** Project all four stable fields from the restricted-proof package after
    an arbitrary ambient renaming.  The same nested And-E sequence was
    previously repeated by the exact-tail and under-prefix endpoint
    wrappers.  Stating it renaming-naturally both removes that duplication
    and exposes precisely the inherited resources available inside a deep
    direct-shell eigenvariable context. *)
Theorem
    raw_codedPALocalProof_restrictedProofTemplate_renamed_projections :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    localContext (renaming : nat -> nat) restrictedRoot,
  RawCodedPALocalProofOf M localContext
    (rawTemplateFormula translation
      (templateFormulaRename renaming
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate))
    restrictedRoot ->
  exists coreRoot atomicRoot formulaCoverageRoot ruleCoverageRoot,
    RawCodedPALocalProofOf M localContext
      (rawTemplateFormula translation
        (templateFormulaRename renaming
          coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise))
      coreRoot /\
    RawCodedPALocalProofOf M localContext
      (rawTemplateFormula translation
        (templateFormulaRename renaming
          coqStrongStepProofEndpointAtomicAdequacyAtomicPremise))
      atomicRoot /\
    RawCodedPALocalProofOf M localContext
      (rawTemplateFormula translation
        (templateFormulaRename renaming
          (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 4)))))
      formulaCoverageRoot /\
    RawCodedPALocalProofOf M localContext
      (rawTemplateFormula translation
        (templateFormulaRename renaming
          (embedPAFormula (proofRuleCoverageTermAt (tVar 4)))))
      ruleCoverageRoot.
Proof.
  intros M hPA translation localContext renaming restrictedRoot
    hrestricted.
  rewrite coqRestrictedPADerivationSoundnessRestrictedProofTemplate_view
    in hrestricted.
  cbn [templateFormulaRename] in hrestricted.
  rewrite !rawTemplateFormula_and in hrestricted.
  pose proof
    (raw_codedPALocalProofOf_andE1 M hPA localContext _ _
      restrictedRoot hrestricted) as hcore.
  pose proof
    (raw_codedPALocalProofOf_andE2 M hPA localContext _ _
      restrictedRoot hrestricted) as hcertificates.
  lazymatch type of hcertificates with
  | RawCodedPALocalProofOf _ _ _ ?certificatesRoot =>
      pose proof
        (raw_codedPALocalProofOf_andE1 M hPA localContext _ _
          certificatesRoot hcertificates) as hatomic;
      pose proof
        (raw_codedPALocalProofOf_andE2 M hPA localContext _ _
          certificatesRoot hcertificates) as hcoverages
  end.
  lazymatch type of hcoverages with
  | RawCodedPALocalProofOf _ _ _ ?coveragesRoot =>
      pose proof
        (raw_codedPALocalProofOf_andE1 M hPA localContext _ _
          coveragesRoot hcoverages) as hformulaCoverage;
      pose proof
        (raw_codedPALocalProofOf_andE2 M hPA localContext _ _
          coveragesRoot hcoverages) as hruleCoverage
  end.
  lazymatch type of hcore with
  | RawCodedPALocalProofOf _ _ _ ?coreRoot => exists coreRoot
  end.
  lazymatch type of hatomic with
  | RawCodedPALocalProofOf _ _ _ ?atomicRoot => exists atomicRoot
  end.
  lazymatch type of hformulaCoverage with
  | RawCodedPALocalProofOf _ _ _ ?formulaCoverageRoot =>
      exists formulaCoverageRoot
  end.
  lazymatch type of hruleCoverage with
  | RawCodedPALocalProofOf _ _ _ ?ruleCoverageRoot =>
      exists ruleCoverageRoot
  end.
  repeat (first [assumption | split]).
Qed.

(** Identity renaming is the common outer-shell case.  Keeping it as a
    corollary lets callers use the structural projection theorem without
    repeating normalization of four renamed conclusions. *)
Corollary raw_codedPALocalProof_restrictedProofTemplate_projections :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    localContext restrictedRoot,
  RawCodedPALocalProofOf M localContext
    (rawTemplateFormula translation
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    restrictedRoot ->
  exists coreRoot atomicRoot formulaCoverageRoot ruleCoverageRoot,
    RawCodedPALocalProofOf M localContext
      (rawTemplateFormula translation
        coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise)
      coreRoot /\
    RawCodedPALocalProofOf M localContext
      (rawTemplateFormula translation
        coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
      atomicRoot /\
    RawCodedPALocalProofOf M localContext
      (rawTemplateFormula translation
        (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 4))))
      formulaCoverageRoot /\
    RawCodedPALocalProofOf M localContext
      (rawTemplateFormula translation
        (embedPAFormula (proofRuleCoverageTermAt (tVar 4))))
      ruleCoverageRoot.
Proof.
  intros M hPA translation localContext restrictedRoot hrestricted.
  pose proof
    (raw_codedPALocalProof_restrictedProofTemplate_renamed_projections
      M hPA translation localContext (fun index => index) restrictedRoot)
    as hproject.
  rewrite !templateFormulaRename_id in hproject.
  exact (hproject hrestricted).
Qed.

(** A renamed restricted package which is already present in the temporary
    prefix needs no separate proof producer.  Compile its assumption leaf
    over the witnessed PA tail and immediately expose all four projections.
    This is the form used after entering eigenvariables: the prefix contains
    the renamed package literally, even though it no longer contains the
    unrenamed outer-shell formula. *)
Corollary
    raw_codedPALocalProof_restrictedProofTemplate_renamed_projections_of_template_assumption :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext prefix (renaming : nat -> nat),
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  In (templateFormulaRename renaming
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    prefix ->
  exists coreRoot atomicRoot formulaCoverageRoot ruleCoverageRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext prefix)
      (rawTemplateFormula translation
        (templateFormulaRename renaming
          coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise))
      coreRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext prefix)
      (rawTemplateFormula translation
        (templateFormulaRename renaming
          coqStrongStepProofEndpointAtomicAdequacyAtomicPremise))
      atomicRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext prefix)
      (rawTemplateFormula translation
        (templateFormulaRename renaming
          (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 4)))))
      formulaCoverageRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext prefix)
      (rawTemplateFormula translation
        (templateFormulaRename renaming
          (embedPAFormula (proofRuleCoverageTermAt (tVar 4)))))
      ruleCoverageRoot.
Proof.
  intros M hPA translation witnessList baseContext prefix renaming
    hwitnessed hmember.
  pose proof
    (raw_templateAssumptionOnPAAxiomContext_localProof
      M hPA translation witnessList baseContext prefix
      (templateFormulaRename renaming
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
      hwitnessed hmember) as hrestricted.
  lazymatch type of hrestricted with
  | RawCodedPALocalProofOf _ _ _ ?restrictedRoot =>
      exact
        (raw_codedPALocalProof_restrictedProofTemplate_renamed_projections
          M hPA translation
          (rawTemplateContextCodeOnTail translation baseContext prefix)
          renaming restrictedRoot hrestricted)
  end.
Qed.

(** The native local-domain templates deliberately reserve variable zero for
    the level numeral.  Opening that slot moves their formula argument from
    [#3] to the strong-step conclusion slot [#2], yielding exactly the two
    restricted-target domain contexts. *)
Lemma coqStrongStepSigmaDomainTemplate_open :
  templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
    (embedPAFormula dynamicTruthLocalSigmaInputDomainTemplate) =
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetSigmaDomainContext (tVar 2)).
Proof. reflexivity. Qed.

Lemma coqStrongStepPiDomainTemplate_open :
  templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
    (embedPAFormula dynamicTruthLocalPiInputDomainTemplate) =
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetPiDomainContext (tVar 2)).
Proof. reflexivity. Qed.

(** PA embedding agreement turns the atomic conclusion into the exact fixed
    numeral used by native local admissibility. *)
Lemma raw_strongStepEndpointAtomicAdequacyConclusion_code : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
    coqStrongStepProofEndpointAtomicAdequacyConclusion =
  rawDynamicTruthLocalAtomicAdequacyCode M.
Proof.
  intros M hPA inputs.
  rewrite coqStrongStepProofEndpointAtomicAdequacyConclusion_view.
  unfold rawDirectTemplateFormula.
  rewrite rawStructuralTemplateFormulaWith_embedPA.
  rewrite rawQuotedFormulaCode_standard by exact hPA.
  reflexivity.
Qed.

(** General nonstandard domain alignment.  The two trace outputs need not be
    decoded: represented substitution functionality identifies them with the
    direct restricted-target outputs once their common numeral-term code is
    named. *)
Theorem raw_strongStepEndpointQuantifierBoundedConclusion_code : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    levelNumeral sigmaDomain piDomain,
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = levelNumeral ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
    sigmaDomain ->
  RawCodedFormulaSingleSubstitution M levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalPiInputDomainTemplate))
    piDomain ->
  rawDirectTemplateFormula inputs
    coqStrongStepProofEndpointQuantifierBoundedConclusion =
  rawFormulaOrCode M sigmaDomain piDomain.
Proof.
  intros M hPA inputs levelNumeral sigmaDomain piDomain
    hlevel hsigma hpi.
  pose proof (rawDirectTemplateFormula_open M hPA inputs
    (embedPAFormula dynamicTruthLocalSigmaInputDomainTemplate)
    coqRestrictedPASoundnessLowerLevelTerm) as hsigmaDirect.
  pose proof (rawDirectTemplateFormula_open M hPA inputs
    (embedPAFormula dynamicTruthLocalPiInputDomainTemplate)
    coqRestrictedPASoundnessLowerLevelTerm) as hpiDirect.
  unfold rawDirectTemplateFormula in hsigmaDirect, hpiDirect.
  rewrite !rawStructuralTemplateFormulaWith_embedPA
    in hsigmaDirect, hpiDirect.
  rewrite coqStrongStepSigmaDomainTemplate_open in hsigmaDirect.
  rewrite coqStrongStepPiDomainTemplate_open in hpiDirect.
  rewrite !rawQuotedFormulaCode_standard in hsigmaDirect, hpiDirect
    by exact hPA.
  rewrite hlevel in hsigmaDirect, hpiDirect.
  pose proof (raw_codedFormulaSingleSubstitution_functional M hPA
    levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalSigmaInputDomainTemplate))
    (rawStructuralTemplateFormulaWith M
      (rawDirectTemplateSymbols inputs)
      (restrictedTargetTemplateFormulaContext
        coqRestrictedPASoundnessLowerLevelTerm
        (restrictedTargetSigmaDomainContext (tVar 2))))
    sigmaDomain hsigmaDirect hsigma) as hsigmaCode.
  pose proof (raw_codedFormulaSingleSubstitution_functional M hPA
    levelNumeral
    (rawNumeralValue M
      (formulaCode dynamicTruthLocalPiInputDomainTemplate))
    (rawStructuralTemplateFormulaWith M
      (rawDirectTemplateSymbols inputs)
      (restrictedTargetTemplateFormulaContext
        coqRestrictedPASoundnessLowerLevelTerm
        (restrictedTargetPiDomainContext (tVar 2))))
    piDomain hpiDirect hpi) as hpiCode.
  rewrite coqStrongStepProofEndpointQuantifierBoundedConclusion_view.
  unfold rawDirectTemplateFormula.
  rewrite rawStructuralWith_restrictedTargetTemplateFormulaContext.
  cbn [restrictedTargetFormulaQuantifierBoundedContext
    rawRestrictedTargetFormulaContextCode].
  rewrite <- !rawStructuralWith_restrictedTargetTemplateFormulaContext.
  now rewrite hsigmaCode, hpiCode.
Qed.

(** Generic context-safe application of a two-premise template law.  Fixed
    PA theorem compilers naturally return the law over a witnessed tail; this
    lemma inserts it beneath an arbitrary adequate temporary prefix, moves
    both caller premises through the same tail extension, and performs the
    two represented modus-ponens steps. *)
Theorem raw_codedPALocalProof_twoPremiseLaw_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (translation : RawCodedTemplateTranslation M)
    baseWitnessList baseContext targetWitnessList targetContext prefix
    law premise1 premise2 conclusion lawRoot premise1Root premise2Root,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPAAxiomWitnessContext M targetWitnessList targetContext ->
  RawContextListIncluded M baseContext targetContext ->
  law = tfImp premise1 (tfImp premise2 conclusion) ->
  RawCodedPALocalProofOf M targetContext
    (rawTemplateFormula translation law) lawRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation premise1) premise1Root ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation premise2) premise2Root ->
  exists resultRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawTemplateFormula translation conclusion) resultRoot.
Proof.
  intros M hPA translation baseWitnessList baseContext
    targetWitnessList targetContext prefix law premise1 premise2 conclusion
    lawRoot premise1Root premise2Root hprefix hbase htarget hincluded
    hshape hlaw hpremise1 hpremise2.
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    targetContext prefix (rawTemplateFormula translation law) lawRoot
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed M
      targetWitnessList targetContext htarget)
    hprefix hlaw) as [prefixedLawRoot hprefixedLaw].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext prefix
      (rawTemplateFormula translation premise1) premise1Root
      hbase htarget hincluded hpremise1)
    as [transportedPremise1Root htransportedPremise1].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext prefix
      (rawTemplateFormula translation premise2) premise2Root
      hbase htarget hincluded hpremise2)
    as [transportedPremise2Root htransportedPremise2].
  rewrite hshape, !rawTemplateFormula_imp in hprefixedLaw.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawTemplateContextCodeOnTail translation targetContext prefix)
    (rawTemplateFormula translation premise1)
    (rawFormulaImpCode M
      (rawTemplateFormula translation premise2)
      (rawTemplateFormula translation conclusion))
    prefixedLawRoot transportedPremise1Root
    hprefixedLaw htransportedPremise1) as hafterPremise1.
  lazymatch type of hafterPremise1 with
  | RawCodedPALocalProofOf _ _ _ ?afterPremise1Root =>
      pose proof (raw_codedPALocalProofOf_impE M hPA
        (rawTemplateContextCodeOnTail translation targetContext prefix)
        (rawTemplateFormula translation premise2)
        (rawTemplateFormula translation conclusion)
        afterPremise1Root transportedPremise2Root
        hafterPremise1 htransportedPremise2) as hresult;
      lazymatch type of hresult with
      | RawCodedPALocalProofOf _ _ _ ?resultRoot =>
          exists resultRoot; exact hresult
      end
  end.
Qed.

(** Renaming-natural application of an arbitrary two-premise PA law.
    Eigenvariable entry renames the inherited premises, the law, and its
    conclusion uniformly.  Instead of asking every client to construct a
    renamed proof root, we rename the ordinary PA derivation (PA axioms are
    sentences), compile it on the caller's witnessed tail, insert the
    temporary prefix, and perform both represented modus-ponens steps.

    This theorem intentionally makes no claim that a renamed conclusion is
    the unrenamed endpoint needed by a particular callback.  Such an
    identification is a separate semantic obligation and cannot be hidden by
    context bookkeeping. *)
Theorem
    raw_codedPALocalProof_twoPremisePALaw_renamed_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    (renaming : nat -> nat)
    baseWitnessList baseContext prefix
    law premise1 premise2 conclusion premise1Root premise2Root,
  law = pImp premise1 (pImp premise2 conclusion) ->
  Formula.BProv Formula.Ax_s [] law ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (templateFormulaRename renaming (embedPAFormula premise1)))
    premise1Root ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (templateFormulaRename renaming (embedPAFormula premise2)))
    premise2Root ->
  exists targetWitnessList targetContext resultRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawTemplateFormula translation
        (templateFormulaRename renaming (embedPAFormula conclusion)))
      resultRoot.
Proof.
  intros M hPA translation hagreement renaming
    baseWitnessList baseContext prefix
    law premise1 premise2 conclusion premise1Root premise2Root
    hshape hlaw hprefix hbase hpremise1 hpremise2.
  assert (hrenamedLaw : Formula.BProv Formula.Ax_s []
      (Formula.rename renaming law)).
  {
    change (Formula.BProv Formula.Ax_s
      (map (Formula.rename renaming) [])
      (Formula.rename renaming law)).
    exact (Formula.BProv_rename_of_sentences
      Formula.Ax_s Formula.sentence_ax_s [] law hlaw renaming).
  }
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      (Formula.rename renaming law) hbase hrenamedLaw)
    as (witnesses & lawRoot & htargetWitnessed & hlawRoot).
  set (targetWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses baseWitnessList).
  set (targetContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  assert (hincluded : RawContextListIncluded M baseContext targetContext).
  {
    unfold targetContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA witnesses baseContext).
  }
  assert (hrenamedLawRoot : RawCodedPALocalProofOf M targetContext
      (rawTemplateFormula translation
        (templateFormulaRename renaming (embedPAFormula law))) lawRoot).
  {
    unfold targetContext.
    rewrite <- embedPAFormula_rename.
    exact hlawRoot.
  }
  pose proof
    (raw_codedPALocalProof_twoPremiseLaw_on_witnessed_tail_under_prefix
      M hPA translation baseWitnessList baseContext
      targetWitnessList targetContext prefix
      (templateFormulaRename renaming (embedPAFormula law))
      (templateFormulaRename renaming (embedPAFormula premise1))
      (templateFormulaRename renaming (embedPAFormula premise2))
      (templateFormulaRename renaming (embedPAFormula conclusion))
      lawRoot premise1Root premise2Root hprefix hbase
      htargetWitnessed hincluded) as hresult.
  assert (hrenamedShape :
      templateFormulaRename renaming (embedPAFormula law) =
      tfImp (templateFormulaRename renaming (embedPAFormula premise1))
        (tfImp
          (templateFormulaRename renaming (embedPAFormula premise2))
          (templateFormulaRename renaming (embedPAFormula conclusion)))).
  {
    rewrite hshape.
    cbn [embedPAFormula templateFormulaRename].
    reflexivity.
  }
  specialize (hresult hrenamedShape hrenamedLawRoot hpremise1 hpremise2).
  destruct hresult as [resultRoot hresult].
  exists targetWitnessList, targetContext, resultRoot.
  split; [exact htargetWitnessed |].
  split; assumption.
Qed.

(** The atomic endpoint law is an ordinary PA formula, so the generic
    renaming theorem applies without exposing its three formula components
    at each use site.  This is the exact inherited-premise result available
    after any number of direct-shell eigenvariables have been entered. *)
Corollary
    raw_codedPALocalProof_strongStepProofEndpointAtomicAdequacy_renamed_of_roots_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    (renaming : nat -> nat)
    baseWitnessList baseContext prefix atomicRoot ruleRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (templateFormulaRename renaming
        coqStrongStepProofEndpointAtomicAdequacyAtomicPremise))
    atomicRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (templateFormulaRename renaming
        coqStrongStepProofEndpointAtomicAdequacyRulePremise))
    ruleRoot ->
  exists targetWitnessList targetContext resultRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawTemplateFormula translation
        (templateFormulaRename renaming
          coqStrongStepProofEndpointAtomicAdequacyConclusion))
      resultRoot.
Proof.
  intros M hPA translation hagreement renaming
    baseWitnessList baseContext prefix atomicRoot ruleRoot
    hprefix hbase hatomic hrule.
  exact
    (raw_codedPALocalProof_twoPremisePALaw_renamed_on_witnessed_tail_under_prefix
      M hPA translation hagreement renaming
      baseWitnessList baseContext prefix
      strongStepProofEndpointAtomicAdequacyFormula
      (proofAtomicallyAdequateTermAt (tVar 4))
      (proofRuleValidTermAt (tVar 4) (tVar 3) (tVar 2))
      (codedFormulaAtomicallyAdequateTermAt (tVar 2))
      atomicRoot ruleRoot eq_refl
      PA_proves_strongStepProofEndpointAtomicAdequacyFormula
      hprefix hbase hatomic hrule).
Qed.

(** Assumption-only specialization of the renamed atomic endpoint.  Both
    premises are inherited from the shifted direct shell; the restricted
    package is projected once and the represented PA law is then applied on
    the same retained prefix.  Only the standard PA witness tail may grow. *)
Corollary
    raw_codedPALocalProof_strongStepProofEndpointAtomicAdequacy_renamed_of_template_assumptions_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    (renaming : nat -> nat)
    baseWitnessList baseContext prefix,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  In (templateFormulaRename renaming
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    prefix ->
  In (templateFormulaRename renaming
      coqStrongStepProofEndpointAtomicAdequacyRulePremise)
    prefix ->
  exists targetWitnessList targetContext resultRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawTemplateFormula translation
        (templateFormulaRename renaming
          coqStrongStepProofEndpointAtomicAdequacyConclusion))
      resultRoot.
Proof.
  intros M hPA translation hagreement renaming
    baseWitnessList baseContext prefix hprefix hbase
    hrestrictedIn hruleIn.
  destruct
    (raw_codedPALocalProof_restrictedProofTemplate_renamed_projections_of_template_assumption
      M hPA translation baseWitnessList baseContext prefix renaming
      hbase hrestrictedIn)
    as (coreRoot & atomicRoot & formulaCoverageRoot &
      ruleCoverageRoot & hcore & hatomic &
      hformulaCoverage & hruleCoverage).
  pose proof
    (raw_templateAssumptionOnPAAxiomContext_localProof
      M hPA translation baseWitnessList baseContext prefix
      (templateFormulaRename renaming
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)
      hbase hruleIn) as hrule.
  lazymatch type of hrule with
  | RawCodedPALocalProofOf _ _ _ ?ruleRoot =>
      exact
        (raw_codedPALocalProof_strongStepProofEndpointAtomicAdequacy_renamed_of_roots_on_witnessed_tail_under_prefix
          M hPA translation hagreement renaming
          baseWitnessList baseContext prefix atomicRoot ruleRoot
          hprefix hbase hatomic hrule)
  end.
Qed.

(** Binder-count interface for the preceding renaming-natural result.
    Membership is shifted structurally through the eigenvariable context,
    then [templateFormulaShiftMany_as_rename] presents the inherited formulas
    in the uniform renaming form expected by the endpoint compiler. *)
Corollary
    raw_codedPALocalProof_strongStepProofEndpointAtomicAdequacy_of_template_assumptions_after_binders_on_witnessed_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    binderCount baseWitnessList baseContext callerPrefix,
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (templateContextShiftMany binderCount callerPrefix) ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
    callerPrefix ->
  In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
  exists targetWitnessList targetContext resultRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext
        (templateContextShiftMany binderCount callerPrefix))
      (rawTemplateFormula translation
        (templateFormulaRename
          (templateShiftRenamingMany binderCount)
          coqStrongStepProofEndpointAtomicAdequacyConclusion))
      resultRoot.
Proof.
  intros M hPA translation hagreement binderCount
    baseWitnessList baseContext callerPrefix hprefix hbase
    hrestrictedIn hruleIn.
  apply
    (raw_codedPALocalProof_strongStepProofEndpointAtomicAdequacy_renamed_of_template_assumptions_on_witnessed_tail_under_prefix
      M hPA translation hagreement
      (templateShiftRenamingMany binderCount)
      baseWitnessList baseContext
      (templateContextShiftMany binderCount callerPrefix)
      hprefix hbase).
  - rewrite <- templateFormulaShiftMany_as_rename.
    exact (templateContextShiftMany_member binderCount callerPrefix
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate
      hrestrictedIn).
  - rewrite <- templateFormulaShiftMany_as_rename.
    exact (templateContextShiftMany_member binderCount callerPrefix
      coqStrongStepProofEndpointAtomicAdequacyRulePremise hruleIn).
Qed.

(** Renaming-natural rank-domain specialization.  Unlike the ordinary PA
    atomic law, this law contains a named nonstandard level parameter.  The
    renamed source compiler abstracts and reopens that parameter after
    renaming, then the generic prefix-safe two-premise adapter synchronizes
    the resulting law with both inherited roots. *)
Theorem
    raw_codedPALocalProof_strongStepProofEndpointQuantifierBounded_renamed_of_roots_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (renaming : nat -> nat)
    baseWitnessList baseContext prefix coreRoot ruleRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs) prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename renaming
        coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise))
    coreRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename renaming
        coqStrongStepProofEndpointQuantifierBoundedEndpointPremise))
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
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawDirectTemplateFormula inputs
        (templateFormulaRename renaming
          coqStrongStepProofEndpointQuantifierBoundedConclusion))
      resultRoot.
Proof.
  intros M hPA inputs renaming baseWitnessList baseContext prefix
    coreRoot ruleRoot hprefix hbase hcore hrule.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct
    (raw_codedPALocalProof_strongStepProofEndpointQuantifierBoundedRenamedLaw_on_witnessed_base
      M hPA inputs renaming baseWitnessList baseContext hbase)
    as (witnesses & lawRoot & hextended & hlaw).
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
  change (RawCodedPALocalProofOf M extendedContext
    (rawTemplateFormula translation
      (templateFormulaRename renaming
        coqStrongStepProofEndpointQuantifierBoundedLawTemplate))
    lawRoot) in hlaw.
  destruct
    (raw_codedPALocalProof_twoPremiseLaw_on_witnessed_tail_under_prefix
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext prefix
      (templateFormulaRename renaming
        coqStrongStepProofEndpointQuantifierBoundedLawTemplate)
      (templateFormulaRename renaming
        coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise)
      (templateFormulaRename renaming
        coqStrongStepProofEndpointQuantifierBoundedEndpointPremise)
      (templateFormulaRename renaming
        coqStrongStepProofEndpointQuantifierBoundedConclusion)
      lawRoot coreRoot ruleRoot hprefix hbase hextended hincluded)
    as [resultRoot hresult].
  - rewrite
      coqStrongStepProofEndpointQuantifierBoundedLawTemplate_imp2_shape.
    cbn [templateFormulaRename]. reflexivity.
  - exact hlaw.
  - exact hcore.
  - exact hrule.
  - exists witnesses, resultRoot.
    split; [exact hextended |].
    split; [exact hincluded | exact hresult].
Qed.

(** Synchronize both endpoint invariants from actual renamed premise roots.
    This is the proof-root analogue of the later assumption-membership
    wrapper and the renaming-natural analogue of the unshifted synchronized
    endpoint.  Rank boundedness and atomic adequacy may select independent
    finite PA witness batches; the generic growing-pair combinator merges
    those batches without imposing equality on either producer.

    Stating the theorem for an arbitrary renaming makes it usable beneath any
    finite eigenvariable prefix.  In particular, guarded constructor parents
    can consume proof analyses retained below their five freshly opened
    variables instead of requiring the original shell formulas to remain
    literal assumptions. *)
Theorem
    raw_codedPALocalProof_strongStepEndpointEvidence_renamed_of_restricted_and_rule_roots_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (renaming : nat -> nat)
    baseWitnessList baseContext prefix restrictedRoot ruleRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs) prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename renaming
        coqRestrictedPADerivationSoundnessRestrictedProofTemplate))
    restrictedRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename renaming
        coqStrongStepProofEndpointAtomicAdequacyRulePremise))
    ruleRoot ->
  exists targetWitnessList targetContext atomicRoot rankRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext prefix)
      (rawDirectTemplateFormula inputs
        (templateFormulaRename renaming
          coqStrongStepProofEndpointAtomicAdequacyConclusion))
      atomicRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext prefix)
      (rawDirectTemplateFormula inputs
        (templateFormulaRename renaming
          coqStrongStepProofEndpointQuantifierBoundedConclusion))
      rankRoot.
Proof.
  intros M hPA inputs renaming baseWitnessList baseContext prefix
    restrictedRoot ruleRoot hprefix hbase hrestricted hrule.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct
    (raw_codedPALocalProof_restrictedProofTemplate_renamed_projections
      M hPA translation
      (rawTemplateContextCodeOnTail translation baseContext prefix)
      renaming restrictedRoot hrestricted) as
    (coreRoot & atomicPremiseRoot & formulaCoverageRoot &
      ruleCoverageRoot & hcore & hatomicPremise &
      _hformulaCoverage & _hruleCoverage).
  assert (hruleRank : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext prefix)
      (rawDirectTemplateFormula inputs
        (templateFormulaRename renaming
          coqStrongStepProofEndpointQuantifierBoundedEndpointPremise))
      ruleRoot).
  {
    rewrite <- coqStrongStepEndpointEvidence_rule_premises_agree.
    exact hrule.
  }
  destruct
    (raw_codedPALocalProof_strongStepProofEndpointAtomicAdequacy_renamed_of_roots_on_witnessed_tail_under_prefix
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      renaming baseWitnessList baseContext prefix
      atomicPremiseRoot ruleRoot hprefix hbase hatomicPremise hrule)
    as (atomicWitnessList & atomicContext & atomicRoot &
      hatomicWitnessed & hbaseAtomicIncluded & hatomic).
  assert (hatomicGrowing : RawCodedPAGrowingTemplateLocalProofAt M
      translation baseWitnessList baseContext prefix
      (rawDirectTemplateFormula inputs
        (templateFormulaRename renaming
          coqStrongStepProofEndpointAtomicAdequacyConclusion))).
  {
    exists atomicWitnessList, atomicContext, atomicRoot.
    split; [exact hatomicWitnessed |].
    split; [exact hbaseAtomicIncluded | exact hatomic].
  }
  destruct
    (raw_codedPALocalProof_strongStepProofEndpointQuantifierBounded_renamed_of_roots_on_witnessed_tail_under_prefix
      M hPA inputs renaming baseWitnessList baseContext prefix
      coreRoot ruleRoot hprefix hbase hcore hruleRank) as
    (rankWitnesses & rankRoot & hrankWitnessed &
      hbaseRankIncluded & hrank).
  assert (hrankGrowing : RawCodedPAGrowingTemplateLocalProofAt M
      translation baseWitnessList baseContext prefix
      (rawDirectTemplateFormula inputs
        (templateFormulaRename renaming
          coqStrongStepProofEndpointQuantifierBoundedConclusion))).
  {
    exists
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        rankWitnesses baseWitnessList),
      (rawStandardPAAxiomWitnessPrefixContextCode M
        rankWitnesses baseContext),
      rankRoot.
    split; [exact hrankWitnessed |].
    split; [exact hbaseRankIncluded | exact hrank].
  }
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_pair_at_prefix
      M hPA translation baseWitnessList baseContext prefix
      (rawDirectTemplateFormula inputs
        (templateFormulaRename renaming
          coqStrongStepProofEndpointAtomicAdequacyConclusion))
      (rawDirectTemplateFormula inputs
        (templateFormulaRename renaming
          coqStrongStepProofEndpointQuantifierBoundedConclusion))
      hatomicGrowing hrankGrowing).
Qed.

(** Compile the renamed rank-domain conclusion directly from inherited
    assumptions.  The restricted package projection supplies its hierarchy
    core, while the common rule-validity premise is a second assumption
    leaf in the same renamed prefix. *)
Corollary
    raw_codedPALocalProof_strongStepProofEndpointQuantifierBounded_renamed_of_template_assumptions_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (renaming : nat -> nat)
    baseWitnessList baseContext prefix,
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs) prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  In (templateFormulaRename renaming
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    prefix ->
  In (templateFormulaRename renaming
      coqStrongStepProofEndpointQuantifierBoundedEndpointPremise)
    prefix ->
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
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawDirectTemplateFormula inputs
        (templateFormulaRename renaming
          coqStrongStepProofEndpointQuantifierBoundedConclusion))
      resultRoot.
Proof.
  intros M hPA inputs renaming baseWitnessList baseContext prefix
    hprefix hbase hrestrictedIn hruleIn.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct
    (raw_codedPALocalProof_restrictedProofTemplate_renamed_projections_of_template_assumption
      M hPA translation baseWitnessList baseContext prefix renaming
      hbase hrestrictedIn)
    as (coreRoot & atomicRoot & formulaCoverageRoot &
      ruleCoverageRoot & hcore & hatomic &
      hformulaCoverage & hruleCoverage).
  pose proof
    (raw_templateAssumptionOnPAAxiomContext_localProof
      M hPA translation baseWitnessList baseContext prefix
      (templateFormulaRename renaming
        coqStrongStepProofEndpointQuantifierBoundedEndpointPremise)
      hbase hruleIn) as hrule.
  lazymatch type of hrule with
  | RawCodedPALocalProofOf _ _ _ ?ruleRoot =>
      exact
        (raw_codedPALocalProof_strongStepProofEndpointQuantifierBounded_renamed_of_roots_on_witnessed_tail_under_prefix
          M hPA inputs renaming baseWitnessList baseContext prefix
          coreRoot ruleRoot hprefix hbase hcore hrule)
  end.
Qed.

(** Binder-count form matching the direct predecessor closure. *)
Corollary
    raw_codedPALocalProof_strongStepProofEndpointQuantifierBounded_of_template_assumptions_after_binders_on_witnessed_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    binderCount baseWitnessList baseContext callerPrefix,
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (templateContextShiftMany binderCount callerPrefix) ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
    callerPrefix ->
  In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
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
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext)
        (templateContextShiftMany binderCount callerPrefix))
      (rawDirectTemplateFormula inputs
        (templateFormulaRename
          (templateShiftRenamingMany binderCount)
          coqStrongStepProofEndpointQuantifierBoundedConclusion))
      resultRoot.
Proof.
  intros M hPA inputs binderCount baseWitnessList baseContext
    callerPrefix hprefix hbase hrestrictedIn hruleIn.
  apply
    (raw_codedPALocalProof_strongStepProofEndpointQuantifierBounded_renamed_of_template_assumptions_on_witnessed_tail_under_prefix
      M hPA inputs (templateShiftRenamingMany binderCount)
      baseWitnessList baseContext
      (templateContextShiftMany binderCount callerPrefix)
      hprefix hbase).
  - rewrite <- templateFormulaShiftMany_as_rename.
    exact (templateContextShiftMany_member binderCount callerPrefix
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate
      hrestrictedIn).
  - rewrite <- templateFormulaShiftMany_as_rename.
    apply (templateContextShiftMany_member binderCount callerPrefix
      coqStrongStepProofEndpointQuantifierBoundedEndpointPremise).
    rewrite <- coqStrongStepEndpointEvidence_rule_premises_agree.
    exact hruleIn.
Qed.

(** Synchronize both renamed endpoint conclusions after any finite binder
    prefix.  Rank boundedness is compiled first; atomic adequacy then grows
    that witnessed PA tail once more, and the rank root is transported to
    the final tail under the identical shifted caller prefix.  Consequently
    callers receive both roots in one literal context and need provide only
    membership of the two original direct-shell assumptions. *)
Theorem
    raw_codedPALocalProof_strongStepEndpointEvidence_of_template_assumptions_after_binders_on_witnessed_tail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    binderCount baseWitnessList baseContext callerPrefix,
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    (templateContextShiftMany binderCount callerPrefix) ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  In coqRestrictedPADerivationSoundnessRestrictedProofTemplate
    callerPrefix ->
  In coqStrongStepProofEndpointAtomicAdequacyRulePremise callerPrefix ->
  exists targetWitnessList targetContext atomicRoot rankRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M baseContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext
        (templateContextShiftMany binderCount callerPrefix))
      (rawDirectTemplateFormula inputs
        (templateFormulaRename
          (templateShiftRenamingMany binderCount)
          coqStrongStepProofEndpointAtomicAdequacyConclusion))
      atomicRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        targetContext
        (templateContextShiftMany binderCount callerPrefix))
      (rawDirectTemplateFormula inputs
        (templateFormulaRename
          (templateShiftRenamingMany binderCount)
          coqStrongStepProofEndpointQuantifierBoundedConclusion))
      rankRoot.
Proof.
  intros M hPA inputs binderCount baseWitnessList baseContext
    callerPrefix hprefix hbase hrestrictedIn hruleIn.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (renaming := templateShiftRenamingMany binderCount).
  set (shiftedPrefix :=
    templateContextShiftMany binderCount callerPrefix).
  destruct
    (raw_codedPALocalProof_strongStepProofEndpointQuantifierBounded_of_template_assumptions_after_binders_on_witnessed_tail
      M hPA inputs binderCount baseWitnessList baseContext callerPrefix
      hprefix hbase hrestrictedIn hruleIn)
    as (rankWitnesses & rankRoot & hrankWitnessed &
      hbaseRankIncluded & hrank).
  set (rankWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      rankWitnesses baseWitnessList).
  set (rankContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      rankWitnesses baseContext).
  destruct
    (raw_codedPALocalProof_strongStepProofEndpointAtomicAdequacy_of_template_assumptions_after_binders_on_witnessed_tail
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      binderCount rankWitnessList rankContext callerPrefix
      hprefix hrankWitnessed hrestrictedIn hruleIn)
    as (targetWitnessList & targetContext & atomicRoot &
      htargetWitnessed & hrankTargetIncluded & hatomic).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation rankWitnessList rankContext
      targetWitnessList targetContext shiftedPrefix
      (rawDirectTemplateFormula inputs
        (templateFormulaRename renaming
          coqStrongStepProofEndpointQuantifierBoundedConclusion))
      rankRoot hrankWitnessed htargetWitnessed
      hrankTargetIncluded hrank)
    as [rankOnTargetRoot hrankOnTarget].
  exists targetWitnessList, targetContext, atomicRoot, rankOnTargetRoot.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hrankTargetIncluded member
      (hbaseRankIncluded member hmember)).
  - split; assumption.
Qed.

(** Rank-domain specialization of the generic under-prefix law. *)
Theorem
    raw_codedPALocalProof_strongStepProofEndpointQuantifierBounded_of_roots_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext prefix coreRoot ruleRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs) prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise)
    coreRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointQuantifierBoundedEndpointPremise)
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
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedConclusion)
      resultRoot.
Proof.
  intros M hPA inputs baseWitnessList baseContext prefix
    coreRoot ruleRoot hprefix hbase hcore hrule.
  destruct
    (raw_codedPALocalProof_strongStepProofEndpointQuantifierBounded_renamed_of_roots_on_witnessed_tail_under_prefix
      M hPA inputs (fun index => index)
      baseWitnessList baseContext prefix coreRoot ruleRoot
      hprefix hbase) as (witnesses & resultRoot &
        hextended & hincluded & hresult).
  - rewrite !templateFormulaRename_id.
    exact hcore.
  - rewrite !templateFormulaRename_id.
    exact hrule.
  - rewrite !templateFormulaRename_id in hresult.
  exists witnesses, resultRoot.
  split; [exact hextended |].
  split; [exact hincluded | exact hresult].
Qed.

(** Atomic-adequacy specialization of the same reusable law application. *)
Theorem
    raw_codedPALocalProof_strongStepProofEndpointAtomicAdequacy_of_roots_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext prefix atomicRoot ruleRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs) prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
    atomicRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
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
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyConclusion)
      resultRoot.
Proof.
  intros M hPA inputs baseWitnessList baseContext prefix
    atomicRoot ruleRoot hprefix hbase hatomic hrule.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct
    (raw_codedPALocalProof_strongStepProofEndpointAtomicAdequacyLaw_on_witnessed_base
      M hPA inputs baseWitnessList baseContext hbase)
    as (witnesses & lawRoot & hextended & hlaw).
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
  change (RawCodedPALocalProofOf M extendedContext
    (rawTemplateFormula translation
      coqStrongStepProofEndpointAtomicAdequacyLawTemplate)
    lawRoot) in hlaw.
  destruct
    (raw_codedPALocalProof_twoPremiseLaw_on_witnessed_tail_under_prefix
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext prefix
      coqStrongStepProofEndpointAtomicAdequacyLawTemplate
      coqStrongStepProofEndpointAtomicAdequacyAtomicPremise
      coqStrongStepProofEndpointAtomicAdequacyRulePremise
      coqStrongStepProofEndpointAtomicAdequacyConclusion
      lawRoot atomicRoot ruleRoot hprefix hbase hextended hincluded
      coqStrongStepProofEndpointAtomicAdequacyLawTemplate_imp2_shape
      hlaw hatomic hrule)
    as [resultRoot hresult].
  exists witnesses, resultRoot.
  split; [exact hextended |].
  split; [exact hincluded | exact hresult].
Qed.

(** Run the rank compiler, then the atomic compiler over the rank extension.
    The returned prefix is [atomicPrefix ++ rankPrefix], matching the literal
    composition order of the two prefix folds. *)
Theorem raw_codedPALocalProof_strongStepEndpointEvidence_of_roots : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext coreRoot atomicRoot ruleRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise)
    coreRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
    atomicRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyRulePremise)
    ruleRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix)
      atomicResultRoot rankResultRoot,
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
      atomicResultRoot /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedConclusion)
      rankResultRoot.
Proof.
  intros M hPA inputs baseWitnessList baseContext
    coreRoot atomicRoot ruleRoot hbase hcore hatomic hrule.
  assert (hruleRank : RawCodedPALocalProofOf M baseContext
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedEndpointPremise)
      ruleRoot).
  {
    rewrite <- coqStrongStepEndpointEvidence_rule_premises_agree.
    exact hrule.
  }
  destruct
    (raw_codedPALocalProof_strongStepProofEndpointQuantifierBounded_of_roots_on_witnessed_extension
      M hPA inputs baseWitnessList baseContext coreRoot ruleRoot
      hbase hcore hruleRank)
    as (rankPrefix & rankResultRoot & hrankBase & hincludedRank & hrank).
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (rankWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      rankPrefix baseWitnessList).
  set (rankContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      rankPrefix baseContext).
  assert (hatomicOnEmptyPrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext [])
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
      atomicRoot).
  { cbn [rawTemplateContextCodeOnTail]. exact hatomic. }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      rankWitnessList rankContext []
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
      atomicRoot hbase hrankBase hincludedRank hatomicOnEmptyPrefix)
    as [atomicOnRankRoot hatomicOnRank].
  cbn [rawTemplateContextCodeOnTail] in hatomicOnRank.
  assert (hruleOnEmptyPrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext [])
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)
      ruleRoot).
  { cbn [rawTemplateContextCodeOnTail]. exact hrule. }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      rankWitnessList rankContext []
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)
      ruleRoot hbase hrankBase hincludedRank hruleOnEmptyPrefix)
    as [ruleOnRankRoot hruleOnRank].
  cbn [rawTemplateContextCodeOnTail] in hruleOnRank.
  destruct
    (raw_codedPALocalProof_strongStepProofEndpointAtomicAdequacy_of_roots_on_witnessed_extension
      M hPA inputs rankWitnessList rankContext
      atomicOnRankRoot ruleOnRankRoot
      hrankBase hatomicOnRank hruleOnRank)
    as (atomicPrefix & atomicResultRoot & hatomicBase &
      hincludedAtomic & hatomicResult).
  set (finalWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      atomicPrefix rankWitnessList).
  set (finalContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      atomicPrefix rankContext).
  assert (hrankOnEmptyPrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation rankContext [])
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedConclusion)
      rankResultRoot).
  { cbn [rawTemplateContextCodeOnTail]. exact hrank. }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation rankWitnessList rankContext
      finalWitnessList finalContext []
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedConclusion)
      rankResultRoot hrankBase hatomicBase hincludedAtomic
      hrankOnEmptyPrefix)
    as [rankOnFinalRoot hrankOnFinal].
  cbn [rawTemplateContextCodeOnTail] in hrankOnFinal.
  exists (atomicPrefix ++ rankPrefix),
    atomicResultRoot, rankOnFinalRoot.
  rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
  rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
  change (RawCodedPAAxiomWitnessContext M finalWitnessList finalContext /\
    RawContextListIncluded M baseContext finalContext /\
    RawCodedPALocalProofOf M finalContext
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyConclusion)
      atomicResultRoot /\
    RawCodedPALocalProofOf M finalContext
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedConclusion)
      rankOnFinalRoot).
  split; [exact hatomicBase |].
  split.
  - intros member hmember.
    exact (hincludedAtomic member (hincludedRank member hmember)).
  - split; [exact hatomicResult | exact hrankOnFinal].
Qed.

(** Prefix-preserving counterpart used by the direct soundness shell. *)
Theorem
    raw_codedPALocalProof_strongStepEndpointEvidence_of_roots_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext prefix coreRoot atomicRoot ruleRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs) prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise)
    coreRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
    atomicRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyRulePremise)
    ruleRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix)
      atomicResultRoot rankResultRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyConclusion)
      atomicResultRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedConclusion)
      rankResultRoot.
Proof.
  intros M hPA inputs baseWitnessList baseContext prefix
    coreRoot atomicRoot ruleRoot hprefix hbase hcore hatomic hrule.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  assert (hruleRank : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext prefix)
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedEndpointPremise)
      ruleRoot).
  {
    rewrite <- coqStrongStepEndpointEvidence_rule_premises_agree.
    exact hrule.
  }
  destruct
    (raw_codedPALocalProof_strongStepProofEndpointQuantifierBounded_of_roots_on_witnessed_tail_under_prefix
      M hPA inputs baseWitnessList baseContext prefix coreRoot ruleRoot
      hprefix hbase hcore hruleRank)
    as (rankPrefix & rankResultRoot & hrankBase & hincludedRank & hrank).
  set (rankWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      rankPrefix baseWitnessList).
  set (rankContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      rankPrefix baseContext).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      rankWitnessList rankContext prefix
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
      atomicRoot hbase hrankBase hincludedRank hatomic)
    as [atomicOnRankRoot hatomicOnRank].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation baseWitnessList baseContext
      rankWitnessList rankContext prefix
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyRulePremise)
      ruleRoot hbase hrankBase hincludedRank hrule)
    as [ruleOnRankRoot hruleOnRank].
  destruct
    (raw_codedPALocalProof_strongStepProofEndpointAtomicAdequacy_of_roots_on_witnessed_tail_under_prefix
      M hPA inputs rankWitnessList rankContext prefix
      atomicOnRankRoot ruleOnRankRoot
      hprefix hrankBase hatomicOnRank hruleOnRank)
    as (atomicPrefix & atomicResultRoot & hatomicBase &
      hincludedAtomic & hatomicResult).
  set (finalWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      atomicPrefix rankWitnessList).
  set (finalContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      atomicPrefix rankContext).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation rankWitnessList rankContext
      finalWitnessList finalContext prefix
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedConclusion)
      rankResultRoot hrankBase hatomicBase hincludedAtomic hrank)
    as [rankOnFinalRoot hrankOnFinal].
  exists (atomicPrefix ++ rankPrefix),
    atomicResultRoot, rankOnFinalRoot.
  rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
  rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
  change (RawCodedPAAxiomWitnessContext M finalWitnessList finalContext /\
    RawContextListIncluded M baseContext finalContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation finalContext prefix)
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyConclusion)
      atomicResultRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation finalContext prefix)
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedConclusion)
      rankOnFinalRoot).
  split; [exact hatomicBase |].
  split.
  - intros member hmember.
    exact (hincludedAtomic member (hincludedRank member hmember)).
  - split; [exact hatomicResult | exact hrankOnFinal].
Qed.

(** Project the core and proof-wide atomic certificate from the direct
    restricted-proof conjunction, then invoke the synchronized compiler. *)
Theorem
    raw_codedPALocalProof_strongStepEndpointEvidence_of_restricted_and_rule_roots :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext restrictedRoot ruleRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    restrictedRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyRulePremise)
    ruleRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix)
      atomicResultRoot rankResultRoot,
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
      atomicResultRoot /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedConclusion)
      rankResultRoot.
Proof.
  intros M hPA inputs baseWitnessList baseContext
    restrictedRoot ruleRoot hbase hrestricted hrule.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  change (RawCodedPALocalProofOf M baseContext
    (rawTemplateFormula translation
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    restrictedRoot) in hrestricted.
  destruct
    (raw_codedPALocalProof_restrictedProofTemplate_projections
      M hPA translation baseContext restrictedRoot hrestricted)
    as (coreRoot & atomicRoot & formulaCoverageRoot &
      ruleCoverageRoot & hcore & hatomic &
      _ & _).
  exact
    (raw_codedPALocalProof_strongStepEndpointEvidence_of_roots
      M hPA inputs baseWitnessList baseContext
      coreRoot atomicRoot ruleRoot
      hbase hcore hatomic hrule).
Qed.

(** Fully shell-compatible wrapper: both assumptions remain beneath the
    caller's temporary prefix while only the witnessed PA tail grows. *)
Theorem
    raw_codedPALocalProof_strongStepEndpointEvidence_of_restricted_and_rule_roots_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext prefix restrictedRoot ruleRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M
    (rawDirectStructuralTemplateTranslation M hPA inputs) prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    restrictedRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      baseContext prefix)
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointAtomicAdequacyRulePremise)
    ruleRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix)
      atomicResultRoot rankResultRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyConclusion)
      atomicResultRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointQuantifierBoundedConclusion)
      rankResultRoot.
Proof.
  intros M hPA inputs baseWitnessList baseContext prefix
    restrictedRoot ruleRoot hprefix hbase hrestricted hrule.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (localContext :=
    rawTemplateContextCodeOnTail translation baseContext prefix).
  change (RawCodedPALocalProofOf M localContext
    (rawTemplateFormula translation
      coqRestrictedPADerivationSoundnessRestrictedProofTemplate)
    restrictedRoot) in hrestricted.
  destruct
    (raw_codedPALocalProof_restrictedProofTemplate_projections
      M hPA translation localContext restrictedRoot hrestricted)
    as (coreRoot & atomicRoot & formulaCoverageRoot &
      ruleCoverageRoot & hcore & hatomic &
      _ & _).
  exact
    (raw_codedPALocalProof_strongStepEndpointEvidence_of_roots_on_witnessed_tail_under_prefix
      M hPA inputs baseWitnessList baseContext prefix
      coreRoot atomicRoot ruleRoot
      hprefix hbase hcore hatomic hrule).
Qed.

End PABoundedRawCodedStrongStepProofEndpointEvidenceCompilation.
