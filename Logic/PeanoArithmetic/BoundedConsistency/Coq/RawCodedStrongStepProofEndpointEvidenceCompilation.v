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
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedProofRuleCoverage
  RawCodedRestrictedPAProof
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPAAxiomWitnessPrefix
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
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
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
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct
    (raw_codedPALocalProof_strongStepProofEndpointQuantifierBoundedLaw_on_witnessed_base
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
      coqStrongStepProofEndpointQuantifierBoundedLawTemplate)
    lawRoot) in hlaw.
  destruct
    (raw_codedPALocalProof_twoPremiseLaw_on_witnessed_tail_under_prefix
      M hPA translation baseWitnessList baseContext
      extendedWitnessList extendedContext prefix
      coqStrongStepProofEndpointQuantifierBoundedLawTemplate
      coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise
      coqStrongStepProofEndpointQuantifierBoundedEndpointPremise
      coqStrongStepProofEndpointQuantifierBoundedConclusion
      lawRoot coreRoot ruleRoot hprefix hbase hextended hincluded
      coqStrongStepProofEndpointQuantifierBoundedLawTemplate_imp2_shape
      hlaw hcore hrule)
    as [resultRoot hresult].
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
  rewrite coqRestrictedPADerivationSoundnessRestrictedProofTemplate_view
    in hrestricted.
  rewrite !rawTemplateFormula_and in hrestricted.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA baseContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise)
    (rawFormulaAndCode M
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
      (rawFormulaAndCode M
        (rawDirectTemplateFormula inputs
          (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 4))))
        (rawDirectTemplateFormula inputs
          (embedPAFormula (proofRuleCoverageTermAt (tVar 4))))))
    restrictedRoot hrestricted) as hcore.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA baseContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise)
    (rawFormulaAndCode M
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
      (rawFormulaAndCode M
        (rawDirectTemplateFormula inputs
          (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 4))))
        (rawDirectTemplateFormula inputs
          (embedPAFormula (proofRuleCoverageTermAt (tVar 4))))))
    restrictedRoot hrestricted) as hcertificates.
  lazymatch type of hcertificates with
  | RawCodedPALocalProofOf _ _ _ ?certificatesRoot =>
      pose proof (raw_codedPALocalProofOf_andE1 M hPA baseContext
        (rawDirectTemplateFormula inputs
          coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
        (rawFormulaAndCode M
          (rawDirectTemplateFormula inputs
            (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 4))))
          (rawDirectTemplateFormula inputs
            (embedPAFormula (proofRuleCoverageTermAt (tVar 4)))))
        certificatesRoot hcertificates) as hatomic;
      lazymatch type of hcore with
      | RawCodedPALocalProofOf _ _ _ ?coreRoot =>
          lazymatch type of hatomic with
          | RawCodedPALocalProofOf _ _ _ ?atomicRoot =>
              exact
                (raw_codedPALocalProof_strongStepEndpointEvidence_of_roots
                  M hPA inputs baseWitnessList baseContext
                  coreRoot atomicRoot ruleRoot
                  hbase hcore hatomic hrule)
          end
      end
  end.
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
  rewrite coqRestrictedPADerivationSoundnessRestrictedProofTemplate_view
    in hrestricted.
  rewrite !rawTemplateFormula_and in hrestricted.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA localContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise)
    (rawFormulaAndCode M
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
      (rawFormulaAndCode M
        (rawDirectTemplateFormula inputs
          (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 4))))
        (rawDirectTemplateFormula inputs
          (embedPAFormula (proofRuleCoverageTermAt (tVar 4))))))
    restrictedRoot hrestricted) as hcore.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA localContext
    (rawDirectTemplateFormula inputs
      coqStrongStepProofEndpointQuantifierBoundedRestrictedPremise)
    (rawFormulaAndCode M
      (rawDirectTemplateFormula inputs
        coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
      (rawFormulaAndCode M
        (rawDirectTemplateFormula inputs
          (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 4))))
        (rawDirectTemplateFormula inputs
          (embedPAFormula (proofRuleCoverageTermAt (tVar 4))))))
    restrictedRoot hrestricted) as hcertificates.
  lazymatch type of hcertificates with
  | RawCodedPALocalProofOf _ _ _ ?certificatesRoot =>
      pose proof (raw_codedPALocalProofOf_andE1 M hPA localContext
        (rawDirectTemplateFormula inputs
          coqStrongStepProofEndpointAtomicAdequacyAtomicPremise)
        (rawFormulaAndCode M
          (rawDirectTemplateFormula inputs
            (embedPAFormula (proofHasFormulaCoverageTermAt (tVar 4))))
          (rawDirectTemplateFormula inputs
            (embedPAFormula (proofRuleCoverageTermAt (tVar 4)))))
        certificatesRoot hcertificates) as hatomic;
      lazymatch type of hcore with
      | RawCodedPALocalProofOf _ _ _ ?coreRoot =>
          lazymatch type of hatomic with
          | RawCodedPALocalProofOf _ _ _ ?atomicRoot =>
              exact
                (raw_codedPALocalProof_strongStepEndpointEvidence_of_roots_on_witnessed_tail_under_prefix
                  M hPA inputs baseWitnessList baseContext prefix
                  coreRoot atomicRoot ruleRoot
                  hprefix hbase hcore hatomic hrule)
          end
      end
  end.
Qed.

End PABoundedRawCodedStrongStepProofEndpointEvidenceCompilation.
