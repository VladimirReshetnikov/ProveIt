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
  RawCodedSyntaxConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedProofRuleCoverage
  RawCodedRestrictedPAProof
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPAAxiomWitnessPrefix
  RawCodedProofEndpointQuantifierBoundedProofCompilation
  RawCodedStrongStepProofEndpointQuantifierBoundedProofCompilation
  RawCodedStrongStepProofEndpointAtomicAdequacyProofCompilation.

Import ListNotations.

Module PABoundedRawCodedStrongStepProofEndpointEvidenceCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
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

End PABoundedRawCodedStrongStepProofEndpointEvidenceCompilation.
