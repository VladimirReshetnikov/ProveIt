(**
  Arbitrary-root append-existence adapter for the direct soundness rows.

  The native row compiler used to expose the append-existence proof as an
  independent residual.  That proof is not a native-truth obligation: it is
  an instance of the closed PA theorem for simultaneous beta-table
  extension.  This file packages the corresponding transport once and for
  all.  The caller may still choose an arbitrary finite standard prefix and
  arbitrary template root terms; the resulting proof is returned on the
  exact prefixed context, not on a hidden or contracted context.

  The inherited-row implication remains deliberately separate.  Its roots
  mention the opaque native predicates and cannot be manufactured from the
  closed append theorem alone.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedPAProofLeafCertificates
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateProofCompiler
  RawCodedTemplateSyntax
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedFourStateTableAppendProofCompilation
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.

Import ListNotations.

Module PABoundedRawCodedRestrictedPADirectAppendExistenceAdapter.

Import PA.
Import PABoundedCodedProof.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPAProofLeafCertificates.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionAlignedTruthProduction.

(** A direct translation presents any finite standard PA prefix as a genuine
    witnessed context.  The same lemma is used by the native row modules,
    but spelling it here keeps the adapter independent of their semantic
    resources. *)
Lemma raw_directAppendExistence_witnessed_context : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) witnesses,
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (embedPAContext (map witnessedAxiom witnesses))).
Proof.
  intros M hPA inputs witnesses.
  exact (raw_directEmbeddedPAAxiomWitnessContext M hPA inputs witnesses).
Qed.

(** The append theorem is first compiled on the empty standard tail.  Its
    selected prefix is then placed *inside* the caller prefix by witnessed
    context weakening.  This order is important: direct rows use
    [baseWitnesses ++ suffix], whereas the generic PA compiler prepends the
    prefix supplied to its base context. *)
Theorem raw_directAppendExistence_on_standard_tail : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  forall (baseWitnesses : StandardPAAxiomWitnessPrefix)
    (boundName : TemplateParameterName) (rootMode : nat)
    (rootFormula rootAssignmentCode rootAssignmentStep : TemplateTerm),
  exists suffix : StandardPAAxiomWitnessPrefix, exists appendRoot : M,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        (baseWitnesses ++ suffix) (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext
          (map witnessedAxiom (baseWitnesses ++ suffix)))) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext
          (map witnessedAxiom (baseWitnesses ++ suffix))))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqFourStateTableAppendExistsTemplate
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter boundName)
          (embedPATerm (Term.numeral rootMode))
          rootFormula rootAssignmentCode rootAssignmentStep)) appendRoot.
Proof.
  intros M hPA inputs baseWitnesses boundName rootMode
    rootFormula rootAssignmentCode rootAssignmentStep.
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  set (agreement := rawDirectStructuralTemplatePAAgreement M hPA inputs).
  set (emptyWitnessList := raw_zero M).
  set (emptyContext := raw_zero M).
  assert (hempty : RawCodedPAAxiomWitnessContext M
      emptyWitnessList emptyContext).
  {
    unfold emptyWitnessList, emptyContext.
    exact (raw_codedPAAxiomWitnessContext_empty M hPA).
  }
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_exists_on_witnessed_tail_of_defined_instances
      M hPA translation agreement
      emptyWitnessList emptyContext boundName rootMode
      rootFormula rootAssignmentCode rootAssignmentStep
      (coqFourStateTableAppendCanonicalDefinedTemplate_instances
        boundName rootMode)
      hempty)
    as (appendWitnesses & appendRoot & happendWitnessed & happend).
  set (appendContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      appendWitnesses emptyContext).
  set (targetWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      baseWitnesses
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        appendWitnesses emptyWitnessList)).
  set (targetContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      baseWitnesses appendContext).
  assert (htargetWitnessed : RawCodedPAAxiomWitnessContext M
      targetWitnessList targetContext).
  {
    unfold targetWitnessList, targetContext, appendContext.
    exact (raw_codedPAAxiomWitnessContext_standardPrefix M hPA
      baseWitnesses
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        appendWitnesses emptyWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        appendWitnesses emptyContext)
      happendWitnessed).
  }
  assert (happendIncluded : RawContextListIncluded M
      appendContext targetContext).
  {
    unfold targetContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA baseWitnesses appendContext).
  }
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        appendWitnesses emptyWitnessList)
      appendContext targetWitnessList targetContext
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter boundName)
          (embedPATerm (Term.numeral rootMode))
          rootFormula rootAssignmentCode rootAssignmentStep))
      appendRoot happendWitnessed htargetWitnessed happendIncluded happend)
    as [transportedRoot htransported].
  exists appendWitnesses, transportedRoot.
  split.
  - unfold targetWitnessList, targetContext, appendContext,
      translation in htargetWitnessed |- *.
    rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
    assert (hcontext : rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext
          (map witnessedAxiom (baseWitnesses ++ appendWitnesses))) =
      rawStandardPAAxiomWitnessPrefixContextCode M
        (baseWitnesses ++ appendWitnesses) (raw_zero M)).
    {
      rewrite rawTemplateContextCode_as_on_tail.
      apply (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
        M (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawDirectStructuralTemplatePAAgreement M hPA inputs)
        (baseWitnesses ++ appendWitnesses) (raw_zero M)).
    }
    rewrite hcontext.
    rewrite <- rawStandardPAAxiomWitnessPrefixContextCode_app
      in htargetWitnessed.
    exact htargetWitnessed.
  - assert (htargetContext : targetContext =
        rawTemplateContextCode translation
          (embedPAContext
            (map witnessedAxiom (baseWitnesses ++ appendWitnesses)))).
    {
      unfold targetContext, appendContext, emptyContext.
      rewrite <- rawStandardPAAxiomWitnessPrefixContextCode_app.
      rewrite rawTemplateContextCode_as_on_tail.
      symmetry.
      apply (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
        M translation agreement (baseWitnesses ++ appendWitnesses)
        (raw_zero M)).
    }
    rewrite <- htargetContext.
    exact htransported.
Qed.

(** Specialize the adapter to the exact root layout of the mode-zero direct
    row.  This is the resource shape consumed by the direct production
    compiler; only its inherited-row implication remains a semantic input. *)
Corollary raw_directModeZeroAppendExistence_on_standard_tail : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (baseWitnesses : StandardPAAxiomWitnessPrefix),
  exists suffix : StandardPAAxiomWitnessPrefix, exists appendRoot : M,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        (baseWitnesses ++ suffix) (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext
          (map witnessedAxiom (baseWitnesses ++ suffix)))) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext
          (map witnessedAxiom (baseWitnesses ++ suffix))))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqFourStateTableAppendExistsTemplate
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral 0))
          (ttVar 0) (ttVar 1) (ttVar 2))) appendRoot.
Proof.
  intros M hPA inputs baseWitnesses.
  exact (raw_directAppendExistence_on_standard_tail
    M hPA inputs baseWitnesses
    coqDynamicTruthAppendRowBoundParameterName 0
    (ttVar 0) (ttVar 1) (ttVar 2)).
Qed.

End PABoundedRawCodedRestrictedPADirectAppendExistenceAdapter.
