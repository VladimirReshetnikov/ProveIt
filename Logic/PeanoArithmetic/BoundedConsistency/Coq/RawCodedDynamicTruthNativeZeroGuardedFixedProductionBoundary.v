(**
  Isolate the caller-independent guarded rank-zero row boundary.

  The guarded implication opens five constructor variables before its local
  truth applications are used.  Consequently the relevant application tuple
  is [child, assignmentCode, assignmentStep] = [#2,#6,#5], not the historical
  permuted tuple [#2,#1,#0].  This module records two facts about that change:

  - an arbitrary caller suffix is purely structural and can be inserted by
    the generic root-term append compiler; hence the only source obligation
    is the pair of mode compilers at the fixed guarded prefix; and
  - the historical and guarded temporary append contexts are syntactically
    different.  Thus an old proof root cannot be reused by a conclusion
    rewrite or a same-prefix tail transport.

  The second statement is deliberately only a syntax obstruction.  It does
  not claim a metatheoretic non-derivability result; a genuine represented
  substitution/renaming compiler could still bridge the contexts.  No such
  general raw-proof-code compiler is currently part of the development.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateBottomDirectStructuralInputs
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedPAGrowingTemplateRebase
  RawCodedLtSuccCasesProofCompilation
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedFourStateTableAppendGlobalTraversalAssembly
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation
  RawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification
  RawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification
  RawCodedDynamicTruthBooleanGuardedBranchExclusivity
  RawCodedDynamicTruthBooleanGuardedDiagonalCompilation
  RawCodedDynamicTruthNativeZeroBooleanGuardedParentCompilation
  RawCodedStrongStepPredecessorGlobalRowEvidenceCompilation
  RawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeZeroGuardedFixedProductionBoundary.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateBottomDirectStructuralInputs.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedPAGrowingTemplateRebase.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import
  PABoundedRawCodedDynamicTruthImpGuardedPredecessorExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification.
Import PABoundedRawCodedDynamicTruthBooleanGuardedBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBooleanGuardedDiagonalCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroBooleanGuardedParentCompilation.
Import
  PABoundedRawCodedStrongStepPredecessorGlobalRowEvidenceCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedPredecessorCompilation.

(** The rank-zero inherited branch needs no special interpretation for its
    opaque truth atoms.  Its only translation-sensitive fact is that the
    reserved append bound denotes the literal term zero.  State that bridge
    for an arbitrary direct structural input package, so the guarded
    selector translation need not be replaced by the unrelated bottom
    translation. *)
Lemma raw_dynamicTruthZeroCanonicalDirect_append_below_parameter_zero :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateTerm inputs
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) =
    rawQuotedTermCode M tZero ->
  rawTemplateFormula (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqLtSuccCasesBelowTemplate
      (ttVar 4)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)) =
  rawTemplateFormula (rawDirectStructuralTemplateTranslation M hPA inputs)
    (coqNoLtZeroAntecedentTemplate (ttVar 4)).
Proof.
  intros M hPA inputs hbound.
  rewrite coqNoLtZeroAntecedentTemplate_append_below_zero.
  change
    (rawDirectTemplateFormula inputs
      (coqLtSuccCasesBelowTemplate
        (ttVar 4)
        (ttParameter coqDynamicTruthAppendRowBoundParameterName)) =
     rawDirectTemplateFormula inputs
      (coqLtSuccCasesBelowTemplate (ttVar 4) ttZero)).
  unfold rawDirectTemplateTerm in hbound.
  vm_compute.
  vm_compute in hbound.
  rewrite hbound.
  reflexivity.
Qed.

(** Translation-coherent form of the vacuous inherited-row producer.  This
    is the bottom-specialized construction from append-source identification
    with its genuine dependency exposed: direct structural adequacy supplies
    every arithmetic atom, and [hbound] alone identifies the row bound with
    zero.  In particular, opaque guarded evidence selectors remain intact. *)
Theorem
    raw_dynamicTruthZeroCanonicalDirect_appendInheritedRowResourcesAtRootTermsUnderPrefix_on_standardWitnessTail_of_append_root :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateTerm inputs
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) =
    rawQuotedTermCode M tZero ->
  forall rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep
    appendWitnesses appendRoot,
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      appendWitnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      appendWitnesses (raw_zero M)) ->
  RawCodedPALocalProofOf M
    (rawStandardPAAxiomWitnessPrefixContextCode M
      appendWitnesses (raw_zero M))
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthZeroCanonicalAppendExistsTemplateAtRootTerms
        rootMode rootFormula rootAssignmentCode rootAssignmentStep))
    appendRoot ->
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) /\
    RawDynamicTruthZeroCanonicalAppendInheritedRowResourcesAtRootTermsUnderPrefixAt
      M (rawDirectStructuralTemplateTranslation M hPA inputs)
      rootMode outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep witnesses.
Proof.
  intros M hPA inputs hbound rootMode outerPrefix
    rootFormula rootAssignmentCode rootAssignmentStep
    appendWitnesses appendRoot happendWitnessed happend.
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  set (rowPrefix :=
    coqDynamicTruthZeroCanonicalAppendRowContextAtRootTerms
      rootMode rootFormula rootAssignmentCode rootAssignmentStep outerPrefix).
  destruct
    (raw_codedPALocalProofOf_below_zero_imp_ignored_imp_on_witnessed_tail_under_prefix
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        appendWitnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        appendWitnesses (raw_zero M))
      (templateContextShiftMany 5 rowPrefix) (ttVar 4)
      coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate
      (templateFormulaShiftMany 5
        (coqFourStateTableAppendConcreteClosedRowProductionTemplate
          (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
          (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)))
      (raw_directStructuralTemplatePrefix_atomically_adequate
        M hPA inputs (templateContextShiftMany 5 rowPrefix))
      ((raw_directStructuralTemplatePrefix_atomically_adequate
          M hPA inputs [coqNoLtZeroAntecedentTemplate (ttVar 4)])
        (coqNoLtZeroAntecedentTemplate (ttVar 4))
        (or_introl eq_refl))
      ((raw_directStructuralTemplatePrefix_atomically_adequate
          M hPA inputs
          [coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate])
        coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate
        (or_introl eq_refl))
      happendWitnessed)
    as (traversalWitnesses & bodyRoot & hfinalWitnessed & hbody).
  set (finalWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      traversalWitnesses
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        appendWitnesses (raw_zero M))).
  set (finalContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      traversalWitnesses
      (rawStandardPAAxiomWitnessPrefixContextCode M
        appendWitnesses (raw_zero M))).
  assert (hboundBody : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation finalContext
        (templateContextShiftMany 5 rowPrefix))
      (rawTemplateFormula translation
        coqDynamicTruthZeroCanonicalVacuousInheritedBoundRowBodyTemplate)
      bodyRoot).
  {
    unfold coqDynamicTruthZeroCanonicalVacuousInheritedBoundRowBodyTemplate.
    rewrite !rawTemplateFormula_imp.
    unfold translation in hbody |- *.
    rewrite
      (raw_dynamicTruthZeroCanonicalDirect_append_below_parameter_zero
        M hPA inputs hbound).
    exact hbody.
  }
  destruct
    (raw_codedPALocalProofOf_universal_introduction_chain_on_witnessed_tail
      M hPA translation finalWitnessList finalContext 5
      rowPrefix
      coqDynamicTruthZeroCanonicalVacuousInheritedBoundRowBodyTemplate
      bodyRoot hfinalWitnessed hboundBody)
    as [traversalRoot htraversal].
  set (visibleRowContext :=
    rawTemplateContextCodeOnTail translation finalContext rowPrefix).
  assert (hvisibleRowContext : RawContextListRealizable M visibleRowContext).
  {
    unfold visibleRowContext.
    exact (raw_templateContextOnTail_realizable M hPA translation
      finalContext rowPrefix
      (raw_codedPAAxiomWitnessContext_context_realizable M
        finalWitnessList finalContext hfinalWitnessed)).
  }
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    visibleRowContext (rawFormulaBotCode M) hvisibleRowContext)
    as holdLookupBody.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    visibleRowContext (rawFormulaBotCode M) (rawFormulaBotCode M)
    _ holdLookupBody) as holdLookup.
  lazymatch type of holdLookup with
  | RawCodedPALocalProofOf _ _ _ ?oldLookupRoot =>
      assert (holdLookupTemplate : RawCodedPALocalProofOf M
        visibleRowContext
        (rawTemplateFormula translation
          coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate)
        oldLookupRoot)
  end.
  {
    unfold coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate.
    rewrite rawTemplateFormula_imp, rawTemplateFormula_bot.
    exact holdLookup.
  }
  destruct
    (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
      M hPA traversalWitnesses
      (rawStandardPAAxiomWitnessPrefixContextCode M
        appendWitnesses (raw_zero M))
      (rawTemplateFormula translation
        (coqDynamicTruthZeroCanonicalAppendExistsTemplateAtRootTerms
          rootMode rootFormula rootAssignmentCode rootAssignmentStep))
      appendRoot
      (raw_codedPAAxiomWitnessContext_context_realizable M
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          appendWitnesses (raw_zero M))
        (rawStandardPAAxiomWitnessPrefixContextCode M
          appendWitnesses (raw_zero M)) happendWitnessed)
      happend)
    as [transportedAppendRoot htransportedAppend].
  exists (traversalWitnesses ++ appendWitnesses).
  rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
  rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
  split; [exact hfinalWitnessed |].
  exists transportedAppendRoot,
    coqDynamicTruthZeroCanonicalVacuousInheritedTraversalTemplate,
    coqDynamicTruthZeroCanonicalVacuousOldLookupTemplate.
  split.
  - rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
    exact htransportedAppend.
  - split.
    + exact
        coqDynamicTruthZeroCanonicalVacuousInheritedTraversalTemplate_open.
    + exists traversalRoot.
      lazymatch type of holdLookupTemplate with
      | RawCodedPALocalProofOf _ _ _ ?oldLookupRoot =>
          exists oldLookupRoot
      end.
      split.
      * fold finalContext in htraversal.
        rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
        unfold rowPrefix,
          coqDynamicTruthZeroCanonicalAppendRowContextAtRootTerms
          in htraversal |- *.
        exact htraversal.
      * unfold visibleRowContext in holdLookupTemplate.
        rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
        unfold rowPrefix,
          coqDynamicTruthZeroCanonicalAppendRowContextAtRootTerms
          in holdLookupTemplate |- *.
        exact holdLookupTemplate.
Qed.

(** Internal guarded specialization for the very same direct translation
    selected by evidence identification.  Append existence is already
    translation-parametric; the preceding theorem adds the vacuous inherited
    traversal without changing translations. *)
Theorem
    raw_dynamicTruthZeroCanonicalDirect_guardedAppendInheritedRowResourcesUnderPrefix_on_standardWitnessTail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateTerm inputs
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) =
    rawQuotedTermCode M tZero ->
  forall rootMode outerPrefix,
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) /\
    RawDynamicTruthZeroCanonicalGuardedAppendInheritedRowResourcesUnderPrefixAt
      M (rawDirectStructuralTemplateTranslation M hPA inputs)
      rootMode outerPrefix witnesses.
Proof.
  intros M hPA inputs hbound rootMode outerPrefix.
  destruct
    (raw_dynamicTruthZeroCanonicalGuardedAppendRoot_on_standardWitnessTail
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs) rootMode)
    as (appendWitnesses & appendRoot & happendWitnessed & happend).
  exact
    (raw_dynamicTruthZeroCanonicalDirect_appendInheritedRowResourcesAtRootTermsUnderPrefix_on_standardWitnessTail_of_append_root
      M hPA inputs hbound rootMode outerPrefix
      (ttVar 2) (ttVar 6) (ttVar 5)
      appendWitnesses appendRoot happendWitnessed happend).
Qed.

Corollary
    raw_dynamicTruthZeroCanonicalIdentified_guardedAppendInheritedRowResourcesUnderPrefix_on_standardWitnessTail :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  forall rootMode outerPrefix,
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) /\
    RawDynamicTruthZeroCanonicalGuardedAppendInheritedRowResourcesUnderPrefixAt
      M (rawDirectStructuralTemplateTranslation M hPA inputs)
      rootMode outerPrefix witnesses.
Proof.
  intros M hPA inputs hidentification rootMode outerPrefix.
  exact
    (raw_dynamicTruthZeroCanonicalDirect_guardedAppendInheritedRowResourcesUnderPrefix_on_standardWitnessTail
      M hPA inputs
      (rawDynamicTruthZeroGuardedEvidence_appendBoundZero
        M inputs hidentification)
      rootMode outerPrefix).
Qed.

(** Attach one same-translation fixed-production compiler to the inherited
    roots.  This is the first endpoint at which all four guarded row roots
    coexist under the selector-bearing evidence translation. *)
Theorem
    raw_dynamicTruthZeroCanonicalIdentified_guardedAppendRowKernelPayload_on_standardWitnessTail_of_growing_fixed_production :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  forall rootMode outerPrefix,
  RawDynamicTruthZeroCanonicalGuardedGrowingFixedProductionCompilerUnderPrefixAt
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
    rootMode outerPrefix ->
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) /\
    RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadUnderPrefixAt
      M (rawDirectStructuralTemplateTranslation M hPA inputs)
      rootMode outerPrefix witnesses.
Proof.
  intros M hPA inputs hidentification rootMode outerPrefix hfixed.
  destruct
    (raw_dynamicTruthZeroCanonicalIdentified_guardedAppendInheritedRowResourcesUnderPrefix_on_standardWitnessTail
      M hPA inputs hidentification rootMode outerPrefix)
    as (inheritedWitnesses & hinheritedWitnessed & hinherited).
  exact
    (raw_dynamicTruthZeroCanonicalAppendRowKernelPayloadAtRootTerms_on_standardWitnessTail_of_inherited_and_growing_fixed_production
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      rootMode outerPrefix (ttVar 2) (ttVar 6) (ttVar 5)
      inheritedWitnesses hinheritedWitnessed hinherited hfixed).
Qed.

(** Both modes may independently produce the canonical row or refute their
    temporary contexts.  Bottom elimination converts those alternatives,
    the preceding theorem builds each payload, and the established witness
    synchronizer combines the two finite helper batches. *)
Theorem
    raw_dynamicTruthZeroCanonicalIdentified_guardedAppendRowKernelPayloadPairUnderPrefix_of_independent_growing_fixed_productions_or_refutations :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  forall outerPrefix,
  RawDynamicTruthZeroCanonicalGuardedIndependentGrowingFixedProductionOrRefutationCompilersUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs) outerPrefix ->
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs) outerPrefix.
Proof.
  intros M hPA inputs hidentification outerPrefix hcompilers.
  pose proof
    (raw_dynamicTruthZeroCanonicalIndependentGrowingFixedProductionCompilersAtRootTermsUnderPrefix_of_production_or_refutation
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      outerPrefix (ttVar 2) (ttVar 6) (ttVar 5) hcompilers)
    as hfixed.
  destruct hfixed as [hsigmaFixed hpiFixed].
  assert (hindependent :
      RawDynamicTruthZeroCanonicalIndependentGuardedAppendRowKernelPayloadsUnderPrefix
        M (rawDirectStructuralTemplateTranslation M hPA inputs) outerPrefix).
  {
    split.
    - destruct
        (raw_dynamicTruthZeroCanonicalIdentified_guardedAppendRowKernelPayload_on_standardWitnessTail_of_growing_fixed_production
          M hPA inputs hidentification 0 outerPrefix hsigmaFixed)
        as (sigmaWitnesses & _ & hsigmaPayload).
      exact (ex_intro _ sigmaWitnesses hsigmaPayload).
    - destruct
        (raw_dynamicTruthZeroCanonicalIdentified_guardedAppendRowKernelPayload_on_standardWitnessTail_of_growing_fixed_production
          M hPA inputs hidentification 1 outerPrefix hpiFixed)
        as (piWitnesses & _ & hpiPayload).
      exact (ex_intro _ piWitnesses hpiPayload).
  }
  exact
    (raw_dynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix_of_independent_payloads
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      outerPrefix hindependent).
Qed.

(** A selected-translation spelling of the exact fixed guarded residue.  It
    deliberately mentions [inputs]: the evidence identification, inherited
    traversal, fixed production, and final synchronized payload must all use
    this one translation. *)
Definition
    RawDynamicTruthZeroCanonicalIdentifiedGuardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawDynamicTruthZeroCanonicalGuardedIndependentGrowingFixedProductionOrRefutationCompilersUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthImpGuardedFixedDeepPrefix.

Arguments
  RawDynamicTruthZeroCanonicalIdentifiedGuardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
  M hPA inputs : clear implicits.

(** Invocation-facing selected residual.  Stating it explicitly prevents a
    bottom-translation producer from being mistaken for evidence under the
    selector-bearing guarded translation. *)
Definition
    RawDynamicTruthZeroCanonicalIdentifiedGuardedDeepIndependentGrowingFixedProductionOrRefutationCompilersForAllCallers
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall callerPrefix,
    RawDynamicTruthZeroCanonicalGuardedIndependentGrowingFixedProductionOrRefutationCompilersUnderPrefix
      M (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqDynamicTruthImpGuardedDeepPrefix callerPrefix).

Arguments
  RawDynamicTruthZeroCanonicalIdentifiedGuardedDeepIndependentGrowingFixedProductionOrRefutationCompilersForAllCallers
  M hPA inputs : clear implicits.

(** The full synchronized payload pair at each guarded invocation follows
    immediately from evidence identification and the same-translation
    producer residue. *)
Theorem
    raw_dynamicTruthZeroCanonicalIdentified_guardedDeepAppendRowKernelPayloadPairForAllCallers :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  RawDynamicTruthZeroCanonicalIdentifiedGuardedDeepIndependentGrowingFixedProductionOrRefutationCompilersForAllCallers
    M hPA inputs ->
  forall callerPrefix,
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix).
Proof.
  intros M hPA inputs hidentification hcompilers callerPrefix.
  exact
    (raw_dynamicTruthZeroCanonicalIdentified_guardedAppendRowKernelPayloadPairUnderPrefix_of_independent_growing_fixed_productions_or_refutations
      M hPA inputs hidentification
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix)
      (hcompilers callerPrefix)).
Qed.

(** Suffix insertion is structural for every direct translation, not merely
    for the bottom instance.  Reprove the generic root-term adapter with the
    selected direct input package supplying atomic adequacy. *)
Theorem
    raw_dynamicTruthZeroCanonicalDirect_growingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt_app :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  forall rootMode outerPrefix callerSuffix
    rootFormula rootAssignmentCode rootAssignmentStep,
  RawDynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      rootMode outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep ->
  RawDynamicTruthZeroCanonicalGrowingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      rootMode (outerPrefix ++ callerSuffix)
      rootFormula rootAssignmentCode rootAssignmentStep.
Proof.
  intros M hPA inputs rootMode outerPrefix callerSuffix
    rootFormula rootAssignmentCode rootAssignmentStep hcompiler
    sourceWitnessList sourceContext hsource.
  destruct (hcompiler sourceWitnessList sourceContext hsource) as
    (witnesses & sourceRoot & hextended & hsourceProof).
  set (translation := rawDirectStructuralTemplateTranslation M hPA inputs).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M witnesses sourceContext).
  set (oldPrefix := templateContextShiftMany 5
    (coqFourStateTableAppendWitnessContext
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      (embedPATerm (Term.numeral rootMode))
      rootFormula rootAssignmentCode rootAssignmentStep outerPrefix)).
  set (newPrefix := templateContextShiftMany 5
    (coqFourStateTableAppendWitnessContext
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      (embedPATerm (Term.numeral rootMode))
      rootFormula rootAssignmentCode rootAssignmentStep
      (outerPrefix ++ callerSuffix))).
  assert (hprefixShape :
      oldPrefix ++ templateContextShiftMany 13 callerSuffix = newPrefix).
  {
    unfold oldPrefix, newPrefix.
    rewrite !coqFourStateTableAppendRowContext_affine.
    rewrite templateContextShiftMany_app.
    rewrite <- app_assoc. reflexivity.
  }
  assert (hcombinedAdequate :
      RawCodedTemplatePrefixAtomicallyAdequate M translation
        (oldPrefix ++ templateContextShiftMany 13 callerSuffix)).
  {
    rewrite hprefixShape.
    exact (raw_directStructuralTemplatePrefix_atomically_adequate
      M hPA inputs newPrefix).
  }
  assert (hextendedRealizable : RawContextListRealizable M extendedContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses sourceWitnessList)
      extendedContext hextended).
  }
  destruct hsourceProof as [hproduction | hrefutation].
  - destruct
      (raw_codedPALocalProof_templateSuffix
        M hPA translation extendedContext oldPrefix
        (templateContextShiftMany 13 callerSuffix)
        (rawTemplateFormula translation
          (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
            (coqFourStateTableAppendEmbeddedModeProductionMotive
              dynamicTruthZeroCanonicalSigmaRowFormula
              dynamicTruthZeroCanonicalPiRowFormula)))
        sourceRoot hextendedRealizable hcombinedAdequate hproduction)
      as [targetRoot htarget].
    exists witnesses, targetRoot. split; [exact hextended |].
    left. unfold translation, extendedContext in htarget |- *.
    rewrite hprefixShape in htarget. exact htarget.
  - destruct
      (raw_codedPALocalProof_templateSuffix
        M hPA translation extendedContext oldPrefix
        (templateContextShiftMany 13 callerSuffix)
        (rawFormulaBotCode M) sourceRoot
        hextendedRealizable hcombinedAdequate hrefutation)
      as [targetRoot htarget].
    exists witnesses, targetRoot. split; [exact hextended |].
    right. unfold translation, extendedContext in htarget |- *.
    rewrite hprefixShape in htarget. exact htarget.
Qed.

Corollary
    raw_dynamicTruthZeroCanonicalDirect_independentGrowingFixedProductionOrRefutationCompilersAtRootTermsUnderPrefix_app :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  forall outerPrefix callerSuffix
    rootFormula rootAssignmentCode rootAssignmentStep,
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersAtRootTermsUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs) outerPrefix
      rootFormula rootAssignmentCode rootAssignmentStep ->
  RawDynamicTruthZeroCanonicalIndependentGrowingFixedProductionOrRefutationCompilersAtRootTermsUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (outerPrefix ++ callerSuffix)
      rootFormula rootAssignmentCode rootAssignmentStep.
Proof.
  intros M hPA inputs outerPrefix callerSuffix
    rootFormula rootAssignmentCode rootAssignmentStep [hsigma hpi].
  split.
  - exact
      (raw_dynamicTruthZeroCanonicalDirect_growingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt_app
        M hPA inputs 0 outerPrefix callerSuffix
        rootFormula rootAssignmentCode rootAssignmentStep hsigma).
  - exact
      (raw_dynamicTruthZeroCanonicalDirect_growingFixedProductionOrRefutationCompilerAtRootTermsUnderPrefixAt_app
        M hPA inputs 1 outerPrefix callerSuffix
        rootFormula rootAssignmentCode rootAssignmentStep hpi).
Qed.

(** The exact selected fixed residue is equivalent to the apparent family of
    caller-indexed residues.  The five guarded binders rename the caller
    suffix before the append compiler inserts it. *)
Theorem
    raw_dynamicTruthZeroCanonicalIdentified_guardedDeepIndependentGrowingFixedProductionOrRefutationCompilersForAllCallers_of_fixed :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthZeroCanonicalIdentifiedGuardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
    M hPA inputs ->
  RawDynamicTruthZeroCanonicalIdentifiedGuardedDeepIndependentGrowingFixedProductionOrRefutationCompilersForAllCallers
    M hPA inputs.
Proof.
  intros M hPA inputs hfixed callerPrefix.
  rewrite coqDynamicTruthImpGuardedDeepPrefix_split.
  exact
    (raw_dynamicTruthZeroCanonicalDirect_independentGrowingFixedProductionOrRefutationCompilersAtRootTermsUnderPrefix_app
      M hPA inputs coqDynamicTruthImpGuardedFixedDeepPrefix
      (templateContextShiftMany 5 callerPrefix)
      (ttVar 2) (ttVar 6) (ttVar 5) hfixed).
Qed.

Theorem
    raw_dynamicTruthZeroCanonicalIdentified_guardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers_of_all_callers :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthZeroCanonicalIdentifiedGuardedDeepIndependentGrowingFixedProductionOrRefutationCompilersForAllCallers
    M hPA inputs ->
  RawDynamicTruthZeroCanonicalIdentifiedGuardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
    M hPA inputs.
Proof.
  intros M hPA inputs hall.
  specialize (hall []).
  rewrite coqDynamicTruthImpGuardedDeepPrefix_split in hall.
  cbn [templateContextShiftMany List.app] in hall.
  exact hall.
Qed.

Corollary
    raw_dynamicTruthZeroCanonicalIdentified_guardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers_iff_all_callers :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthZeroCanonicalIdentifiedGuardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
    M hPA inputs <->
  RawDynamicTruthZeroCanonicalIdentifiedGuardedDeepIndependentGrowingFixedProductionOrRefutationCompilersForAllCallers
    M hPA inputs.
Proof.
  intros M hPA inputs. split.
  - apply
      raw_dynamicTruthZeroCanonicalIdentified_guardedDeepIndependentGrowingFixedProductionOrRefutationCompilersForAllCallers_of_fixed.
  - apply
      raw_dynamicTruthZeroCanonicalIdentified_guardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers_of_all_callers.
Qed.

(** Selected evidence plus the single fixed residue yields synchronized
    guarded payload pairs for every caller prefix. *)
Corollary
    raw_dynamicTruthZeroCanonicalIdentified_guardedDeepAppendRowKernelPayloadPairForAllCallers_of_fixed :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  RawDynamicTruthZeroCanonicalIdentifiedGuardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
    M hPA inputs ->
  forall callerPrefix,
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix).
Proof.
  intros M hPA inputs hidentification hfixed.
  apply
    (raw_dynamicTruthZeroCanonicalIdentified_guardedDeepAppendRowKernelPayloadPairForAllCallers
      M hPA inputs hidentification).
  exact
    (raw_dynamicTruthZeroCanonicalIdentified_guardedDeepIndependentGrowingFixedProductionOrRefutationCompilersForAllCallers_of_fixed
      M hPA inputs hfixed).
Qed.

(** Boolean analogue of the selected fixed implication residue.  The outer
    prefix is constructor-specific; keeping [constructor] explicit prevents
    accidental transport between conjunction and disjunction guards. *)
Definition
    RawDynamicTruthZeroCanonicalIdentifiedBooleanGuardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
    (constructor : DynamicTruthBooleanConstructor)
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawDynamicTruthZeroCanonicalGuardedIndependentGrowingFixedProductionOrRefutationCompilersUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthBooleanGuardedFixedDeepPrefix constructor).

Arguments
  RawDynamicTruthZeroCanonicalIdentifiedBooleanGuardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
  constructor M hPA inputs : clear implicits.

(** The exact fixed collision payload boundary: implication, conjunction, and
    disjunction each own their two mode compilers under their literal guard. *)
Record
    RawDynamicTruthZeroCanonicalIdentifiedGuardedCollisionFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop := {
  rawDynamicTruthZeroGuardedCollisionFixed_imp :
    RawDynamicTruthZeroCanonicalIdentifiedGuardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
      M hPA inputs;
  rawDynamicTruthZeroGuardedCollisionFixed_and :
    RawDynamicTruthZeroCanonicalIdentifiedBooleanGuardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
      DTBooleanAnd M hPA inputs;
  rawDynamicTruthZeroGuardedCollisionFixed_or :
    RawDynamicTruthZeroCanonicalIdentifiedBooleanGuardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
      DTBooleanOr M hPA inputs
}.

Arguments
  RawDynamicTruthZeroCanonicalIdentifiedGuardedCollisionFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
  M hPA inputs : clear implicits.

(** Insert an arbitrary shifted caller suffix below a fixed Boolean guard. *)
Theorem
    raw_dynamicTruthZeroCanonicalIdentified_booleanGuardedDeepIndependentGrowingFixedProductionOrRefutationCompilersForCaller_of_fixed :
    forall constructor (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthZeroCanonicalIdentifiedBooleanGuardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
    constructor M hPA inputs ->
  forall callerPrefix,
  RawDynamicTruthZeroCanonicalGuardedIndependentGrowingFixedProductionOrRefutationCompilersUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix).
Proof.
  intros constructor M hPA inputs hfixed callerPrefix.
  rewrite coqDynamicTruthBooleanGuardedDeepPrefix_split.
  exact
    (raw_dynamicTruthZeroCanonicalDirect_independentGrowingFixedProductionOrRefutationCompilersAtRootTermsUnderPrefix_app
      M hPA inputs
      (coqDynamicTruthBooleanGuardedFixedDeepPrefix constructor)
      (templateContextShiftMany 5 callerPrefix)
      (ttVar 2) (ttVar 6) (ttVar 5) hfixed).
Qed.

(** Compile the synchronized Boolean append payload from its one fixed
    constructor-local residue. *)
Corollary
    raw_dynamicTruthZeroCanonicalIdentified_booleanGuardedDeepAppendRowKernelPayloadPairForCaller_of_fixed :
    forall constructor (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  RawDynamicTruthZeroCanonicalIdentifiedBooleanGuardedFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
    constructor M hPA inputs ->
  forall callerPrefix,
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix).
Proof.
  intros constructor M hPA inputs hidentification hfixed callerPrefix.
  exact
    (raw_dynamicTruthZeroCanonicalIdentified_guardedAppendRowKernelPayloadPairUnderPrefix_of_independent_growing_fixed_productions_or_refutations
      M hPA inputs hidentification
      (coqDynamicTruthBooleanGuardedDeepPrefix constructor callerPrefix)
      (raw_dynamicTruthZeroCanonicalIdentified_booleanGuardedDeepIndependentGrowingFixedProductionOrRefutationCompilersForCaller_of_fixed
        constructor M hPA inputs hfixed callerPrefix)).
Qed.

(** Produce all three payload pairs needed by the guarded collision compiler
    for one caller prefix.  This theorem is merely synchronization at the
    interface level: each field is compiled from its own honest fixed guard. *)
Theorem
    raw_dynamicTruthZeroCanonicalIdentified_guardedCollisionAppendRowKernelPayloadPairsForCaller_of_fixed :
    forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
  RawDynamicTruthZeroCanonicalIdentifiedGuardedCollisionFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
    M hPA inputs ->
  forall callerPrefix,
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthImpGuardedDeepPrefix callerPrefix) /\
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthBooleanGuardedDeepPrefix DTBooleanAnd callerPrefix) /\
  RawDynamicTruthZeroCanonicalGuardedAppendRowKernelPayloadPairUnderPrefix
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthBooleanGuardedDeepPrefix DTBooleanOr callerPrefix).
Proof.
  intros M hPA inputs hidentification
    [himpFixed handFixed horFixed] callerPrefix.
  split.
  - exact
      (raw_dynamicTruthZeroCanonicalIdentified_guardedDeepAppendRowKernelPayloadPairForAllCallers_of_fixed
        M hPA inputs hidentification himpFixed callerPrefix).
  - split.
    + exact
        (raw_dynamicTruthZeroCanonicalIdentified_booleanGuardedDeepAppendRowKernelPayloadPairForCaller_of_fixed
          DTBooleanAnd M hPA inputs hidentification handFixed callerPrefix).
    + exact
        (raw_dynamicTruthZeroCanonicalIdentified_booleanGuardedDeepAppendRowKernelPayloadPairForCaller_of_fixed
          DTBooleanOr M hPA inputs hidentification horFixed callerPrefix).
Qed.

(** Name the two temporary contexts before comparing them.  All append
    witnesses and all five row binders agree; only the assignment roots in
    the append instance change from [#1,#0] to [#6,#5]. *)
Definition coqDynamicTruthZeroCanonicalPermutedFixedProductionContext
    (rootMode : nat) : TemplateContext :=
  templateContextShiftMany 5
    (coqFourStateTableAppendWitnessContext
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      (embedPATerm (Term.numeral rootMode))
      (ttVar 2) (ttVar 1) (ttVar 0) []).

Definition coqDynamicTruthZeroCanonicalGuardedFixedProductionContext
    (rootMode : nat) : TemplateContext :=
  templateContextShiftMany 5
    (coqFourStateTableAppendWitnessContext
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      (embedPATerm (Term.numeral rootMode))
      (ttVar 2) (ttVar 6) (ttVar 5) []).

(** A kernel computation at either canonical mode exposes the differing
    assignment-code lookup.  This rules out definitional conversion and the
    equality-based conclusion rewrites used by the permuted append path. *)
Lemma coqDynamicTruthZeroCanonicalPermutedFixedProductionContext_neq_guarded_zero :
  coqDynamicTruthZeroCanonicalPermutedFixedProductionContext 0 <>
  coqDynamicTruthZeroCanonicalGuardedFixedProductionContext 0.
Proof.
  vm_compute.
  discriminate.
Qed.

Lemma coqDynamicTruthZeroCanonicalPermutedFixedProductionContext_neq_guarded_one :
  coqDynamicTruthZeroCanonicalPermutedFixedProductionContext 1 <>
  coqDynamicTruthZeroCanonicalGuardedFixedProductionContext 1.
Proof.
  vm_compute.
  discriminate.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroGuardedFixedProductionBoundary.
