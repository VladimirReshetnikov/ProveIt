(**
  Identify canonical rank-zero append sources with canonical applications.

  The permuted append traversal reverses its three exposed argument slots.
  When its two local rows are the literal first-successor rows above the
  fixed global base predicates, the resulting template is exactly the
  standard ternary application isolated by canonical trace exactification.
  This is a syntax theorem; no semantic or proof-producing premise occurs.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedLtSuccCasesProofCompilation
  RawCodedPAGrowingTemplateConjunction
  RawCodedFourStateTableAppendSource
  RawCodedFourStateTableAppendProofCompilation
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedFourStateTableAppendGlobalTraversalAssembly
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation
  RawCodedDynamicTruthPredecessorAtomicDomainGlobalRootsSynchronization
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthGlobalBaseRootClosure
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthNativeZeroCanonicalTraceExactification.

Module
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedPAGrowingTemplateConjunction.
Import PABoundedRawCodedFourStateTableAppendSource.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import
  PABoundedRawCodedDynamicTruthPredecessorAdmissibilityAssignmentCompilation.
Import
  PABoundedRawCodedDynamicTruthPredecessorAtomicDomainGlobalRootsSynchronization.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthGlobalBaseRootClosure.
Import
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalTraceExactification.

(** Literal local rows used by the first global successor. *)
Definition dynamicTruthZeroCanonicalSigmaRowFormula : formula :=
  dynamicTruthSigmaSuccessorRowFormula (Term.numeral 1)
    dynamicTruthGlobalPiBaseFormula.

Definition dynamicTruthZeroCanonicalPiRowFormula : formula :=
  dynamicTruthPiSuccessorRowFormula (Term.numeral 1)
    dynamicTruthGlobalSigmaBaseFormula.

(** Reversing the exposed tuple is definitionally the protected three-open
    application at [#2,#1,#0].  Kernel computation is intentional here: it
    audits the complete binder-sensitive syntax tree. *)
Lemma coqFourStateTableAppendPermutedTemplateGlobalSource_zero_sigma :
  coqFourStateTableAppendPermutedTemplateGlobalSource 0
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula) =
  embedPAFormula dynamicTruthZeroInputGlobalSigmaApplicationFormula.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma coqFourStateTableAppendPermutedTemplateGlobalSource_zero_pi :
  coqFourStateTableAppendPermutedTemplateGlobalSource 1
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula) =
  embedPAFormula dynamicTruthZeroInputGlobalPiApplicationFormula.
Proof.
  vm_compute. reflexivity.
Qed.

(** Carrier-facing forms for arbitrary PA-agreeing translations. *)
Theorem rawTemplateFormula_zeroCanonicalPermutedGlobalSource_sigma : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 0
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)) =
  rawQuotedFormulaCode M
    dynamicTruthZeroInputGlobalSigmaApplicationFormula.
Proof.
  intros M translation hagreement.
  rewrite coqFourStateTableAppendPermutedTemplateGlobalSource_zero_sigma.
  exact (rawTemplateFormula_embedPA hagreement
    dynamicTruthZeroInputGlobalSigmaApplicationFormula).
Qed.

Theorem rawTemplateFormula_zeroCanonicalPermutedGlobalSource_pi : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 1
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)) =
  rawQuotedFormulaCode M
    dynamicTruthZeroInputGlobalPiApplicationFormula.
Proof.
  intros M translation hagreement.
  rewrite coqFourStateTableAppendPermutedTemplateGlobalSource_zero_pi.
  exact (rawTemplateFormula_embedPA hagreement
    dynamicTruthZeroInputGlobalPiApplicationFormula).
Qed.

(** Any append traversal which returns the two embedded-row permuted sources
    can be rebased directly onto a witnessed callback context.  The two raw
    conclusion rewrites happen before context merging, so no structural
    translation remains in the resulting global-root package. *)
Theorem
    raw_dynamicTruthZeroCanonicalGlobalApplicationRoots_of_permuted_append_pair :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall producerSourceContext sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPAGrowingTemplateLocalProofPairAtEmpty M producerSourceContext
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 0
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)))
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 1
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula))) ->
  RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
    sourceContext
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula)
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula).
Proof.
  intros M hPA translation hagreement producerSourceContext
    sourceWitnessList sourceContext hsource hpair.
  rewrite (rawTemplateFormula_zeroCanonicalPermutedGlobalSource_sigma
    M translation hagreement) in hpair.
  rewrite (rawTemplateFormula_zeroCanonicalPermutedGlobalSource_pi
    M translation hagreement) in hpair.
  exact
    (raw_dynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom_of_rebased_growing_pair
      M hPA producerSourceContext sourceWitnessList sourceContext
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalSigmaApplicationFormula)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalPiApplicationFormula)
      hsource hpair).
Qed.

(** Primitive inputs consumed by one polarity of the canonical reversed
    append traversal.  Compared with the shared-row package used by positive
    levels, the row formulas are literal embedded PA syntax, so no opaque
    selector or output-code equation is retained. *)
Definition RawDynamicTruthZeroCanonicalPermutedAppendInputsAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep : TemplateTerm,
  exists appendRoot : M,
    (rootMode = 0 \/ rootMode = 1) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0))) appendRoot /\
    RawCodedPAGrowingTemplateLocalProofAt M translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter coqDynamicTruthAppendRowBoundParameterName)
        (embedPATerm (Term.numeral rootMode))
        (ttVar 2) (ttVar 1) (ttVar 0) nil)
      (rawTemplateFormula translation
        (templateAnd7Seventh
          (coqFourStateTableAppendOpenedPermutedTemplateGlobalFormula
            rootMode
            (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
            (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
            (ttParameter coqDynamicTruthAppendRowBoundParameterName)))).

Arguments RawDynamicTruthZeroCanonicalPermutedAppendInputsAt
  M translation rootMode witnesses : clear implicits.

(** Prefix-preserving primitive package.  The append-existence proof remains
    on the witnessed PA tail because it is independent of the predecessor
    assumptions; only the seventh-field traversal proof must genuinely live
    beneath the retained caller prefix. *)
Definition RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (outerPrefix : TemplateContext)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep : TemplateTerm,
  exists appendRoot : M,
    (rootMode = 0 \/ rootMode = 1) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0))) appendRoot /\
    RawCodedPAGrowingTemplateLocalProofAt M translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter coqDynamicTruthAppendRowBoundParameterName)
        (embedPATerm (Term.numeral rootMode))
        (ttVar 2) (ttVar 1) (ttVar 0) outerPrefix)
      (rawTemplateFormula translation
        (templateAnd7Seventh
          (coqFourStateTableAppendOpenedPermutedTemplateGlobalFormula
            rootMode
            (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
            (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
            (ttParameter coqDynamicTruthAppendRowBoundParameterName)))).

Arguments RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
  M translation rootMode outerPrefix witnesses : clear implicits.

(** Close one polarity without discharging the caller prefix.  The generic
    prefix inserter places the append-existence proof beneath that prefix;
    the prefix-preserving eight-witness eliminator then returns the global
    application in the same state-dependent context. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_permuted_global_of_inputs_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode outerPrefix witnesses,
  RawCodedTemplatePrefixAtomicallyAdequate M translation outerPrefix ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    M translation rootMode outerPrefix witnesses ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) outerPrefix
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource rootMode
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula))).
Proof.
  intros M hPA translation hagreement rootMode outerPrefix witnesses
    hprefix
    (modeCode & modeStep & formulaCode & formulaStep &
      assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep & appendRoot &
      hrootMode & happend & hrows).
  assert (hbase : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement witnesses) as hbaseTemplate.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hbaseTemplate.
    exact hbaseTemplate.
  }
  pose proof
    (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) hbase) as hbaseRealizable.
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) outerPrefix
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0)))
      appendRoot hbaseRealizable hprefix happend)
    as [prefixedAppendRoot hprefixedAppend].
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_template_global_of_append_rows_under_prefix
      M hPA translation hagreement rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      coqDynamicTruthAppendRowBoundParameterName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep outerPrefix witnesses
      prefixedAppendRoot hrootMode hprefixedAppend hrows).
Qed.

(** Synchronize both state-dependent polarities without dropping their
    common prefix. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofPairAt_dynamic_truth_zero_canonical_permuted_globals_of_inputs_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall outerPrefix witnesses,
  RawCodedTemplatePrefixAtomicallyAdequate M translation outerPrefix ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    M translation 0 outerPrefix witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    M translation 1 outerPrefix witnesses ->
  RawCodedPAGrowingTemplateLocalProofPairAt M translation
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) outerPrefix
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 0
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)))
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 1
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula))).
Proof.
  intros M hPA translation hagreement outerPrefix witnesses
    hprefix hsigma hpi.
  apply
    (raw_codedPAGrowingTemplateLocalProofAt_pair_at_prefix
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) outerPrefix).
  - exact
      (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_permuted_global_of_inputs_under_prefix
        M hPA translation hagreement 0 outerPrefix witnesses
        hprefix hsigma).
  - exact
      (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_permuted_global_of_inputs_under_prefix
        M hPA translation hagreement 1 outerPrefix witnesses
        hprefix hpi).
Qed.

(** Rebase the synchronized append result onto the caller's witnessed tail
    and normalize its two conclusions to the literal canonical application
    codes. *)
Theorem
    raw_dynamicTruthZeroCanonicalApplicationPair_of_permuted_append_inputs_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall outerPrefix witnesses sourceWitnessList sourceContext,
  RawCodedTemplatePrefixAtomicallyAdequate M translation outerPrefix ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    M translation 0 outerPrefix witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    M translation 1 outerPrefix witnesses ->
  RawCodedPAGrowingTemplateLocalProofPairAt M translation
    sourceContext outerPrefix
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula)
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula).
Proof.
  intros M hPA translation hagreement outerPrefix witnesses
    sourceWitnessList sourceContext hprefix hsource hsigma hpi.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofPairAt_dynamic_truth_zero_canonical_permuted_globals_of_inputs_under_prefix
      M hPA translation hagreement outerPrefix witnesses
      hprefix hsigma hpi) as hpair.
  rewrite (rawTemplateFormula_zeroCanonicalPermutedGlobalSource_sigma
    M translation hagreement) in hpair.
  rewrite (rawTemplateFormula_zeroCanonicalPermutedGlobalSource_pi
    M translation hagreement) in hpair.
  exact
    (raw_codedPAGrowingTemplateLocalProofPairAt_rebase
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) outerPrefix
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalSigmaApplicationFormula)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalPiApplicationFormula)
      sourceWitnessList sourceContext hsource hpair).
Qed.

(** Canonical rank-zero client.  The only temporary assumptions retained by
    the append traversal are the two predecessor-state membership formulas.
    Their atomic adequacy follows uniformly from PA agreement, so callers do
    not need to repeat that structural side condition. *)
Theorem
    raw_dynamicTruthZeroCanonicalStateApplicationPair_of_permuted_append_inputs :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnesses sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    M translation 0 coqDynamicTruthPredecessorStateTemplateContext
      witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsUnderPrefixAt
    M translation 1 coqDynamicTruthPredecessorStateTemplateContext
      witnesses ->
  RawCodedPAGrowingTemplateLocalProofPairAt M translation
    sourceContext coqDynamicTruthPredecessorStateTemplateContext
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula)
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula).
Proof.
  intros M hPA translation hagreement witnesses
    sourceWitnessList sourceContext hsource hsigma hpi.
  exact
    (raw_dynamicTruthZeroCanonicalApplicationPair_of_permuted_append_inputs_under_prefix
      M hPA translation hagreement
      coqDynamicTruthPredecessorStateTemplateContext witnesses
      sourceWitnessList sourceContext
      (raw_dynamicTruthPredecessorStateTemplateContext_atomically_adequate
        M hPA translation hagreement)
      hsource hsigma hpi).
Qed.

(** Close one canonical polarity from its primitive append package. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_permuted_global_of_inputs :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode witnesses,
  RawDynamicTruthZeroCanonicalPermutedAppendInputsAt M translation
    rootMode witnesses ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) nil
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource rootMode
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula))).
Proof.
  intros M hPA translation hagreement rootMode witnesses
    (modeCode & modeStep & formulaCode & formulaStep &
      assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep & appendRoot &
      hrootMode & happend & hrows).
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_template_global_of_append_rows
      M hPA translation hagreement rootMode
      (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
      (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)
      coqDynamicTruthAppendRowBoundParameterName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep witnesses appendRoot
      hrootMode happend hrows).
Qed.

(** Synchronize the two canonical append polarities at their shared standard
    witness-prefix source. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofPairAtEmpty_dynamic_truth_zero_canonical_permuted_globals_of_inputs :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnesses,
  RawDynamicTruthZeroCanonicalPermutedAppendInputsAt M translation
    0 witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsAt M translation
    1 witnesses ->
  RawCodedPAGrowingTemplateLocalProofPairAtEmpty M
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 0
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula)))
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 1
        (embedPAFormula dynamicTruthZeroCanonicalSigmaRowFormula)
        (embedPAFormula dynamicTruthZeroCanonicalPiRowFormula))).
Proof.
  intros M hPA translation hagreement witnesses hsigma hpi.
  apply (raw_codedPAGrowingTemplateLocalProofAt_pair_at_empty
    M hPA translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))).
  - exact
      (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_permuted_global_of_inputs
        M hPA translation hagreement 0 witnesses hsigma).
  - exact
      (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_zero_canonical_permuted_global_of_inputs
        M hPA translation hagreement 1 witnesses hpi).
Qed.

(** Public handoff from two primitive append packages to the exact canonical
    global roots beneath any witnessed predecessor callback base. *)
Theorem
    raw_dynamicTruthZeroCanonicalGlobalApplicationRoots_of_permuted_append_inputs :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnesses sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsAt M translation
    0 witnesses ->
  RawDynamicTruthZeroCanonicalPermutedAppendInputsAt M translation
    1 witnesses ->
  RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
    sourceContext
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula)
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula).
Proof.
  intros M hPA translation hagreement witnesses sourceWitnessList
    sourceContext hsource hsigma hpi.
  exact
    (raw_dynamicTruthZeroCanonicalGlobalApplicationRoots_of_permuted_append_pair
      M hPA translation hagreement
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      sourceWitnessList sourceContext hsource
      (raw_codedPAGrowingTemplateLocalProofPairAtEmpty_dynamic_truth_zero_canonical_permuted_globals_of_inputs
        M hPA translation hagreement witnesses hsigma hpi)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalAppendSourceIdentification.
