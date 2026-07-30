(**
  Compile both shared successor globals from append traversal resources.

  The opaque-row append endpoint is intentionally rooted at a finite standard
  PA-witness prefix over the empty context.  Native predecessor compilation,
  however, starts from an arbitrary witnessed PA context accumulated by the
  current helper batch.  There is no reason to identify those contexts or to
  contract append proofs back to the helper context.

  This module packages the exact visible append resources for one polarity,
  compiles both polarities independently, synchronizes their growing tails,
  and finally merges that synchronized context with an arbitrary witnessed
  caller context.  Complete witnessed-context weakening transports the two
  global roots to the merge.  The predecessor state assumptions are inserted
  only after this last synchronization.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedLtSuccCasesProofCompilation
  RawCodedPAAxiomWitnessPrefix
  RawCodedPAGrowingTemplateConjunction
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedFourStateTableAppendSource
  RawCodedFourStateTableAppendProofCompilation
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedFourStateTableAppendTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthSuccessorRowsAppendNormalization.

Module PABoundedRawCodedDynamicTruthSharedSuccessorAppendGlobalRoots.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPAGrowingTemplateConjunction.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedFourStateTableAppendSource.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedFourStateTableAppendTemplateGlobalTraversalAssembly.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.

(** Exact proof-producing inputs consumed by the normalized shared-row append
    endpoint for one root mode.  The eight traversal fields are existentially
    hidden because clients should construct them as one coherent append
    trace, not coordinate their names across later callbacks. *)
Definition RawDynamicTruthSharedSuccessorAppendGlobalInputsAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (rootMode : nat) (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep : TemplateTerm,
  exists appendRoot fixedProductionRoot : M,
  exists inheritedTraversal oldLookup : TemplateFormula,
    let boundName := coqDynamicTruthAppendRowBoundParameterName in
    let namedRowPrefix :=
      coqFourStateTableAppendRowPrefix
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName)
        (ttParameter coqFourStateTableAppendRowModeParameterName)
        (ttParameter coqFourStateTableAppendRowFormulaParameterName)
        (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
        (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName) in
    (rootMode = 0 \/ rootMode = 1) /\
    (forall tail,
      rawTemplateContextCodeOnTail translation tail namedRowPrefix =
      rawTemplateContextCodeOnTail translation tail
        (coqFourStateTableAppendRowPrefix
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter boundName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 0) (ttVar 1) (ttVar 2))) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter boundName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 0) (ttVar 1) (ttVar 2))) appendRoot /\
    templateUniversalOpenMany inheritedTraversal
      coqFourStateTableAppendConcreteRowVariables =
      Some
        (tfImp
          (coqLtSuccCasesBelowTemplate
            (ttVar 4) (ttParameter boundName))
          (tfImp oldLookup
            (coqFourStateTableAppendConcreteClosedRowProductionTemplate
              coqDynamicTruthSharedSigmaSuccessorRowTemplate
              coqDynamicTruthSharedPiSuccessorRowTemplate))) /\
    RawFourStateTableAppendInheritedLocalRootsAt M translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      namedRowPrefix inheritedTraversal oldLookup /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M)) namedRowPrefix)
      (rawTemplateFormula translation
        (coqFourStateTableAppendNamedClosedRowProductionTemplate
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      fixedProductionRoot.

Arguments RawDynamicTruthSharedSuccessorAppendGlobalInputsAt
  M translation rootMode witnesses : clear implicits.

Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_shared_successor_global_of_append_input_package :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode witnesses,
  RawDynamicTruthSharedSuccessorAppendGlobalInputsAt
    M translation rootMode witnesses ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) []
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource rootMode
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate)).
Proof.
  intros M hPA translation hagreement rootMode witnesses
    (modeCode & modeStep & formulaCode & formulaStep &
      assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep &
      appendRoot & fixedProductionRoot & inheritedTraversal & oldLookup &
      hrootMode & hprefix & happend & hopen & hinherited & hfixed).
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_shared_successor_global_of_append_and_inherited_row_roots
      M hPA translation hagreement rootMode
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      witnesses appendRoot inheritedTraversal oldLookup fixedProductionRoot
      hrootMode hprefix happend hopen hinherited hfixed).
Qed.

(** Synchronize the independently growing Sigma- and Pi-rooted traversals. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofPairAtEmpty_dynamic_truth_shared_successor_globals_of_append_input_packages :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnesses,
  RawDynamicTruthSharedSuccessorAppendGlobalInputsAt
    M translation 0 witnesses ->
  RawDynamicTruthSharedSuccessorAppendGlobalInputsAt
    M translation 1 witnesses ->
  RawCodedPAGrowingTemplateLocalProofPairAtEmpty M
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate))
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource 1
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate)).
Proof.
  intros M hPA translation hagreement witnesses hsigma hpi.
  apply (raw_codedPAGrowingTemplateLocalProofAt_pair_at_empty
    M hPA translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))).
  - exact
      (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_shared_successor_global_of_append_input_package
        M hPA translation hagreement 0 witnesses hsigma).
  - exact
      (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_shared_successor_global_of_append_input_package
        M hPA translation hagreement 1 witnesses hpi).
Qed.

(** Merge append's synchronized standard-helper context with the arbitrary
    witnessed caller context.  Both source proofs are weakened from the
    append side; the caller-side inclusion is retained for the aligned
    strong-step continuation. *)
Theorem
    raw_dynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom_of_shared_successor_append_input_packages :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext witnesses,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawDynamicTruthSharedSuccessorAppendGlobalInputsAt
    M translation 0 witnesses ->
  RawDynamicTruthSharedSuccessorAppendGlobalInputsAt
    M translation 1 witnesses ->
  RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
    baseContext
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate))
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource 1
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate)).
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext witnesses hbase hsigmaInputs hpiInputs.
  destruct
    (raw_codedPAGrowingTemplateLocalProofPairAtEmpty_dynamic_truth_shared_successor_globals_of_append_input_packages
      M hPA translation hagreement witnesses hsigmaInputs hpiInputs) as
    (appendWitnessList & appendContext & sigmaRoot & piRoot &
      happendWitnessed & _hstandardIncluded & hsigma & hpi).
  destruct (raw_codedPAAxiomWitnessContext_prefixMerge M hPA
    appendWitnessList appendContext baseWitnessList baseContext
    happendWitnessed hbase) as
    (mergedWitnessList & mergedContext & hmergedWitnessed &
      _happendWitnessIncluded & happendIncluded &
      _hbaseWitnessIncluded & hbaseIncluded & _hbaseTransport).
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete M hPA
      appendWitnessList appendContext mergedWitnessList mergedContext
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource 0
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      sigmaRoot happendWitnessed hmergedWitnessed happendIncluded hsigma) as
    [transportedSigmaRoot htransportedSigma].
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete M hPA
      appendWitnessList appendContext mergedWitnessList mergedContext
      (rawTemplateFormula translation
        (coqDynamicTruthGlobalExistentialSource 1
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      piRoot happendWitnessed hmergedWitnessed happendIncluded hpi) as
    [transportedPiRoot htransportedPi].
  apply
    (raw_dynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom_of_growing_pair
      M hPA baseContext).
  exists mergedWitnessList, mergedContext,
    transportedSigmaRoot, transportedPiRoot.
  split; [exact hmergedWitnessed |].
  split; [exact hbaseIncluded |].
  split; assumption.
Qed.

End PABoundedRawCodedDynamicTruthSharedSuccessorAppendGlobalRoots.
