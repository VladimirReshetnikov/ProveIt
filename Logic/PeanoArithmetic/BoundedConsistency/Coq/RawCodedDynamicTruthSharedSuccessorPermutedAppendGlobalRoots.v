(**
  Package and synchronize the two permuted shared-successor append roots.

  Native derivation soundness applies each ternary global predicate to the
  current arguments in de Bruijn order [2,1,0].  The permuted append
  traversal compiler closes precisely those two applied formulas.  This file
  gives that compiler the same compact, proof-producing resource boundary as
  the ordinary [0,1,2] append endpoint, then synchronizes both polarities and
  transports them beneath an arbitrary predecessor callback context.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
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
  RawCodedDynamicTruthPredecessorStateExclusivityCompilation
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.

Module
  PABoundedRawCodedDynamicTruthSharedSuccessorPermutedAppendGlobalRoots.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
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
Import
  PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.

(** Exact resources consumed by one polarity of the reversed append client.
    The named row prefix stays abstract up to translated context-code
    equality, so clients need not expose how its four parameters realize the
    concrete root tuple. *)
Definition RawDynamicTruthSharedSuccessorPermutedAppendGlobalInputsAt
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
          (ttVar 2) (ttVar 1) (ttVar 0))) /\
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
          (ttVar 2) (ttVar 1) (ttVar 0))) appendRoot /\
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

Arguments RawDynamicTruthSharedSuccessorPermutedAppendGlobalInputsAt
  M translation rootMode witnesses : clear implicits.

Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_shared_successor_global_of_append_input_package :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode witnesses,
  RawDynamicTruthSharedSuccessorPermutedAppendGlobalInputsAt
    M translation rootMode witnesses ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) []
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource rootMode
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
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_shared_successor_global_of_append_and_inherited_row_roots
      M hPA translation hagreement rootMode
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      witnesses appendRoot inheritedTraversal oldLookup fixedProductionRoot
      hrootMode hprefix happend hopen hinherited hfixed).
Qed.

(** Synchronize both independently growing permuted roots before either one
    is transported to a caller context. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofPairAtEmpty_dynamic_truth_permuted_shared_successor_globals_of_append_input_packages :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnesses,
  RawDynamicTruthSharedSuccessorPermutedAppendGlobalInputsAt
    M translation 0 witnesses ->
  RawDynamicTruthSharedSuccessorPermutedAppendGlobalInputsAt
    M translation 1 witnesses ->
  RawCodedPAGrowingTemplateLocalProofPairAtEmpty M
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate))
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 1
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
      (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_shared_successor_global_of_append_input_package
        M hPA translation hagreement 0 witnesses hsigma).
  - exact
      (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_shared_successor_global_of_append_input_package
        M hPA translation hagreement 1 witnesses hpi).
Qed.

(** Merge the synchronized append context with an arbitrary witnessed base,
    transport both permuted roots to the merge, and insert the two literal
    predecessor-state assumptions. *)
Theorem
    raw_dynamicTruthPredecessorPermutedGlobalRootsOnWitnessedExtensionFrom_of_shared_successor_append_input_packages :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext witnesses,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawDynamicTruthSharedSuccessorPermutedAppendGlobalInputsAt
    M translation 0 witnesses ->
  RawDynamicTruthSharedSuccessorPermutedAppendGlobalInputsAt
    M translation 1 witnesses ->
  RawDynamicTruthPredecessorGlobalRootsOnWitnessedExtensionFrom M
    baseContext
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate))
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource 1
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate)).
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext witnesses hbase hsigmaInputs hpiInputs.
  destruct
    (raw_codedPAGrowingTemplateLocalProofPairAtEmpty_dynamic_truth_permuted_shared_successor_globals_of_append_input_packages
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
        (coqFourStateTableAppendPermutedTemplateGlobalSource 0
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      sigmaRoot happendWitnessed hmergedWitnessed happendIncluded hsigma) as
    [transportedSigmaRoot htransportedSigma].
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete M hPA
      appendWitnessList appendContext mergedWitnessList mergedContext
      (rawTemplateFormula translation
        (coqFourStateTableAppendPermutedTemplateGlobalSource 1
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

End
  PABoundedRawCodedDynamicTruthSharedSuccessorPermutedAppendGlobalRoots.
