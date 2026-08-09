(**
  Produce the positive Imp-I bodies from literal append-row roots.

  The generic append traversal historically returned an existentially
  enlarged witnessed context.  That interface is sufficient for local
  traversal clients, but the direct derivation-soundness continuation must
  retain the stronger fact that every enlargement is a finite prefix of
  standard PA-axiom witnesses.  This file reconstructs the successor row in
  dependency order and keeps the two helper batches selected by equality
  transport and the arithmetic [i < S b] split explicit.

  No truth principle is assumed here.  The eventual Imp-I resource package
  exposes only literal append existence, inherited traversal/lookup, and the
  four roots used by the fixed Sigma-implication production.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedProofAssumptionLeaf
  RawCodedProofImpIConstructor
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofExistentialIntroductionChain
  RawCodedPALocalProofComposition
  RawCodedPALocalProofEquality
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplatePAEmbedding
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedFixedLevelTruthTotality
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedLtSuccCasesProofCompilation
  RawCodedPAGrowingTemplateConjunction
  RawCodedFourStateTableAppendProofCompilation
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedFourStateTableAppendGlobalTraversalAssembly
  RawCodedFourStateTableAppendTemplateGlobalTraversalAssembly
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthSigmaOrFixedProductionTemplate
  RawCodedDynamicTruthSigmaImpFixedProductionCompilation
  RawCodedDynamicTruthSigmaImpFixedProductionAppendIntegration
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADirectImpIntroductionPositiveBodyCompilation.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADirectImpIntroductionPositiveBodyAppendProduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofExistentialIntroductionChain.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofEquality.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedPAGrowingTemplateConjunction.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
Import PABoundedRawCodedFourStateTableAppendTemplateGlobalTraversalAssembly.
Import
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplate.
Import PABoundedRawCodedDynamicTruthSigmaImpFixedProductionCompilation.
Import
  PABoundedRawCodedDynamicTruthSigmaImpFixedProductionAppendIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADirectImpIntroductionPositiveBodyCompilation.

(** The operational equality lookup is a structural consequence of the
    eight append witnesses.  Existing clients stated this fact only for a
    standard tail rooted at the empty context.  Construct it once over the
    empty tail and transport it to an arbitrary honestly witnessed PA tail;
    this is what lets the positive-body compiler retain its caller's tail. *)
Theorem
    raw_fourStateTableAppendEqualityProductionInputsAt_on_witnessed_tail_under_prefix_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall sourceWitnessList sourceContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound sigmaProduction piProduction
    extraPrefix rowLookupRoot fixedResultRoot,
  let rowPrefix := coqFourStateTableAppendRowPrefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName)
    (ttParameter coqFourStateTableAppendRowModeParameterName)
    (ttParameter coqFourStateTableAppendRowFormulaParameterName)
    (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
    (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName) in
  let equalityHead :=
    coqLtSuccCasesEqualTemplate (ttVar 4) rowBound in
  let fixedResult :=
    coqFourStateTableAppendNamedClosedRowProductionTemplate
      sigmaProduction piProduction in
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation extraPrefix ->
  equalityHead = tfEq (ttVar 4) (ttParameter boundName) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation equalityHead) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext
      (extraPrefix ++ rowPrefix))
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityRowLookupTemplate
        coqFourStateTableAppendRowModeParameterName
        coqFourStateTableAppendRowFormulaParameterName
        coqFourStateTableAppendRowAssignmentCodeParameterName
        coqFourStateTableAppendRowAssignmentStepParameterName
        (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)))
    rowLookupRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext
      (extraPrefix ++ rowPrefix))
    (rawTemplateFormula translation fixedResult) fixedResultRoot ->
  RawFourStateTableAppendEqualityProductionInputsAt M translation
    sourceContext (equalityHead :: extraPrefix ++ rowPrefix)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName
    coqFourStateTableAppendRowModeParameterName
    coqFourStateTableAppendRowFormulaParameterName
    coqFourStateTableAppendRowAssignmentCodeParameterName
    coqFourStateTableAppendRowAssignmentStepParameterName
    (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
    fixedResult.
Proof.
  intros M hPA translation hagreement sourceWitnessList sourceContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound sigmaProduction piProduction
    extraPrefix rowLookupRoot fixedResultRoot
    rowPrefix equalityHead fixedResult
    hsource hextraPrefix hequalityHead hequalityAdequate
    hrowLookup hfixedResult.
  cbn zeta in *.
  assert (hempty : RawCodedPAAxiomWitnessContext M
      (raw_zero M) (raw_zero M)).
  {
    pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
    cbn [rawQuotedPAAxiomWitnessList rawListCode map] in h.
    exact h.
  }
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_equality_branch_lookup_parameter_under_prefix
      M hPA translation [] extraPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName
      (ttParameter coqFourStateTableAppendRowModeParameterName)
      (ttParameter coqFourStateTableAppendRowFormulaParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName)
      (ttVar 4) rowBound hextraPrefix hequalityHead hequalityAdequate)
    as [emptyFixedLookupRoot hemptyFixedLookup].
  rewrite coqFourStateTableAppendRowContext_affine in hemptyFixedLookup.
  cbn [templateContextShiftMany List.app] in hemptyFixedLookup.
  rewrite raw_templateContextCode_as_on_tail_general in hemptyFixedLookup.
  rewrite <- rawTemplateContextCodeOnTail_app in hemptyFixedLookup.
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      (raw_zero M) (raw_zero M) sourceWitnessList sourceContext
      (equalityHead :: extraPrefix ++ rowPrefix)
      (rawTemplateFormula translation
        (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
          boundName (ttVar 4)
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter coqFourStateTableAppendRowModeParameterName)
          (ttParameter coqFourStateTableAppendRowFormulaParameterName)
          (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
          (ttParameter
            coqFourStateTableAppendRowAssignmentStepParameterName)))
      emptyFixedLookupRoot hempty hsource
      (raw_contextListIncluded_zero M hPA sourceContext)
      hemptyFixedLookup)
    as [fixedLookupRoot hfixedLookup].
  assert (hcombinedContext : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation sourceContext
        (extraPrefix ++ rowPrefix))).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      sourceWitnessList sourceContext hsource).
  }
  assert (hequalityPrefix :
      RawCodedTemplatePrefixAtomicallyAdequate M translation
        [equalityHead]).
  {
    intros formula [hformula | hformula].
    - subst formula. exact hequalityAdequate.
    - contradiction.
  }
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation
      (rawTemplateContextCodeOnTail translation sourceContext
        (extraPrefix ++ rowPrefix))
      [equalityHead]
      (rawTemplateFormula translation
        (coqFourStateTableAppendEqualityRowLookupTemplate
          coqFourStateTableAppendRowModeParameterName
          coqFourStateTableAppendRowFormulaParameterName
          coqFourStateTableAppendRowAssignmentCodeParameterName
          coqFourStateTableAppendRowAssignmentStepParameterName
          (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)))
      rowLookupRoot hcombinedContext hequalityPrefix hrowLookup)
    as [shiftedRowLookupRoot hshiftedRowLookup].
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation
      (rawTemplateContextCodeOnTail translation sourceContext
        (extraPrefix ++ rowPrefix))
      [equalityHead]
      (rawTemplateFormula translation
        (coqFourStateTableAppendNamedClosedRowProductionTemplate
          sigmaProduction piProduction))
      fixedResultRoot hcombinedContext hequalityPrefix hfixedResult)
    as [shiftedFixedResultRoot hshiftedFixedResult].
  unfold RawFourStateTableAppendEqualityProductionInputsAt.
  exists fixedLookupRoot, shiftedRowLookupRoot, shiftedFixedResultRoot.
  cbn in hfixedLookup, hshiftedRowLookup, hshiftedFixedResult |- *.
  split; [exact hfixedLookup |].
  split; [exact hshiftedRowLookup | exact hshiftedFixedResult].
Qed.

(** Arbitrary-tail form of the structural fixed-bound lookup used by the
    equality branch.  The proof is first built in the literal append witness
    context (including the retained outer prefix), then weakened from the
    empty witnessed PA tail to the caller's tail. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_equality_fixed_lookup_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext outerPrefix extraPrefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName mode formula assignmentCode assignmentStep
    index rowBound,
  let rowPrefix := templateContextShiftMany 5
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) mode formula assignmentCode assignmentStep
      outerPrefix) in
  let equalityHead := coqLtSuccCasesEqualTemplate index rowBound in
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation extraPrefix ->
  equalityHead = tfEq index (ttParameter boundName) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation equalityHead) ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sourceContext
        (equalityHead :: extraPrefix ++ rowPrefix))
      (rawTemplateFormula translation
        (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
          boundName index
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          mode formula assignmentCode assignmentStep)) root.
Proof.
  intros M hPA translation sourceWitnessList sourceContext
    outerPrefix extraPrefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName mode formula assignmentCode assignmentStep
    index rowBound rowPrefix equalityHead
    hsource hextraPrefix hequalityHead hequalityAdequate.
  cbn zeta in *.
  assert (hempty : RawCodedPAAxiomWitnessContext M
      (raw_zero M) (raw_zero M)).
  {
    pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
    cbn [rawQuotedPAAxiomWitnessList rawListCode map] in h.
    exact h.
  }
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_equality_branch_lookup_parameter_under_prefix
      M hPA translation outerPrefix extraPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName mode formula assignmentCode assignmentStep
      index rowBound hextraPrefix hequalityHead hequalityAdequate)
    as [emptyRoot hemptyRoot].
  rewrite raw_templateContextCode_as_on_tail_general in hemptyRoot.
  rewrite <- rawTemplateContextCodeOnTail_app in hemptyRoot.
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      (raw_zero M) (raw_zero M) sourceWitnessList sourceContext
      (equalityHead :: extraPrefix ++ rowPrefix)
      (rawTemplateFormula translation
        (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
          boundName index
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          mode formula assignmentCode assignmentStep))
      emptyRoot hempty hsource
      (raw_contextListIncluded_zero M hPA sourceContext) hemptyRoot)
    as [root hroot].
  exists root.
  exact hroot.
Qed.

(** No-growth seven-field traversal assembly on an arbitrary witnessed PA
    tail.  The six append projections are structural proofs, so they are
    built over the empty tail and transported to the caller's exact tail;
    the supplied seventh row field already lives there. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_traversal_body_on_witnessed_tail_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    outerPrefix rows rowsRoot,
  let prefix := coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep outerPrefix in
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawTemplateFormula translation rows) rowsRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sourceContext prefix)
      (rawTemplateFormula translation
        (coqFourStateTableAppendTraversalBodyTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep rows)) root.
Proof.
  intros M hPA translation sourceWitnessList sourceContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    outerPrefix rows rowsRoot prefix hsource hrows.
  cbn zeta in *.
  assert (hempty : RawCodedPAAxiomWitnessContext M
      (raw_zero M) (raw_zero M)).
  {
    pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as h.
    cbn [rawQuotedPAAxiomWitnessList rawListCode map] in h.
    exact h.
  }
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_defined_components
      M hPA translation outerPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    as (modeRoot & formulaRoot & assignmentCodeRoot & assignmentStepRoot &
      hmode & hformula & hassignmentCode & hassignmentStep).
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_root_bound
      M hPA translation outerPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    as [boundRoot hbound].
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_new_state_lookup
      M hPA translation outerPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    as [lookupRoot hlookup].
  rewrite raw_templateContextCode_as_on_tail_general in
    hmode, hformula, hassignmentCode, hassignmentStep, hbound, hlookup.
  assert (hemptyIncluded : RawContextListIncluded M
      (raw_zero M) sourceContext).
  { exact (raw_contextListIncluded_zero M hPA sourceContext). }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation (raw_zero M) (raw_zero M)
      sourceWitnessList sourceContext prefix
      (rawTemplateFormula translation
        (coqFourStateTableAppendModeDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      modeRoot hempty hsource hemptyIncluded hmode)
    as [modeRoot' hmode'].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation (raw_zero M) (raw_zero M)
      sourceWitnessList sourceContext prefix
      (rawTemplateFormula translation
        (coqFourStateTableAppendFormulaDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      formulaRoot hempty hsource hemptyIncluded hformula)
    as [formulaRoot' hformula'].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation (raw_zero M) (raw_zero M)
      sourceWitnessList sourceContext prefix
      (rawTemplateFormula translation
        (coqFourStateTableAppendAssignmentCodeDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      assignmentCodeRoot hempty hsource hemptyIncluded hassignmentCode)
    as [assignmentCodeRoot' hassignmentCode'].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation (raw_zero M) (raw_zero M)
      sourceWitnessList sourceContext prefix
      (rawTemplateFormula translation
        (coqFourStateTableAppendAssignmentStepDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      assignmentStepRoot hempty hsource hemptyIncluded hassignmentStep)
    as [assignmentStepRoot' hassignmentStep'].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation (raw_zero M) (raw_zero M)
      sourceWitnessList sourceContext prefix
      (rawTemplateFormula translation
        (coqFourStateTableAppendRootBoundTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      boundRoot hempty hsource hemptyIncluded hbound)
    as [boundRoot' hbound'].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation (raw_zero M) (raw_zero M)
      sourceWitnessList sourceContext prefix
      (rawTemplateFormula translation
        (coqFourStateTableAppendNewStateLookupTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      lookupRoot hempty hsource hemptyIncluded hlookup)
    as [lookupRoot' hlookup'].
  destruct
    (raw_codedPALocalProofOf_and7I M hPA
      (rawTemplateContextCodeOnTail translation sourceContext prefix)
      (rawTemplateFormula translation
        (coqFourStateTableAppendModeDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      (rawTemplateFormula translation
        (coqFourStateTableAppendFormulaDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      (rawTemplateFormula translation
        (coqFourStateTableAppendAssignmentCodeDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      (rawTemplateFormula translation
        (coqFourStateTableAppendAssignmentStepDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      (rawTemplateFormula translation
        (coqFourStateTableAppendRootBoundTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      (rawTemplateFormula translation
        (coqFourStateTableAppendNewStateLookupTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      (rawTemplateFormula translation rows)
      modeRoot' formulaRoot' assignmentCodeRoot' assignmentStepRoot'
      boundRoot' lookupRoot' rowsRoot
      hmode' hformula' hassignmentCode' hassignmentStep'
      hbound' hlookup' hrows)
    as [root hrecord].
  exists root.
  unfold coqFourStateTableAppendTraversalBodyTemplate.
  rewrite !rawTemplateFormula_and.
  exact hrecord.
Qed.

(** The concrete Imp-I root coordinates preserve the two shared successor
    rows under the capture-safe three-term substitution used by the global
    append source.  This small normalization is intentionally stated only
    at the actual coordinates: unrestricted opaque rows are not invariant
    under arbitrary root-term substitution. *)
Lemma coqRestrictedPADirectImpIntroduction_shared_rows_at_root_terms_eq :
  coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName) =
    coqFourStateTableAppendOpenedTemplateGlobalRows 0
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      (ttParameter coqDynamicTruthAppendRowBoundParameterName).
Proof. vm_compute. reflexivity. Qed.

(** No-growth root-term append endpoint.  Once the concrete row implication
    has reached one witnessed tail, universal closure, seven-field assembly,
    the ten global witnesses, and elimination of the eight append witnesses
    are all represented structural rules and preserve that exact tail.

    The explicit row-stability equality is necessary for arbitrary exposed
    root terms.  It is syntactic, not proof-producing, and prevents this
    general helper from silently treating opaque rows as substitution
    invariant. *)
Theorem
    raw_codedPALocalProofOf_dynamic_truth_shared_global_at_root_terms_of_append_and_concrete_row_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall sourceWitnessList sourceContext
    rootMode boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    rootFormula rootAssignmentCode rootAssignmentStep
    outerPrefix appendRoot rowRoot,
  let witnessContext := coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
    rootFormula rootAssignmentCode rootAssignmentStep outerPrefix in
  let antecedent := coqLtSuccCasesAntecedentTemplate
    (ttVar 4) (ttParameter boundName) in
  let rowLookup :=
    coqFourStateTableAppendEqualityRowLookupTemplate
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0) in
  let result :=
    coqFourStateTableAppendConcreteClosedRowProductionTemplate
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate in
  rootMode = 0 \/ rootMode = 1 ->
  coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms rootMode
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      rootFormula rootAssignmentCode rootAssignmentStep
      (ttParameter boundName) =
    coqFourStateTableAppendOpenedTemplateGlobalRows rootMode
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      (ttParameter boundName) ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext outerPrefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendExistsTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
        rootFormula rootAssignmentCode rootAssignmentStep)) appendRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext
      (templateContextShiftMany 5 witnessContext))
    (rawTemplateFormula translation
      (tfImp antecedent (tfImp rowLookup result))) rowRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sourceContext outerPrefix)
      (rawTemplateFormula translation
        (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms
          rootMode
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate
          rootFormula rootAssignmentCode rootAssignmentStep)) root.
Proof.
  intros M hPA translation hagreement sourceWitnessList sourceContext
    rootMode boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    rootFormula rootAssignmentCode rootAssignmentStep
    outerPrefix appendRoot rowRoot
    witnessContext antecedent rowLookup result
    hrootMode hrowStable hsource happend hrow.
  cbn zeta in *.
  set (openedProduction :=
    coqFourStateTableAppendOpenedTemplateGlobalRowProduction
      rootMode
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      (ttParameter boundName)).
  assert (hrowOpened : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sourceContext
        (templateContextShiftMany 5 witnessContext))
      (rawTemplateFormula translation
        (tfImp antecedent (tfImp rowLookup openedProduction))) rowRoot).
  {
    unfold openedProduction.
    rewrite <- (coqDynamicTruthSharedSuccessorRows_append_production
      rootMode (ttParameter boundName)).
    exact hrow.
  }
  destruct
    (raw_codedPALocalProofOf_universal_introduction_chain_on_witnessed_tail
      M hPA translation sourceWitnessList sourceContext
      5 witnessContext
      (tfImp antecedent (tfImp rowLookup openedProduction))
      rowRoot hsource hrowOpened)
    as [rowsRoot hrows].
  unfold antecedent, rowLookup, openedProduction, witnessContext in hrows.
  assert (hrowsAtRootTerms : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sourceContext
        (coqFourStateTableAppendWitnessContext
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
          rootFormula rootAssignmentCode rootAssignmentStep outerPrefix))
      (rawTemplateFormula translation
        (coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms
          rootMode
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate
          rootFormula rootAssignmentCode rootAssignmentStep
          (ttParameter boundName))) rowsRoot).
  {
    rewrite hrowStable.
    rewrite coqFourStateTableAppendOpenedTemplateGlobalRows_shape.
    exact hrows.
  }
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_traversal_body_on_witnessed_tail_under_prefix
      M hPA translation sourceWitnessList sourceContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      rootFormula rootAssignmentCode rootAssignmentStep outerPrefix
      (coqFourStateTableAppendOpenedTemplateGlobalRowsAtRootTerms
        rootMode
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        rootFormula rootAssignmentCode rootAssignmentStep
        (ttParameter boundName))
      rowsRoot hsource hrowsAtRootTerms)
    as [bodyRoot hbody].
  pose proof
    (coqFourStateTableAppendOpenedTemplateGlobalFormulaAtRootTerms_shape
      rootMode
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      rootFormula rootAssignmentCode rootAssignmentStep hrootMode)
    as hopenedShape.
  rewrite <- hopenedShape in hbody.
  destruct
    (raw_codedPALocalProofOf_templateExistentialOpenMany
      M hPA translation
      (rawTemplateContextCodeOnTail translation sourceContext
        (coqFourStateTableAppendWitnessContext
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
          rootFormula rootAssignmentCode rootAssignmentStep outerPrefix))
      (templateFormulaShiftMany 8
        (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms
          rootMode
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate
          rootFormula rootAssignmentCode rootAssignmentStep))
      (coqFourStateTableAppendGlobalTraversalWitnesses
        (ttParameter boundName))
      (coqFourStateTableAppendOpenedTemplateGlobalFormulaAtRootTerms
        rootMode
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        rootFormula rootAssignmentCode rootAssignmentStep
        (ttParameter boundName))
      bodyRoot
      (coqFourStateTableAppendOpenedTemplateGlobalFormulaAtRootTerms_success
        rootMode
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        rootFormula rootAssignmentCode rootAssignmentStep
        (ttParameter boundName))
      hbody)
    as [globalRoot hglobal].
  destruct
    (raw_codedPALocalProofOf_existential_elimination_chain_on_witnessed_tail
      M hPA translation sourceWitnessList sourceContext
      8
      (coqFourStateTableAppendExistsTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
        rootFormula rootAssignmentCode rootAssignmentStep)
      outerPrefix
      (coqFourStateTableAppendTemplateGlobalSourceAtRootTerms
        rootMode
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        rootFormula rootAssignmentCode rootAssignmentStep)
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
        rootFormula rootAssignmentCode rootAssignmentStep outerPrefix)
      appendRoot globalRoot hsource
      (coqFourStateTableAppendWitnessContext_success
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
        rootFormula rootAssignmentCode rootAssignmentStep outerPrefix)
      happend hglobal)
    as [root hroot].
  exists root.
  exact hroot.
Qed.

(** Standard-output form of the complete concrete successor-row compiler.
    Equality transport is deliberately compiled before the arithmetic split.
    Its helper witnesses therefore become part of the base seen by the split;
    the latter's finite helper batch is then prepended.  Both predecessor and
    equality branch proofs are transported forward to that common tail before
    [Or-E], and the two temporary premises are discharged locally. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_concrete_closed_row_implications_on_standard_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall sourceWitnessList sourceContext rowPrefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound sigmaProduction piProduction
    inheritedTraversal oldLookup fixedLookupRoot fixedResultRoot,
  let antecedent :=
    coqLtSuccCasesAntecedentTemplate (ttVar 4) rowBound in
  let rowLookup :=
    coqFourStateTableAppendEqualityRowLookupTemplate
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0) in
  let below := coqLtSuccCasesBelowTemplate (ttVar 4) rowBound in
  let equalityHead := coqLtSuccCasesEqualTemplate (ttVar 4) rowBound in
  let fixedResult :=
    coqFourStateTableAppendNamedClosedRowProductionTemplate
      sigmaProduction piProduction in
  let result :=
    coqFourStateTableAppendConcreteClosedRowProductionTemplate
      sigmaProduction piProduction in
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  templateUniversalOpenMany inheritedTraversal
    coqFourStateTableAppendConcreteRowVariables =
    Some (tfImp below (tfImp oldLookup result)) ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation rowPrefix ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation antecedent) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation rowLookup) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation below) ->
  equalityHead = tfEq (ttVar 4) (ttParameter boundName) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation equalityHead) ->
  coqFourStateTableAppendRowModeParameterName <> boundName ->
  coqFourStateTableAppendRowFormulaParameterName <> boundName ->
  coqFourStateTableAppendRowAssignmentCodeParameterName <> boundName ->
  coqFourStateTableAppendRowAssignmentStepParameterName <> boundName ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext
      (equalityHead :: [rowLookup; antecedent] ++ rowPrefix))
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
        boundName (ttVar 4)
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter coqFourStateTableAppendRowModeParameterName)
        (ttParameter coqFourStateTableAppendRowFormulaParameterName)
        (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
        (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName)))
    fixedLookupRoot ->
  RawFourStateTableAppendInheritedLocalRootsAt M translation
    sourceContext rowPrefix inheritedTraversal oldLookup ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext rowPrefix)
    (rawTemplateFormula translation fixedResult) fixedResultRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses sourceWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses sourceContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses sourceContext) rowPrefix)
      (rawTemplateFormula translation
        (tfImp antecedent (tfImp rowLookup result))) root.
Proof.
  intros M hPA translation hagreement sourceWitnessList sourceContext
    rowPrefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    boundName rowBound sigmaProduction piProduction
    inheritedTraversal oldLookup fixedLookupRoot fixedResultRoot
    antecedent rowLookup below equalityHead fixedResult result
    hsource hopen hrowPrefix hantecedentAdequate hrowLookupAdequate
    hbelowAdequate hequalityHead hequalityAdequate
    hmodeFresh hformulaFresh hassignmentCodeFresh hassignmentStepFresh
    hfixedLookup
    hinheritedRoots hfixedResult.
  cbn zeta in *.
  set (extraPrefix := [rowLookup; antecedent]).
  set (combinedPrefix := extraPrefix ++ rowPrefix).
  assert (hextraPrefix :
      RawCodedTemplatePrefixAtomicallyAdequate M translation extraPrefix).
  {
    intros formula [hformula | [hformula | hformula]].
    - subst formula. exact hrowLookupAdequate.
    - subst formula. exact hantecedentAdequate.
    - contradiction.
  }
  assert (hcombinedPrefix :
      RawCodedTemplatePrefixAtomicallyAdequate M translation combinedPrefix).
  {
    intros formula hformula.
    unfold combinedPrefix in hformula.
    apply in_app_or in hformula.
    destruct hformula as [hformula | hformula].
    - exact (hextraPrefix formula hformula).
    - exact (hrowPrefix formula hformula).
  }
  assert (hrowContext : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation sourceContext rowPrefix)).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      sourceWitnessList sourceContext hsource).
  }
  destruct hinheritedRoots as
    (traversalRoot & oldLookupRoot & htraversal & holdLookup).
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation
      (rawTemplateContextCodeOnTail translation sourceContext rowPrefix)
      extraPrefix (rawTemplateFormula translation inheritedTraversal)
      traversalRoot hrowContext hextraPrefix htraversal)
    as [prefixedTraversalRoot hprefixedTraversal].
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation
      (rawTemplateContextCodeOnTail translation sourceContext rowPrefix)
      extraPrefix (rawTemplateFormula translation oldLookup)
      oldLookupRoot hrowContext hextraPrefix holdLookup)
    as [prefixedOldLookupRoot hprefixedOldLookup].
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation
      (rawTemplateContextCodeOnTail translation sourceContext rowPrefix)
      extraPrefix (rawTemplateFormula translation fixedResult)
      fixedResultRoot hrowContext hextraPrefix hfixedResult)
    as [prefixedFixedResultRoot hprefixedFixedResult].
  assert (hantecedentContext : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation sourceContext
        (antecedent :: rowPrefix))).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      sourceWitnessList sourceContext hsource).
  }
  pose proof
    (raw_codedPALocalProofOf_assumption M hPA
      (rawTemplateContextCodeOnTail translation sourceContext rowPrefix)
      (rawTemplateFormula translation antecedent) hrowContext)
    as hantecedentHead.
  assert (hrowLookupSingleton :
      RawCodedTemplatePrefixAtomicallyAdequate M translation [rowLookup]).
  {
    intros formula [hformula | hformula].
    - subst formula. exact hrowLookupAdequate.
    - contradiction.
  }
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation
      (rawTemplateContextCodeOnTail translation sourceContext
        (antecedent :: rowPrefix))
      [rowLookup] (rawTemplateFormula translation antecedent)
      (rawProofAssumptionRoot M
        (rawListNode M (rawTemplateFormula translation antecedent)
          (rawTemplateContextCodeOnTail translation sourceContext rowPrefix))
        (rawTemplateFormula translation antecedent))
      hantecedentContext hrowLookupSingleton hantecedentHead)
    as [antecedentRoot hantecedent].
  pose proof
    (raw_codedPALocalProofOf_assumption M hPA
      (rawTemplateContextCodeOnTail translation sourceContext
        (antecedent :: rowPrefix))
      (rawTemplateFormula translation rowLookup) hantecedentContext)
    as hrowLookup.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext combinedPrefix)
    (rawTemplateFormula translation rowLookup)
    (rawProofAssumptionRoot M
      (rawTemplateContextCodeOnTail translation sourceContext combinedPrefix)
      (rawTemplateFormula translation rowLookup))) in hrowLookup.
  assert (hcombinedContext : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation sourceContext
        combinedPrefix)).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      sourceWitnessList sourceContext hsource).
  }
  assert (hequalitySingleton :
      RawCodedTemplatePrefixAtomicallyAdequate M translation
        [equalityHead]).
  {
    intros formula [hformula | hformula].
    - subst formula. exact hequalityAdequate.
    - contradiction.
  }
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation
      (rawTemplateContextCodeOnTail translation sourceContext
        combinedPrefix)
      [equalityHead]
      (rawTemplateFormula translation rowLookup)
      (rawProofAssumptionRoot M
        (rawTemplateContextCodeOnTail translation sourceContext
          combinedPrefix)
        (rawTemplateFormula translation rowLookup))
      hcombinedContext hequalitySingleton hrowLookup)
    as [equalityRowLookupRoot hequalityRowLookup].
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation
      (rawTemplateContextCodeOnTail translation sourceContext
        combinedPrefix)
      [equalityHead]
      (rawTemplateFormula translation fixedResult)
      prefixedFixedResultRoot hcombinedContext hequalitySingleton
      hprefixedFixedResult)
    as [equalityFixedResultRoot hequalityFixedResult].
  assert (hequalityCombinedPrefix :
      RawCodedTemplatePrefixAtomicallyAdequate M translation
        (equalityHead :: combinedPrefix)).
  {
    intros formula [hformula | hformula].
    - subst formula. exact hequalityAdequate.
    - exact (hcombinedPrefix formula hformula).
  }
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_equality_transport_result_on_witnessed_tail_under_prefix
      M hPA translation hagreement sourceWitnessList sourceContext
      (equalityHead :: combinedPrefix)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      fixedLookupRoot equalityRowLookupRoot fixedResult
      equalityFixedResultRoot
      hequalityCombinedPrefix hsource
      hmodeFresh hformulaFresh hassignmentCodeFresh hassignmentStepFresh
      hfixedLookup hequalityRowLookup hequalityFixedResult)
    as (equalityWitnesses & equalityResultRoot &
      hequalityWitnessed & hequalityResult).
  assert (hresultSyntax :
      templateFormulaReplaceParameters
        coqFourStateTableAppendConcreteRowFieldBindings fixedResult = result).
  {
    unfold fixedResult, result.
    exact
      (coqFourStateTableAppendNamedClosedRowProductionTemplate_replace_fields
        sigmaProduction piProduction).
  }
  fold coqFourStateTableAppendConcreteRowFieldBindings in hequalityResult.
  rewrite hresultSyntax in hequalityResult.
  set (equalityWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      equalityWitnesses sourceWitnessList).
  set (equalityContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      equalityWitnesses sourceContext).
  assert (hsourceEqualityIncluded : RawContextListIncluded M
      sourceContext equalityContext).
  {
    unfold equalityContext.
    exact
      (raw_standardPAAxiomWitnessPrefixContextCode_target_included
        M hPA equalityWitnesses sourceContext).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      equalityWitnessList equalityContext combinedPrefix
      (rawTemplateFormula translation antecedent)
      antecedentRoot hsource hequalityWitnessed hsourceEqualityIncluded
      hantecedent)
    as [equalityAntecedentRoot hequalityAntecedent].
  pose proof
    (raw_fourStateTableAppendInheritedLocalRootsAt_transport
      M hPA translation sourceWitnessList sourceContext
      equalityWitnessList equalityContext combinedPrefix
      inheritedTraversal oldLookup hsource hequalityWitnessed
      hsourceEqualityIncluded
      (ex_intro _ prefixedTraversalRoot
        (ex_intro _ prefixedOldLookupRoot
          (conj hprefixedTraversal hprefixedOldLookup))))
    as hequalityInheritedRoots.
  assert (hequalityBranch : forall caseWitnesses,
      RawCodedPAAxiomWitnessContext M
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          caseWitnesses equalityWitnessList)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          caseWitnesses equalityContext) ->
      exists root,
        RawCodedPALocalProofOf M
          (rawListNode M
            (rawTemplateFormula translation equalityHead)
            (rawTemplateContextCodeOnTail translation
              (rawStandardPAAxiomWitnessPrefixContextCode M
                caseWitnesses equalityContext) combinedPrefix))
          (rawTemplateFormula translation result) root).
  {
    intros caseWitnesses hcaseWitnessed.
    set (caseWitnessList :=
      rawStandardPAAxiomWitnessPrefixWitnessListCode M
        caseWitnesses equalityWitnessList).
    set (caseContext :=
      rawStandardPAAxiomWitnessPrefixContextCode M
        caseWitnesses equalityContext).
    assert (hequalityCaseIncluded : RawContextListIncluded M
        equalityContext caseContext).
    {
      unfold caseContext.
      exact
        (raw_standardPAAxiomWitnessPrefixContextCode_target_included
          M hPA caseWitnesses equalityContext).
    }
    destruct
      (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
        M hPA translation equalityWitnessList equalityContext
        caseWitnessList caseContext
        (equalityHead :: combinedPrefix)
        (rawTemplateFormula translation result)
        equalityResultRoot hequalityWitnessed hcaseWitnessed
        hequalityCaseIncluded hequalityResult)
      as [transportedEqualityRoot htransportedEquality].
    exists transportedEqualityRoot.
    exact htransportedEquality.
  }
  assert (hbelowBranch : forall caseWitnesses,
      RawCodedPAAxiomWitnessContext M
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          caseWitnesses equalityWitnessList)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          caseWitnesses equalityContext) ->
      exists root,
        RawCodedPALocalProofOf M
          (rawListNode M
            (rawTemplateFormula translation below)
            (rawTemplateContextCodeOnTail translation
              (rawStandardPAAxiomWitnessPrefixContextCode M
                caseWitnesses equalityContext) combinedPrefix))
          (rawTemplateFormula translation result) root).
  {
    intros caseWitnesses hcaseWitnessed.
    set (caseWitnessList :=
      rawStandardPAAxiomWitnessPrefixWitnessListCode M
        caseWitnesses equalityWitnessList).
    set (caseContext :=
      rawStandardPAAxiomWitnessPrefixContextCode M
        caseWitnesses equalityContext).
    assert (hequalityCaseIncluded : RawContextListIncluded M
        equalityContext caseContext).
    {
      unfold caseContext.
      exact
        (raw_standardPAAxiomWitnessPrefixContextCode_target_included
          M hPA caseWitnesses equalityContext).
    }
    pose proof
      (raw_fourStateTableAppendInheritedLocalRootsAt_transport
        M hPA translation equalityWitnessList equalityContext
        caseWitnessList caseContext combinedPrefix
        inheritedTraversal oldLookup hequalityWitnessed hcaseWitnessed
        hequalityCaseIncluded hequalityInheritedRoots)
      as hcaseInheritedRoots.
    pose proof
      (raw_fourStateTableAppendInheritedProductionInputsAt_of_local_root_package
        M hPA translation caseWitnessList caseContext combinedPrefix
        inheritedTraversal below oldLookup hcaseWitnessed
        hbelowAdequate hcaseInheritedRoots)
      as hpredecessorInputs.
    destruct hpredecessorInputs as
      (caseTraversalRoot & caseBelowRoot & caseOldLookupRoot &
        hcaseTraversal & hcaseBelow & hcaseOldLookup).
    destruct
      (raw_codedPALocalProofOf_four_state_table_append_inherited_row_production
        M hPA translation
        (rawTemplateContextCodeOnTail translation caseContext
          (below :: combinedPrefix))
        inheritedTraversal below oldLookup result
        caseTraversalRoot caseBelowRoot caseOldLookupRoot
        hopen hcaseTraversal hcaseBelow hcaseOldLookup)
      as [predecessorRoot hpredecessor].
    exists predecessorRoot.
    exact hpredecessor.
  }
  destruct
    (raw_codedPALocalProofOf_lt_succ_cases_eliminate_on_witnessed_tail_under_prefix
      M hPA translation hagreement
      equalityWitnessList equalityContext combinedPrefix
      (ttVar 4) rowBound equalityAntecedentRoot
      (rawTemplateFormula translation result)
      hcombinedPrefix hequalityWitnessed hequalityAntecedent
      hbelowBranch hequalityBranch)
    as
    (caseWitnesses & resultRoot & hfinalWitnessed & hresult).
  set (finalContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      caseWitnesses equalityContext).
  fold finalContext in hresult.
  pose proof
    (raw_codedPALocalProofOf_impI M hPA
      (rawTemplateContextCodeOnTail translation finalContext
        (antecedent :: rowPrefix))
      (rawTemplateFormula translation rowLookup)
      (rawTemplateFormula translation result)
      resultRoot hresult) as hlookupImp.
  rewrite <- rawTemplateFormula_imp in hlookupImp.
  pose proof
    (raw_codedPALocalProofOf_impI M hPA
      (rawTemplateContextCodeOnTail translation finalContext rowPrefix)
      (rawTemplateFormula translation antecedent)
      (rawTemplateFormula translation (tfImp rowLookup result))
      (rawProofImpIRoot M
        (rawTemplateContextCodeOnTail translation finalContext
          (antecedent :: rowPrefix))
        (rawTemplateFormula translation rowLookup)
        (rawTemplateFormula translation result) resultRoot)
      hlookupImp) as hboundImp.
  rewrite <- rawTemplateFormula_imp in hboundImp.
  exists (caseWitnesses ++ equalityWitnesses).
  lazymatch type of hboundImp with
  | RawCodedPALocalProofOf _ _ _ ?root => exists root
  end.
  split.
  - rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
    rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
    exact hfinalWitnessed.
  - rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
    exact hboundImp.
Qed.

(** After eight append witnesses and five row eigenvariables, the literal
    append witnesses occupy de Bruijn positions [12] down to [5].  Naming
    them prevents a selected Sigma-implication state root from silently being
    stated at the unrelated outer coordinates [7] down to [0]. *)
Definition coqRestrictedPADirectImpIntroductionAppendWitness7 : TemplateTerm :=
  ttVar 12.
Definition coqRestrictedPADirectImpIntroductionAppendWitness6 : TemplateTerm :=
  ttVar 11.
Definition coqRestrictedPADirectImpIntroductionAppendWitness5 : TemplateTerm :=
  ttVar 10.
Definition coqRestrictedPADirectImpIntroductionAppendWitness4 : TemplateTerm :=
  ttVar 9.
Definition coqRestrictedPADirectImpIntroductionAppendWitness3 : TemplateTerm :=
  ttVar 8.
Definition coqRestrictedPADirectImpIntroductionAppendWitness2 : TemplateTerm :=
  ttVar 7.
Definition coqRestrictedPADirectImpIntroductionAppendWitness1 : TemplateTerm :=
  ttVar 6.
Definition coqRestrictedPADirectImpIntroductionAppendWitness0 : TemplateTerm :=
  ttVar 5.

(** Literal proof-producing boundary for one positive Imp-I body.  This is
    intentionally not a restatement of the desired body compiler: it exposes
    each root consumed by the append-row construction and retains the exact
    root-term/deep-prefix contexts in which those roots must coexist. *)
Definition
    RawCoqRestrictedPADirectImpIntroductionSigmaImpAppendRootsCompilerAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (selection : CoqDynamicTruthSigmaImpSelectedRow)
    (outerPrefix : TemplateContext) : Prop :=
  forall sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  exists (initialWitnesses : StandardPAAxiomWitnessPrefix),
  exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep : TemplateTerm,
  exists appendRoot modeRoot domainRoot codeRoot stateRoot : M,
  exists inheritedTraversal oldLookup : TemplateFormula,
  let targetWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      initialWitnesses sourceWitnessList in
  let targetContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      initialWitnesses sourceContext in
  let witnessContext := coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter coqDynamicTruthAppendRowBoundParameterName)
    (embedPATerm (Term.numeral 0))
    coqRestrictedPADirectAssumptionOuterConclusionTerm
    (ttVar 9) (ttVar 8) outerPrefix in
  let actualRowPrefix := templateContextShiftMany 5 witnessContext in
  let rowPrefix := templateContextShiftMany 5
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      (ttParameter coqFourStateTableAppendRowModeParameterName)
      (ttParameter coqFourStateTableAppendRowFormulaParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName)
      outerPrefix) in
  RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
  (forall tail,
    rawTemplateContextCodeOnTail translation tail rowPrefix =
    rawTemplateContextCodeOnTail translation tail actualRowPrefix) /\
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation targetContext outerPrefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendExistsTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter coqDynamicTruthAppendRowBoundParameterName)
        (embedPATerm (Term.numeral 0))
        coqRestrictedPADirectAssumptionOuterConclusionTerm
        (ttVar 9) (ttVar 8))) appendRoot /\
  templateUniversalOpenMany inheritedTraversal
      coqFourStateTableAppendConcreteRowVariables =
    Some
      (tfImp
        (coqLtSuccCasesBelowTemplate
          (ttVar 4)
          (ttParameter coqDynamicTruthAppendRowBoundParameterName))
        (tfImp oldLookup
          (coqFourStateTableAppendConcreteClosedRowProductionTemplate
            coqDynamicTruthSharedSigmaSuccessorRowTemplate
            coqDynamicTruthSharedPiSuccessorRowTemplate))) /\
  RawFourStateTableAppendInheritedLocalRootsAt M translation
    targetContext rowPrefix inheritedTraversal oldLookup /\
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation targetContext rowPrefix)
    (rawTemplateFormula translation
      coqDynamicTruthSigmaOrModeZeroTemplate) modeRoot /\
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation targetContext rowPrefix)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedDomainAt
        coqRestrictedPADirectImpIntroductionAppendWitness7
        coqRestrictedPADirectImpIntroductionAppendWitness6
        coqRestrictedPADirectImpIntroductionAppendWitness5
        coqRestrictedPADirectImpIntroductionAppendWitness4
        coqRestrictedPADirectImpIntroductionAppendWitness3
        coqRestrictedPADirectImpIntroductionAppendWitness2
        coqRestrictedPADirectImpIntroductionAppendWitness1
        coqRestrictedPADirectImpIntroductionAppendWitness0)) domainRoot /\
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation targetContext rowPrefix)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaImpOpenedCodeAt
        (coqDynamicTruthSigmaImpSelectedLeaf selection)
        coqRestrictedPADirectImpIntroductionAppendWitness7
        coqRestrictedPADirectImpIntroductionAppendWitness6
        coqRestrictedPADirectImpIntroductionAppendWitness5
        coqRestrictedPADirectImpIntroductionAppendWitness4
        coqRestrictedPADirectImpIntroductionAppendWitness3
        coqRestrictedPADirectImpIntroductionAppendWitness2
        coqRestrictedPADirectImpIntroductionAppendWitness1
        coqRestrictedPADirectImpIntroductionAppendWitness0)) codeRoot /\
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation targetContext rowPrefix)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaImpOpenedStateAt
        (coqDynamicTruthSigmaImpSelectedLeaf selection)
        coqRestrictedPADirectImpIntroductionAppendWitness7
        coqRestrictedPADirectImpIntroductionAppendWitness6
        coqRestrictedPADirectImpIntroductionAppendWitness5
        coqRestrictedPADirectImpIntroductionAppendWitness4
        coqRestrictedPADirectImpIntroductionAppendWitness3
        coqRestrictedPADirectImpIntroductionAppendWitness2
        coqRestrictedPADirectImpIntroductionAppendWitness1
        coqRestrictedPADirectImpIntroductionAppendWitness0)) stateRoot.

Arguments
  RawCoqRestrictedPADirectImpIntroductionSigmaImpAppendRootsCompilerAt
  M translation selection outerPrefix : clear implicits.

(** Consume every exposed root and produce the actual standard-tail body
    compiler.  Equality beta functionality and the arithmetic split choose
    their helper batches internally; the returned batch is their explicit
    concatenation with the resource producer's initial batch. *)
Theorem
    raw_restrictedPADirectImpIntroductionPositiveBodyCompilerAt_of_sigma_imp_append_roots :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    selection outerPrefix,
  RawCoqRestrictedPADirectImpIntroductionSigmaImpAppendRootsCompilerAt
    M (rawDirectStructuralTemplateTranslation M hPA inputs)
    selection outerPrefix ->
  RawCoqRestrictedPADirectImpIntroductionPositiveBodyCompilerAt
    M hPA inputs outerPrefix.
Proof.
  intros M hPA inputs selection outerPrefix hresources
    sourceWitnessList sourceContext hsource.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  pose proof (hresources sourceWitnessList sourceContext hsource)
    as hresourcesAtSource.
  cbn zeta in hresourcesAtSource.
  destruct hresourcesAtSource as
    (initialWitnesses &
      modeCode & modeStep & formulaCode & formulaStep &
      assignmentCodeCode & assignmentCodeStep &
      assignmentStepCode & assignmentStepStep &
      appendRoot & modeRoot & domainRoot & codeRoot & stateRoot &
      inheritedTraversal & oldLookup &
      hinitialWitnessed & hrowPrefix & happend & hopen & hinheritedRoots &
      hmode & hdomain & hcode & hstate).
  set (initialWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      initialWitnesses sourceWitnessList).
  set (initialContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      initialWitnesses sourceContext).
  set (witnessContext := coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter coqDynamicTruthAppendRowBoundParameterName)
    (embedPATerm (Term.numeral 0))
    coqRestrictedPADirectAssumptionOuterConclusionTerm
    (ttVar 9) (ttVar 8) outerPrefix).
  set (actualRowPrefix := templateContextShiftMany 5 witnessContext).
  set (rowPrefix := templateContextShiftMany 5
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      (ttParameter coqFourStateTableAppendRowModeParameterName)
      (ttParameter coqFourStateTableAppendRowFormulaParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName)
      outerPrefix)).
  set (antecedent := coqLtSuccCasesAntecedentTemplate
    (ttVar 4) (ttParameter coqDynamicTruthAppendRowBoundParameterName)).
  set (rowLookup :=
    coqFourStateTableAppendEqualityRowLookupTemplate
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)).
  set (extraPrefix := [rowLookup; antecedent]).
  destruct
    (raw_codedPALocalProofOf_dynamic_truth_sigma_imp_fixed_production_of_four_roots
      M hPA translation initialWitnessList initialContext rowPrefix
      (coqDynamicTruthSigmaImpSelectedLeaf selection)
      (coqDynamicTruthSigmaImpSelectedIndex selection)
      coqRestrictedPADirectImpIntroductionAppendWitness7
      coqRestrictedPADirectImpIntroductionAppendWitness6
      coqRestrictedPADirectImpIntroductionAppendWitness5
      coqRestrictedPADirectImpIntroductionAppendWitness4
      coqRestrictedPADirectImpIntroductionAppendWitness3
      coqRestrictedPADirectImpIntroductionAppendWitness2
      coqRestrictedPADirectImpIntroductionAppendWitness1
      coqRestrictedPADirectImpIntroductionAppendWitness0
      modeRoot domainRoot codeRoot stateRoot
      (coqDynamicTruthSigmaImpSelectedOpenedLeafAt_shape
        selection
        coqRestrictedPADirectImpIntroductionAppendWitness7
        coqRestrictedPADirectImpIntroductionAppendWitness6
        coqRestrictedPADirectImpIntroductionAppendWitness5
        coqRestrictedPADirectImpIntroductionAppendWitness4
        coqRestrictedPADirectImpIntroductionAppendWitness3
        coqRestrictedPADirectImpIntroductionAppendWitness2
        coqRestrictedPADirectImpIntroductionAppendWitness1
        coqRestrictedPADirectImpIntroductionAppendWitness0)
      (coqDynamicTruthSigmaImpSelectedOpenedLeafAt_nth
        selection
        coqRestrictedPADirectImpIntroductionAppendWitness7
        coqRestrictedPADirectImpIntroductionAppendWitness6
        coqRestrictedPADirectImpIntroductionAppendWitness5
        coqRestrictedPADirectImpIntroductionAppendWitness4
        coqRestrictedPADirectImpIntroductionAppendWitness3
        coqRestrictedPADirectImpIntroductionAppendWitness2
        coqRestrictedPADirectImpIntroductionAppendWitness1
        coqRestrictedPADirectImpIntroductionAppendWitness0)
      hinitialWitnessed hmode hdomain hcode hstate)
    as [fixedProductionRoot hfixedProduction].
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_equality_fixed_lookup_on_witnessed_tail_under_prefix
      M hPA translation initialWitnessList initialContext
      outerPrefix extraPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      coqDynamicTruthAppendRowBoundParameterName
      (ttParameter coqFourStateTableAppendRowModeParameterName)
      (ttParameter coqFourStateTableAppendRowFormulaParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName)
      (ttVar 4)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      hinitialWitnessed
      (raw_codedTemplatePrefix_atomically_adequate M hPA translation _)
      eq_refl
      (raw_codedTemplateFormula_atomically_adequate M hPA translation _))
    as [fixedLookupRoot hfixedLookup].
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_concrete_closed_row_implications_on_standard_prefix
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      initialWitnessList initialContext rowPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      coqDynamicTruthAppendRowBoundParameterName
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      inheritedTraversal oldLookup fixedLookupRoot fixedProductionRoot
      hinitialWitnessed hopen
      (raw_codedTemplatePrefix_atomically_adequate M hPA translation _)
      (raw_codedTemplateFormula_atomically_adequate M hPA translation _)
      (raw_codedTemplateFormula_atomically_adequate M hPA translation _)
      (raw_codedTemplateFormula_atomically_adequate M hPA translation _)
      eq_refl
      (raw_codedTemplateFormula_atomically_adequate M hPA translation _)
      ltac:(vm_compute; discriminate)
      ltac:(vm_compute; discriminate)
      ltac:(vm_compute; discriminate)
      ltac:(vm_compute; discriminate)
      hfixedLookup hinheritedRoots hfixedProduction)
    as (rowWitnesses & rowRoot & hfinalWitnessed & hrow).
  set (finalWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      rowWitnesses initialWitnessList).
  set (finalContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      rowWitnesses initialContext).
  assert (hinitialFinalIncluded : RawContextListIncluded M
      initialContext finalContext).
  {
    unfold finalContext.
    exact
      (raw_standardPAAxiomWitnessPrefixContextCode_target_included
        M hPA rowWitnesses initialContext).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation initialWitnessList initialContext
      finalWitnessList finalContext outerPrefix
      (rawTemplateFormula translation
        (coqFourStateTableAppendExistsTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter coqDynamicTruthAppendRowBoundParameterName)
          (embedPATerm (Term.numeral 0))
          coqRestrictedPADirectAssumptionOuterConclusionTerm
          (ttVar 9) (ttVar 8)))
      appendRoot hinitialWitnessed hfinalWitnessed
      hinitialFinalIncluded happend)
    as [finalAppendRoot hfinalAppend].
  assert (hrowActual : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation finalContext actualRowPrefix)
      (rawTemplateFormula translation
        (tfImp antecedent
          (tfImp rowLookup
            (coqFourStateTableAppendConcreteClosedRowProductionTemplate
              coqDynamicTruthSharedSigmaSuccessorRowTemplate
              coqDynamicTruthSharedPiSuccessorRowTemplate)))) rowRoot).
  {
    unfold translation, rowPrefix in hrow.
    rewrite (hrowPrefix
      (rawStandardPAAxiomWitnessPrefixContextCode M
        rowWitnesses initialContext)) in hrow.
    exact hrow.
  }
  destruct
    (raw_codedPALocalProofOf_dynamic_truth_shared_global_at_root_terms_of_append_and_concrete_row_on_witnessed_tail
      M hPA translation
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      finalWitnessList finalContext 0
      coqDynamicTruthAppendRowBoundParameterName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      coqRestrictedPADirectAssumptionOuterConclusionTerm
      (ttVar 9) (ttVar 8) outerPrefix
      finalAppendRoot rowRoot
      (or_introl eq_refl)
      coqRestrictedPADirectImpIntroduction_shared_rows_at_root_terms_eq
      hfinalWitnessed hfinalAppend hrowActual)
    as [bodyRoot hbody].
  exists (rowWitnesses ++ initialWitnesses), bodyRoot.
  split.
  - rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
    rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
    exact hfinalWitnessed.
  - rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
    exact hbody.
Qed.

(** The two selections are kept separate at the resource boundary because
    their state roots arise from different predecessor evidence assumptions.
    The constructor below consumes both packages and fills both fields of the
    already published positive-body compiler record. *)
Record RawCoqRestrictedPADirectImpIntroductionPositiveBodyAppendRootCompilers
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop := {
  rawCoqRestrictedPADirectImpIntroduction_falseLeftAppendRoots :
    RawCoqRestrictedPADirectImpIntroductionSigmaImpAppendRootsCompilerAt
      M (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthSigmaImpSelectFalseLeft
      coqRestrictedPADirectImpIntroductionFalsePositiveBodyPrefix;
  rawCoqRestrictedPADirectImpIntroduction_trueRightAppendRoots :
    RawCoqRestrictedPADirectImpIntroductionSigmaImpAppendRootsCompilerAt
      M (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqDynamicTruthSigmaImpSelectTrueRight
      coqRestrictedPADirectImpIntroductionTruePositiveBodyPrefix
}.

Arguments
  RawCoqRestrictedPADirectImpIntroductionPositiveBodyAppendRootCompilers
  M hPA inputs : clear implicits.

Theorem
    raw_restrictedPADirectImpIntroductionPositiveBodyCompilers_of_literal_append_roots :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectImpIntroductionPositiveBodyAppendRootCompilers
    M hPA inputs ->
  RawCoqRestrictedPADirectImpIntroductionPositiveBodyCompilers
    M hPA inputs.
Proof.
  intros M hPA inputs [hfalse htrue].
  constructor.
  - exact
      (raw_restrictedPADirectImpIntroductionPositiveBodyCompilerAt_of_sigma_imp_append_roots
        M hPA inputs coqDynamicTruthSigmaImpSelectFalseLeft
        coqRestrictedPADirectImpIntroductionFalsePositiveBodyPrefix hfalse).
  - exact
      (raw_restrictedPADirectImpIntroductionPositiveBodyCompilerAt_of_sigma_imp_append_roots
        M hPA inputs coqDynamicTruthSigmaImpSelectTrueRight
        coqRestrictedPADirectImpIntroductionTruePositiveBodyPrefix htrue).
Qed.

End
  PABoundedRawCodedRestrictedPADirectImpIntroductionPositiveBodyAppendProduction.
