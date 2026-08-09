(**
  Feed the two positive Sigma implication rows into the append compiler.

  The finite fixed-production compiler proves either ImpFalseLeft or
  ImpTrueRight from four represented roots in one named-row context.  The
  append compiler already knows how to combine such a fixed row with the
  inherited rows and close the global traversal.  This file records their
  direct composition; in particular, no implication-truth law is assumed or
  produced here.

  [CoqDynamicTruthSigmaImpSelectedRow] deliberately has exactly two
  constructors.  Its leaf and branch-index projections make the literal
  positions 1 and 2 in the shared Sigma disjunction auditable while letting
  the append theorem cover both rows without duplicating its long structural
  argument list.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedLtSuccCasesProofCompilation
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplatePAEmbedding
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedTemplateDisjunctionCaseSchemas
  RawCodedFourStateTableAppendProofCompilation
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthSigmaOrFixedProductionTemplate
  RawCodedDynamicTruthSigmaImpFixedProductionCompilation.

Module
  PABoundedRawCodedDynamicTruthSigmaImpFixedProductionAppendIntegration.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedTemplateDisjunctionCaseSchemas.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplate.
Import PABoundedRawCodedDynamicTruthSigmaImpFixedProductionCompilation.

(** The only two positive implication leaves needed by the direct Imp-I
    proof.  The constructor names state the semantic branch selected by the
    corresponding row. *)
Inductive CoqDynamicTruthSigmaImpSelectedRow : Set :=
| coqDynamicTruthSigmaImpSelectFalseLeft
| coqDynamicTruthSigmaImpSelectTrueRight.

Definition coqDynamicTruthSigmaImpSelectedLeaf
    (selection : CoqDynamicTruthSigmaImpSelectedRow) : TemplateFormula :=
  match selection with
  | coqDynamicTruthSigmaImpSelectFalseLeft =>
      coqDynamicTruthSigmaImpFalseLeftLeafTemplate
  | coqDynamicTruthSigmaImpSelectTrueRight =>
      coqDynamicTruthSigmaImpTrueRightLeafTemplate
  end.

Definition coqDynamicTruthSigmaImpSelectedIndex
    (selection : CoqDynamicTruthSigmaImpSelectedRow) : nat :=
  match selection with
  | coqDynamicTruthSigmaImpSelectFalseLeft => 1
  | coqDynamicTruthSigmaImpSelectTrueRight => 2
  end.

(** Both equalities are computational.  Keeping them as named lemmas makes
    it explicit that the later append proof selects existing branches rather
    than postulating a row lookup. *)
Lemma coqDynamicTruthSigmaImpSelectedOpenedLeafAt_shape : forall
    selection witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0,
  coqDynamicTruthSigmaImpOpenedLeafAt
      (coqDynamicTruthSigmaImpSelectedLeaf selection)
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 =
    coqDynamicTruthSigmaImpExpectedOpenedLeafAt
      (coqDynamicTruthSigmaImpSelectedLeaf selection)
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0.
Proof. intros []; reflexivity. Qed.

Lemma coqDynamicTruthSigmaImpSelectedOpenedLeafAt_nth : forall
    selection witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0,
  templateRightDisjunctionBranchAt
    (coqDynamicTruthSigmaOrOpenedBranchPrefixAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedUniversalAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaImpSelectedIndex selection) =
    Some (coqDynamicTruthSigmaImpOpenedLeafAt
      (coqDynamicTruthSigmaImpSelectedLeaf selection)
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0).
Proof. intros []; reflexivity. Qed.

(** Compose a selected positive implication row with append and inherited
    row traversal at Sigma mode zero.  Every represented source root stays
    in the literal named-row context expected by the append compiler. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_shared_sigma_global_of_append_inherited_and_selected_sigma_imp_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses appendRoot inheritedTraversal oldLookup
    selection
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    modeRoot domainRoot codeRoot stateRoot,
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
  (forall tail,
    rawTemplateContextCodeOnTail translation tail namedRowPrefix =
    rawTemplateContextCodeOnTail translation tail
      (coqFourStateTableAppendRowPrefix
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral 0))
        (ttVar 0) (ttVar 1) (ttVar 2))) ->
  RawCodedPALocalProofOf M
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (rawTemplateFormula translation
      (coqFourStateTableAppendExistsTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral 0))
        (ttVar 0) (ttVar 1) (ttVar 2))) appendRoot ->
  templateUniversalOpenMany inheritedTraversal
      coqFourStateTableAppendConcreteRowVariables =
    Some
      (tfImp
        (coqLtSuccCasesBelowTemplate
          (ttVar 4) (ttParameter boundName))
        (tfImp oldLookup
          (coqFourStateTableAppendConcreteClosedRowProductionTemplate
            coqDynamicTruthSharedSigmaSuccessorRowTemplate
            coqDynamicTruthSharedPiSuccessorRowTemplate))) ->
  RawFourStateTableAppendInheritedLocalRootsAt M translation
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    namedRowPrefix inheritedTraversal oldLookup ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) namedRowPrefix)
    (rawTemplateFormula translation
      coqDynamicTruthSigmaOrModeZeroTemplate) modeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) namedRowPrefix)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedDomainAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) domainRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) namedRowPrefix)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaImpOpenedCodeAt
        (coqDynamicTruthSigmaImpSelectedLeaf selection)
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) codeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) namedRowPrefix)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaImpOpenedStateAt
        (coqDynamicTruthSigmaImpSelectedLeaf selection)
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) stateRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) []
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate)).
Proof.
  intros M hPA translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses appendRoot inheritedTraversal oldLookup
    selection
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    modeRoot domainRoot codeRoot stateRoot
    boundName namedRowPrefix hprefix happend hopen hinherited
    hmode hdomain hcode hstate.
  cbn zeta in *.
  pose proof (raw_templateEmbeddedPAAxiomWitnessContext
    M hPA translation hagreement witnesses) as hbase.
  rewrite (raw_templateContextCode_embedPAAxiomWitnesses
    M translation hagreement witnesses) in hbase.
  destruct
    (raw_codedPALocalProofOf_dynamic_truth_sigma_imp_fixed_production_of_four_roots
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      namedRowPrefix
      (coqDynamicTruthSigmaImpSelectedLeaf selection)
      (coqDynamicTruthSigmaImpSelectedIndex selection)
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0
      modeRoot domainRoot codeRoot stateRoot
      (coqDynamicTruthSigmaImpSelectedOpenedLeafAt_shape
        selection witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)
      (coqDynamicTruthSigmaImpSelectedOpenedLeafAt_nth
        selection witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)
      hbase hmode hdomain hcode hstate) as
    [fixedProductionRoot hfixed].
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_shared_successor_global_of_append_and_inherited_row_roots
      M hPA translation hagreement 0
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      witnesses appendRoot inheritedTraversal oldLookup fixedProductionRoot
      (or_introl eq_refl) hprefix happend hopen hinherited hfixed).
Qed.

End
  PABoundedRawCodedDynamicTruthSigmaImpFixedProductionAppendIntegration.
