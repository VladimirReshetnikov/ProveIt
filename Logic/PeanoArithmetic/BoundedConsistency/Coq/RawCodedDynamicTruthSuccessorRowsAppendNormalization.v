(**
  Normalize the native dynamic-truth successor rows for append traversal.

  The generalized append compiler accepts arbitrary opaque row templates,
  but its concrete equality branch still performs two purely syntactic
  operations: it replaces the four row-field parameters and later opens the
  row beneath thirteen de Bruijn slots.  Native Sigma/Pi successor rows use
  only level parameters zero and one, while their free indices are already
  below that scope.  This module proves those facts once for the relocated
  two-predicate spelling used by the shared direct translator.

  Scope is checked through the reflected Boolean predicate.  This keeps the
  kernel proof term compact even though each fixed row contains many quoted
  arithmetic subformulae.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateRenamingSubstitution
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedLtSuccCasesProofCompilation
  RawCodedFourStateTableAppendSource
  RawCodedFourStateTableAppendProofCompilation
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedFourStateTableAppendGlobalTraversalAssembly
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedPALocalProofEquality
  RawCodedTemplateTripleUniversalOpening
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedRestrictedPADerivationSoundnessExtendedDirectInputs
  RawCodedFourStateTableAppendTemplateGlobalTraversalAssembly.

Module PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateRenamingSubstitution.
Import PABoundedRawCodedPALocalProofEquality.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedFourStateTableAppendSource.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedTemplateTripleUniversalOpening.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
Import
  PABoundedRawCodedFourStateTableAppendTemplateGlobalTraversalAssembly.

Definition coqDynamicTruthSharedSigmaSuccessorRowTemplate : TemplateFormula :=
  coqDynamicTruthSigmaSuccessorRowTemplateAt
    coqRestrictedPALowerPiTruthPredicateName.

Definition coqDynamicTruthSharedPiSuccessorRowTemplate : TemplateFormula :=
  coqDynamicTruthPiSuccessorRowTemplateAt
    coqRestrictedPALowerSigmaTruthPredicateName.

Lemma coqDynamicTruthSharedSigmaSuccessorRowTemplate_scoped_13 :
  TemplateFormulaScoped 13
    coqDynamicTruthSharedSigmaSuccessorRowTemplate.
Proof.
  apply (proj1 (templateFormulaScopedBool_iff 13
    coqDynamicTruthSharedSigmaSuccessorRowTemplate)).
  vm_compute.
  reflexivity.
Qed.

Lemma coqDynamicTruthSharedPiSuccessorRowTemplate_scoped_13 :
  TemplateFormulaScoped 13
    coqDynamicTruthSharedPiSuccessorRowTemplate.
Proof.
  apply (proj1 (templateFormulaScopedBool_iff 13
    coqDynamicTruthSharedPiSuccessorRowTemplate)).
  vm_compute.
  reflexivity.
Qed.

(** Append replaces only named parameters 2--5.  The two native rows reserve
    names 0 and 1 for the lower and upper hierarchy numerals, hence the
    replacement is inert. *)
Lemma coqDynamicTruthSharedSigmaSuccessorRowTemplate_append_fields_inert :
  templateFormulaReplaceParametersDirect
      coqFourStateTableAppendConcreteRowFieldBindings
      coqDynamicTruthSharedSigmaSuccessorRowTemplate =
    coqDynamicTruthSharedSigmaSuccessorRowTemplate.
Proof. vm_compute. reflexivity. Qed.

Lemma coqDynamicTruthSharedPiSuccessorRowTemplate_append_fields_inert :
  templateFormulaReplaceParametersDirect
      coqFourStateTableAppendConcreteRowFieldBindings
      coqDynamicTruthSharedPiSuccessorRowTemplate =
    coqDynamicTruthSharedPiSuccessorRowTemplate.
Proof. vm_compute. reflexivity. Qed.

(** The concrete equality-branch production is therefore definitionally the
    production extracted from either generalized global source. *)
Theorem coqDynamicTruthSharedSuccessorRows_append_production : forall
    rootMode bound,
  coqFourStateTableAppendConcreteClosedRowProductionTemplate
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate =
    coqFourStateTableAppendOpenedTemplateGlobalRowProduction
      rootMode
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate bound.
Proof.
  intros rootMode bound.
  apply coqFourStateTableAppendTemplateClosedRowProduction_eq_opened.
  - exact coqDynamicTruthSharedSigmaSuccessorRowTemplate_scoped_13.
  - exact coqDynamicTruthSharedPiSuccessorRowTemplate_scoped_13.
  - exact
      coqDynamicTruthSharedSigmaSuccessorRowTemplate_append_fields_inert.
  - exact coqDynamicTruthSharedPiSuccessorRowTemplate_append_fields_inert.
Qed.

(** Native-row specialization of the proof-producing append endpoint.  The
    large syntactic equality is intentionally absent from this interface:
    the preceding normalization theorem supplies it for both root modes. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_shared_successor_global_of_append_row :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses appendRoot,
  rootMode = 0 \/ rootMode = 1 ->
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
        (ttVar 0) (ttVar 1) (ttVar 2))) appendRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (coqFourStateTableAppendRowPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName)
      (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2))
    (rawTemplateFormula translation
      (tfImp
        (coqLtSuccCasesAntecedentTemplate
          (ttVar 4) (ttParameter boundName))
        (tfImp
          (coqFourStateTableAppendEqualityRowLookupTemplate
            coqFourStateTableAppendRowModeParameterName
            coqFourStateTableAppendRowFormulaParameterName
            coqFourStateTableAppendRowAssignmentCodeParameterName
            coqFourStateTableAppendRowAssignmentStepParameterName
            (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0))
          (coqFourStateTableAppendConcreteClosedRowProductionTemplate
            coqDynamicTruthSharedSigmaSuccessorRowTemplate
            coqDynamicTruthSharedPiSuccessorRowTemplate)))) ->
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
  intros M hPA translation hagreement
    rootMode boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses appendRoot hrootMode happend hrow.
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_template_global_of_append_concrete_row
      M hPA translation hagreement
      rootMode
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      witnesses
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      appendRoot hrootMode
      (coqDynamicTruthSharedSuccessorRows_append_production
        rootMode (ttParameter boundName))
      happend hrow).
Qed.

(** Prefix-flexible native client.  Equality is required only after
    translation and uniformly in the raw tail, which admits named carrier
    parameters and concrete de Bruijn terms as interchangeable compiler
    presentations. *)
Corollary
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_shared_successor_global_of_append_code_equivalent_row_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses appendRoot rowPrefix,
  rootMode = 0 \/ rootMode = 1 ->
  (forall tail,
    rawTemplateContextCodeOnTail translation tail rowPrefix =
    rawTemplateContextCodeOnTail translation tail
      (coqFourStateTableAppendRowPrefix
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName)
        (embedPATerm (Term.numeral rootMode))
        (ttVar 0) (ttVar 1) (ttVar 2))) ->
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
        (ttVar 0) (ttVar 1) (ttVar 2))) appendRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) rowPrefix
    (rawTemplateFormula translation
      (tfImp
        (coqLtSuccCasesAntecedentTemplate
          (ttVar 4) (ttParameter boundName))
        (tfImp
          (coqFourStateTableAppendEqualityRowLookupTemplate
            coqFourStateTableAppendRowModeParameterName
            coqFourStateTableAppendRowFormulaParameterName
            coqFourStateTableAppendRowAssignmentCodeParameterName
            coqFourStateTableAppendRowAssignmentStepParameterName
            (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0))
          (coqFourStateTableAppendConcreteClosedRowProductionTemplate
            coqDynamicTruthSharedSigmaSuccessorRowTemplate
            coqDynamicTruthSharedPiSuccessorRowTemplate)))) ->
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
  intros M hPA translation hagreement
    rootMode boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses appendRoot rowPrefix
    hrootMode hprefix happend hrow.
  apply
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_shared_successor_global_of_append_row
      M hPA translation hagreement
      rootMode boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      witnesses appendRoot hrootMode happend).
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_prefix_code_eq
      M translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      rowPrefix
      (coqFourStateTableAppendRowPrefix
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName)
        (embedPATerm (Term.numeral rootMode))
        (ttVar 0) (ttVar 1) (ttVar 2))
      (rawTemplateFormula translation
        (tfImp
          (coqLtSuccCasesAntecedentTemplate
            (ttVar 4) (ttParameter boundName))
          (tfImp
            (coqFourStateTableAppendEqualityRowLookupTemplate
              coqFourStateTableAppendRowModeParameterName
              coqFourStateTableAppendRowFormulaParameterName
              coqFourStateTableAppendRowAssignmentCodeParameterName
              coqFourStateTableAppendRowAssignmentStepParameterName
              (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0))
            (coqFourStateTableAppendConcreteClosedRowProductionTemplate
              coqDynamicTruthSharedSigmaSuccessorRowTemplate
              coqDynamicTruthSharedPiSuccessorRowTemplate))))
      hprefix hrow).
Qed.

(** Parameter names two through five are reserved by the append equality
    branch for the four selected row fields.  Name six is therefore a
    concrete fresh choice for the traversal bound; fixing it here removes
    four irrelevant freshness premises from the native client. *)
Definition coqDynamicTruthAppendRowBoundParameterName
    : TemplateParameterName := 6.

(** Compose the complete generic row case compiler with the native opaque-row
    global closure.  The equality [hprefix] is deliberately retained as a
    translated context-code premise: clients may realize the four named row
    witnesses by any carrier terms, without changing the structural
    translation or claiming equality of template syntax.

    All arithmetic atomic-adequacy obligations and all parameter freshness
    checks are discharged internally.  The only proof-producing resources
    left visible are precisely those used by the two branches of the row
    compiler and by the append existential eliminator. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_shared_successor_global_of_append_and_inherited_row_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses appendRoot inheritedTraversal oldLookup fixedProductionRoot,
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
  rootMode = 0 \/ rootMode = 1 ->
  (forall tail,
    rawTemplateContextCodeOnTail translation tail namedRowPrefix =
    rawTemplateContextCodeOnTail translation tail
      (coqFourStateTableAppendRowPrefix
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName)
        (embedPATerm (Term.numeral rootMode))
        (ttVar 0) (ttVar 1) (ttVar 2))) ->
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
      (coqFourStateTableAppendNamedClosedRowProductionTemplate
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate))
    fixedProductionRoot ->
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
  intros M hPA translation hagreement rootMode
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses appendRoot inheritedTraversal oldLookup fixedProductionRoot
    boundName namedRowPrefix hrootMode hprefix happend hopen
    hinherited hfixedProduction.
  cbn zeta in *.
  apply
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_shared_successor_global_of_append_code_equivalent_row_prefix
      M hPA translation hagreement rootMode boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      witnesses appendRoot namedRowPrefix
      hrootMode hprefix happend).
  exact
    (raw_codedPALocalProofOf_four_state_table_append_concrete_closed_row_implications_on_witnessed_row_context
      M hPA translation hagreement
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      boundName (ttParameter boundName)
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      inheritedTraversal oldLookup witnesses fixedProductionRoot
      hopen
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
      hinherited hfixedProduction).
Qed.

End PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
