(**
  Reconstruct native global evidence directly from append traversal.

  The ordinary append endpoint closes a ternary global source whose free
  arguments are presented as variables [0,1,2].  Native derivation soundness
  applies the same predicate to [2,1,0].  The latter is definitionally the
  explicit three-slot renaming isolated by
  [RawCodedDynamicTruthNativeGlobalEvidencePermutation].

  All lower append compilers are already parametric in the root formula and
  assignment terms.  This file therefore reuses them with the reversed tuple,
  proves the corresponding finite opened-body shape, introduces the ten
  global witnesses, and eliminates the eight append witnesses.  No general
  proof-code renaming principle is assumed.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedPAGrowingTemplateConjunction
  RawCodedLtSuccCasesProofCompilation
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofExistentialIntroductionChain
  RawCodedFourStateTableAppendSource
  RawCodedFourStateTableAppendProofCompilation
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedFourStateTableAppendGlobalTraversalAssembly
  RawCodedFourStateTableAppendTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthNativeGlobalEvidencePermutation.

Module
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedPAGrowingTemplateConjunction.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofExistentialIntroductionChain.
Import PABoundedRawCodedFourStateTableAppendSource.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
Import
  PABoundedRawCodedFourStateTableAppendTemplateGlobalTraversalAssembly.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import
  PABoundedRawCodedDynamicTruthNativeGlobalEvidencePermutation.

Definition coqFourStateTableAppendPermutedTemplateGlobalSource
    (rootMode : nat) (localSigma localPi : TemplateFormula)
    : TemplateFormula :=
  templateFormulaRename templateReverseFirstThreeRenaming
    (coqDynamicTruthGlobalExistentialSource
      rootMode localSigma localPi).

Definition coqFourStateTableAppendOpenedPermutedTemplateGlobalFormula
    (rootMode : nat) (localSigma localPi : TemplateFormula)
    (bound : TemplateTerm) : TemplateFormula :=
  match templateExistentialOpenMany
    (templateFormulaShiftMany 8
      (coqFourStateTableAppendPermutedTemplateGlobalSource
        rootMode localSigma localPi))
    (coqFourStateTableAppendGlobalTraversalWitnesses bound) with
  | Some body => body
  | None => tfBot
  end.

Lemma coqFourStateTableAppendOpenedPermutedTemplateGlobalFormula_success :
  forall rootMode localSigma localPi bound,
  templateExistentialOpenMany
    (templateFormulaShiftMany 8
      (coqFourStateTableAppendPermutedTemplateGlobalSource
        rootMode localSigma localPi))
    (coqFourStateTableAppendGlobalTraversalWitnesses bound) =
  Some (coqFourStateTableAppendOpenedPermutedTemplateGlobalFormula
    rootMode localSigma localPi bound).
Proof. intros. reflexivity. Qed.

(** Reversing the root tuple changes the first six certificate fields but
    not the universal row law: the shared local rows are scoped below the
    three outer global arguments.  Naming the seventh projection keeps the
    proof-producing premise independent of this observation. *)
Definition coqFourStateTableAppendOpenedPermutedTemplateGlobalRows
    (rootMode : nat) (localSigma localPi : TemplateFormula)
    (bound : TemplateTerm) : TemplateFormula :=
  templateAnd7Seventh
    (coqFourStateTableAppendOpenedPermutedTemplateGlobalFormula
      rootMode localSigma localPi bound).

Lemma coqFourStateTableAppendOpenedPermutedTemplateGlobalFormula_shape :
  forall rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep,
  rootMode = 0 \/ rootMode = 1 ->
  coqFourStateTableAppendOpenedPermutedTemplateGlobalFormula
    rootMode localSigma localPi (ttParameter boundName) =
  coqFourStateTableAppendTraversalBodyTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName)
    (embedPATerm (Term.numeral rootMode))
    (ttVar 2) (ttVar 1) (ttVar 0)
    (coqFourStateTableAppendOpenedPermutedTemplateGlobalRows
      rootMode localSigma localPi (ttParameter boundName)).
Proof.
  intros rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep [-> | ->];
    reflexivity.
Qed.

(** The three outer arguments do not occur free in either shared successor
    row after it is installed beneath the ten traversal and five row binders.
    Consequently reversing those arguments leaves the seventh field
    unchanged.  This is a finite normalization of the two fixed rows. *)
Lemma coqFourStateTableAppendOpenedPermutedSharedGlobalRows_eq :
  forall rootMode bound,
  rootMode = 0 \/ rootMode = 1 ->
  coqFourStateTableAppendOpenedPermutedTemplateGlobalRows rootMode
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate bound =
  coqFourStateTableAppendOpenedTemplateGlobalRows rootMode
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate bound.
Proof.
  intros rootMode bound [-> | ->]; vm_compute; reflexivity.
Qed.

(** Generalize the existing seventh-field compiler over the three root
    terms.  Only the surrounding append prefix changes; the universally
    quantified row implication and its production normalization are shared. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_opened_template_global_rows_of_concrete_row_at_root_terms_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    rootMode (localSigma localPi : TemplateFormula) boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    rootFormula rootAssignmentCode rootAssignmentStep
    outerPrefix witnesses sigmaProduction piProduction,
  coqFourStateTableAppendConcreteClosedRowProductionTemplate
      sigmaProduction piProduction =
    coqFourStateTableAppendOpenedTemplateGlobalRowProduction
      rootMode localSigma localPi (ttParameter boundName) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (templateContextShiftMany 5
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
        rootFormula rootAssignmentCode rootAssignmentStep outerPrefix))
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
            sigmaProduction piProduction)))) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      rootFormula rootAssignmentCode rootAssignmentStep outerPrefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendOpenedTemplateGlobalRows
        rootMode localSigma localPi (ttParameter boundName))).
Proof.
  intros M hPA translation
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    rootFormula rootAssignmentCode rootAssignmentStep
    outerPrefix witnesses sigmaProduction piProduction
    hproduction hrow.
  set (witnessContext :=
    coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      rootFormula rootAssignmentCode rootAssignmentStep outerPrefix).
  set (antecedent := coqLtSuccCasesAntecedentTemplate
    (ttVar 4) (ttParameter boundName)).
  set (rowLookup :=
    coqFourStateTableAppendEqualityRowLookupTemplate
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)).
  set (openedProduction :=
    coqFourStateTableAppendOpenedTemplateGlobalRowProduction
      rootMode localSigma localPi (ttParameter boundName)).
  assert (hrowOpened : RawCodedPAGrowingTemplateLocalProofAt M translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (templateContextShiftMany 5 witnessContext)
      (rawTemplateFormula translation
        (tfImp antecedent (tfImp rowLookup openedProduction)))).
  {
    apply (raw_codedPAGrowingTemplateLocalProofAt_conclusion_eq
      M translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (templateContextShiftMany 5 witnessContext)
      (rawTemplateFormula translation
        (tfImp antecedent
          (tfImp rowLookup
            (coqFourStateTableAppendConcreteClosedRowProductionTemplate
              sigmaProduction piProduction))))
      (rawTemplateFormula translation
        (tfImp antecedent (tfImp rowLookup openedProduction)))).
    - unfold openedProduction. now rewrite <- hproduction.
    - exact hrow.
  }
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_universal_introduction_chain
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      5 witnessContext
      (tfImp antecedent (tfImp rowLookup openedProduction))
      hrowOpened) as hall5.
  unfold antecedent, rowLookup, openedProduction, witnessContext in hall5.
  rewrite coqFourStateTableAppendOpenedTemplateGlobalRows_shape.
  exact hall5.
Qed.

Theorem
    raw_codedPAGrowingTemplateLocalProofAt_opened_template_global_rows_of_concrete_row_at_root_terms :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    rootMode (localSigma localPi : TemplateFormula) boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    rootFormula rootAssignmentCode rootAssignmentStep
    witnesses sigmaProduction piProduction,
  coqFourStateTableAppendConcreteClosedRowProductionTemplate
      sigmaProduction piProduction =
    coqFourStateTableAppendOpenedTemplateGlobalRowProduction
      rootMode localSigma localPi (ttParameter boundName) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (coqFourStateTableAppendRowPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      rootFormula rootAssignmentCode rootAssignmentStep)
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
            sigmaProduction piProduction)))) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      rootFormula rootAssignmentCode rootAssignmentStep [])
    (rawTemplateFormula translation
      (coqFourStateTableAppendOpenedTemplateGlobalRows
        rootMode localSigma localPi (ttParameter boundName))).
Proof.
  intros M hPA translation
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    rootFormula rootAssignmentCode rootAssignmentStep
    witnesses sigmaProduction piProduction hproduction hrow.
  assert (hrowOpened : RawCodedPAGrowingTemplateLocalProofAt M translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqFourStateTableAppendRowPrefix
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
        rootFormula rootAssignmentCode rootAssignmentStep)
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
            (coqFourStateTableAppendOpenedTemplateGlobalRowProduction
              rootMode localSigma localPi (ttParameter boundName)))))).
  {
    apply (raw_codedPAGrowingTemplateLocalProofAt_conclusion_eq
      M translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqFourStateTableAppendRowPrefix
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
        rootFormula rootAssignmentCode rootAssignmentStep)
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
              sigmaProduction piProduction))))
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
            (coqFourStateTableAppendOpenedTemplateGlobalRowProduction
              rootMode localSigma localPi (ttParameter boundName)))))).
    - now rewrite hproduction.
    - exact hrow.
  }
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_four_state_table_append_row_all5
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      rootFormula rootAssignmentCode rootAssignmentStep
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
          (coqFourStateTableAppendOpenedTemplateGlobalRowProduction
            rootMode localSigma localPi (ttParameter boundName))))
      hrowOpened) as hall5.
  rewrite coqFourStateTableAppendOpenedTemplateGlobalRows_shape.
  exact hall5.
Qed.

(** Close the reversed global formula from its seventh traversal field.  The
    statement mirrors the generic opaque-row endpoint, but every occurrence
    of the root tuple is consistently [2,1,0]. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_template_global_of_append_rows_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode (localSigma localPi : TemplateFormula) boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    outerPrefix witnesses appendRoot,
  rootMode = 0 \/ rootMode = 1 ->
  let sourceWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M) in
  let sourceContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M) in
  let bound := ttParameter boundName in
  let mode := embedPATerm (Term.numeral rootMode) in
  let formula := ttVar 2 in
  let assignmentCode := ttVar 1 in
  let assignmentStep := ttVar 0 in
  let prefix := coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep outerPrefix in
  let opened :=
    coqFourStateTableAppendOpenedPermutedTemplateGlobalFormula
      rootMode localSigma localPi bound in
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext outerPrefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendExistsTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep)) appendRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext prefix
    (rawTemplateFormula translation (templateAnd7Seventh opened)) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext outerPrefix
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource
        rootMode localSigma localPi)).
Proof.
  intros M hPA translation hagreement
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    outerPrefix witnesses appendRoot hrootMode
    sourceWitnessList sourceContext bound mode formula
    assignmentCode assignmentStep prefix opened happend hrows.
  cbn zeta in *.
  assert (hsource : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement witnesses) as hwitnessed.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hwitnessed.
    exact hwitnessed.
  }
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_four_state_table_append_traversal_body_under_prefix
      M hPA translation hagreement
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      (ttVar 2) (ttVar 1) (ttVar 0)
      outerPrefix witnesses
      (coqFourStateTableAppendOpenedPermutedTemplateGlobalRows
        rootMode localSigma localPi (ttParameter boundName)) hrows)
    as hbody.
  pose proof
    (coqFourStateTableAppendOpenedPermutedTemplateGlobalFormula_shape
      rootMode localSigma localPi boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep hrootMode)
    as hopenedShape.
  rewrite <- hopenedShape in hbody.
  destruct hbody as
    (finalWitnessList & finalContext & bodyRoot &
      hfinal & hincluded & hbody).
  destruct
    (raw_codedPALocalProofOf_templateExistentialOpenMany
      M hPA translation
      (rawTemplateContextCodeOnTail translation finalContext
        (coqFourStateTableAppendWitnessContext
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
          (ttVar 2) (ttVar 1) (ttVar 0) outerPrefix))
      (templateFormulaShiftMany 8
        (coqFourStateTableAppendPermutedTemplateGlobalSource
          rootMode localSigma localPi))
      (coqFourStateTableAppendGlobalTraversalWitnesses
        (ttParameter boundName))
      (coqFourStateTableAppendOpenedPermutedTemplateGlobalFormula
        rootMode localSigma localPi (ttParameter boundName))
      bodyRoot
      (coqFourStateTableAppendOpenedPermutedTemplateGlobalFormula_success
        rootMode localSigma localPi (ttParameter boundName)) hbody)
    as [globalRoot hglobal].
  assert (hcontinuation : RawCodedPAGrowingTemplateLocalProofAt M translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
        (ttVar 2) (ttVar 1) (ttVar 0) outerPrefix)
      (rawTemplateFormula translation
        (templateFormulaShiftMany 8
          (coqFourStateTableAppendPermutedTemplateGlobalSource
            rootMode localSigma localPi)))).
  {
    unfold RawCodedPAGrowingTemplateLocalProofAt.
    exists finalWitnessList, finalContext, globalRoot.
    split; [exact hfinal |].
    split; [exact hincluded | exact hglobal].
  }
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_four_state_table_append_ex8_elimination_under_prefix
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      outerPrefix
      (coqFourStateTableAppendPermutedTemplateGlobalSource
        rootMode localSigma localPi)
      appendRoot
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      (ttVar 2) (ttVar 1) (ttVar 0)
      hsource happend hcontinuation).
Qed.

(** Empty-prefix compatibility specialization. *)
Corollary
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_template_global_of_append_rows :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode (localSigma localPi : TemplateFormula) boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses appendRoot,
  rootMode = 0 \/ rootMode = 1 ->
  let sourceWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M) in
  let sourceContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M) in
  let bound := ttParameter boundName in
  let mode := embedPATerm (Term.numeral rootMode) in
  let formula := ttVar 2 in
  let assignmentCode := ttVar 1 in
  let assignmentStep := ttVar 0 in
  let prefix := coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep [] in
  let opened :=
    coqFourStateTableAppendOpenedPermutedTemplateGlobalFormula
      rootMode localSigma localPi bound in
  RawCodedPALocalProofOf M sourceContext
    (rawTemplateFormula translation
      (coqFourStateTableAppendExistsTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep)) appendRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext prefix
    (rawTemplateFormula translation (templateAnd7Seventh opened)) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext []
    (rawTemplateFormula translation
      (coqFourStateTableAppendPermutedTemplateGlobalSource
        rootMode localSigma localPi)).
Proof.
  intros M hPA translation hagreement
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses appendRoot hrootMode
    sourceWitnessList sourceContext bound mode formula
    assignmentCode assignmentStep prefix opened happend hrows.
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_template_global_of_append_rows_under_prefix
      M hPA translation hagreement rootMode localSigma localPi boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep [] witnesses appendRoot
      hrootMode happend hrows).
Qed.

(** Native shared-row specialization of the reversed reconstruction. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_shared_successor_global_of_append_row :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep witnesses appendRoot,
  rootMode = 0 \/ rootMode = 1 ->
  RawCodedPALocalProofOf M
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (rawTemplateFormula translation
      (coqFourStateTableAppendExistsTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
        (ttVar 2) (ttVar 1) (ttVar 0))) appendRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (coqFourStateTableAppendRowPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      (ttVar 2) (ttVar 1) (ttVar 0))
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
      (coqFourStateTableAppendPermutedTemplateGlobalSource rootMode
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate)).
Proof.
  intros M hPA translation hagreement rootMode boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep witnesses appendRoot
    hrootMode happend hrow.
  apply
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_template_global_of_append_rows
      M hPA translation hagreement rootMode
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep witnesses appendRoot
      hrootMode happend).
  change (RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      (ttVar 2) (ttVar 1) (ttVar 0) [])
    (rawTemplateFormula translation
      (coqFourStateTableAppendOpenedPermutedTemplateGlobalRows
        rootMode coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate
        (ttParameter boundName)))).
  rewrite
    (coqFourStateTableAppendOpenedPermutedSharedGlobalRows_eq
      rootMode (ttParameter boundName) hrootMode).
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_opened_template_global_rows_of_concrete_row_at_root_terms
      M hPA translation rootMode
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttVar 2) (ttVar 1) (ttVar 0)
      witnesses
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate
      (coqDynamicTruthSharedSuccessorRows_append_production
        rootMode (ttParameter boundName)) hrow).
Qed.

(** Accept any syntactic row prefix whose translated context code agrees
    with the reversed concrete prefix.  This is the interface needed by the
    named append resources used by the native predecessor compiler. *)
Corollary
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_shared_successor_global_of_append_code_equivalent_row_prefix :
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
        (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
        (ttVar 2) (ttVar 1) (ttVar 0))) ->
  RawCodedPALocalProofOf M
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (rawTemplateFormula translation
      (coqFourStateTableAppendExistsTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
        (ttVar 2) (ttVar 1) (ttVar 0))) appendRoot ->
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
      (coqFourStateTableAppendPermutedTemplateGlobalSource rootMode
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate)).
Proof.
  intros M hPA translation hagreement rootMode boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep witnesses appendRoot rowPrefix
    hrootMode hprefix happend hrow.
  apply
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_shared_successor_global_of_append_row
      M hPA translation hagreement rootMode boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep witnesses appendRoot
      hrootMode happend).
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
        (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
        (ttVar 2) (ttVar 1) (ttVar 0))
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

(** Compose the reversed append closure with the same inherited and fixed-row
    resources used by the ordinary native client.  Only the translated
    prefix equality and append root mention the reversed tuple. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_shared_successor_global_of_append_and_inherited_row_roots :
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
        (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
        (ttVar 2) (ttVar 1) (ttVar 0))) ->
  RawCodedPALocalProofOf M
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (rawTemplateFormula translation
      (coqFourStateTableAppendExistsTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
        (ttVar 2) (ttVar 1) (ttVar 0))) appendRoot ->
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
      (coqFourStateTableAppendPermutedTemplateGlobalSource rootMode
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
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_permuted_shared_successor_global_of_append_code_equivalent_row_prefix
      M hPA translation hagreement rootMode boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep witnesses appendRoot
      namedRowPrefix hrootMode hprefix happend).
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

End
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.
