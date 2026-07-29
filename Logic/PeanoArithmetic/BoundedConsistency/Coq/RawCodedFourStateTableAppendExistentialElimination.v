(**
  Eliminate the eight synchronized table-extension witnesses.

  The four-table append compiler concludes with eight nested existential
  binders, one code/step pair for each traversal column.  This module applies
  the generic finite existential-elimination compiler to that exact template
  and exposes the literal deepest eigenvariable context expected from a
  proof-producing row constructor.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedFixedLevelTruth
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedFourStateTableAppendSource
  RawCodedFourStateTableAppendProofCompilation
  RawCodedPALocalProofExistentialEliminationChain.

Module PABoundedRawCodedFourStateTableAppendExistentialElimination.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedFourStateTableAppendSource.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.

(** The fallback is unreachable and retained only to keep computation total. *)
Definition coqFourStateTableAppendWitnessContext
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    (context : TemplateContext) : TemplateContext :=
  match templateExistentialEliminationContext 8
    (coqFourStateTableAppendExistsTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    context with
  | Some witnessContext => witnessContext
  | None => context
  end.

(** Computational audit: the specialized append consequent has literally
    eight leading existential binders. *)
Lemma coqFourStateTableAppendWitnessContext_success : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep context,
  templateExistentialEliminationContext 8
    (coqFourStateTableAppendExistsTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    context =
  Some (coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep context).
Proof.
  intros.
  unfold coqFourStateTableAppendWitnessContext,
    coqFourStateTableAppendExistsTemplate,
    coqFourStateTableAppendInstanceTemplate,
    codedFourStateTableAppendFormula,
    fourStateTableAppendRepeatedAll,
    fixedLevelEx8.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst
    templateExistentialEliminationContext].
  reflexivity.
Qed.

(** Close a continuation constructed under all eight table witnesses.  Every
    context shift, target shift, assumption leaf, and [ExE] node is supplied
    by the generic chain compiler. *)
Theorem raw_codedPALocalProofOf_four_state_table_append_ex8_elimination :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context conclusion
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    appendRoot continuationRoot,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation
      (coqFourStateTableAppendExistsTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep)) appendRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep context))
    (rawTemplateFormula translation
      (templateFormulaShiftMany 8 conclusion)) continuationRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation conclusion) root.
Proof.
  intros M hPA translation context conclusion
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    appendRoot continuationRoot happend hcontinuation.
  exact (raw_codedPALocalProofOf_existential_elimination_chain
    M hPA translation 8
    (coqFourStateTableAppendExistsTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    context conclusion
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep context)
    appendRoot continuationRoot
    (coqFourStateTableAppendWitnessContext_success
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep context)
    happend hcontinuation).
Qed.

End PABoundedRawCodedFourStateTableAppendExistentialElimination.
