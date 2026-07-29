(**
  Eliminate the eight synchronized table-extension witnesses.

  The four-table append compiler concludes with eight nested existential
  binders, one code/step pair for each traversal column.  This module applies
  the generic finite existential-elimination compiler to that exact template
  and exposes the literal deepest eigenvariable context expected from a
  proof-producing row constructor.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedPALocalProofExistential
  RawCodedProofAssumptionLeaf
  RawCodedPALocalProofConjunction
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTotality
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedFourStateTableAppendSource
  RawCodedFourStateTableAppendProofCompilation
  RawCodedPALocalProofExistentialEliminationChain.

Module PABoundedRawCodedFourStateTableAppendExistentialElimination.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTotality.
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

Definition coqFourStateTableAppendExtensionBodyTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  match templateExistentialBodyMany 8
    (coqFourStateTableAppendExistsTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep) with
  | Some body => body
  | None => tfBot
  end.

(** Unconditional lookup projections carried by the strengthened append
    source.  Their order is mode, formula, assignment-code, assignment-step. *)
Definition coqFourStateTableAppendModeLookupTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  templateAndFirst (templateAndSecond (templateAnd4First
    (coqFourStateTableAppendExtensionBodyTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep))).

Definition coqFourStateTableAppendFormulaLookupTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  templateAndFirst (templateAndSecond (templateAnd4Second
    (coqFourStateTableAppendExtensionBodyTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep))).

Definition coqFourStateTableAppendAssignmentCodeLookupTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  templateAndFirst (templateAndSecond (templateAnd4Third
    (coqFourStateTableAppendExtensionBodyTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep))).

Definition coqFourStateTableAppendAssignmentStepLookupTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  templateAndFirst (templateAndSecond (templateAnd4Fourth
    (coqFourStateTableAppendExtensionBodyTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep))).

Definition coqFourStateTableAppendRootBoundTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  templateAndSecond (templateAndSecond (templateAnd4First
    (coqFourStateTableAppendExtensionBodyTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep))).

(** Defined-through projections of the four freshly extended tables.  Each is
    the first field of the append-prefix half of its component. *)
Definition coqFourStateTableAppendModeDefinedTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  templateAndFirst (templateAndFirst (templateAnd4First
    (coqFourStateTableAppendExtensionBodyTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep))).

Definition coqFourStateTableAppendFormulaDefinedTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  templateAndFirst (templateAndFirst (templateAnd4Second
    (coqFourStateTableAppendExtensionBodyTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep))).

Definition coqFourStateTableAppendAssignmentCodeDefinedTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  templateAndFirst (templateAndFirst (templateAnd4Third
    (coqFourStateTableAppendExtensionBodyTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep))).

Definition coqFourStateTableAppendAssignmentStepDefinedTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  templateAndFirst (templateAndFirst (templateAnd4Fourth
    (coqFourStateTableAppendExtensionBodyTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep))).

Definition coqFourStateTableAppendNewStateDefinedTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  tfAnd
    (coqFourStateTableAppendModeDefinedTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    (tfAnd
      (coqFourStateTableAppendFormulaDefinedTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep)
      (tfAnd
        (coqFourStateTableAppendAssignmentCodeDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)
        (coqFourStateTableAppendAssignmentStepDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))).

Definition coqFourStateTableAppendNewStateLookupTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  tfAnd
    (coqFourStateTableAppendModeLookupTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    (tfAnd
      (coqFourStateTableAppendFormulaLookupTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep)
      (tfAnd
        (coqFourStateTableAppendAssignmentCodeLookupTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)
        (coqFourStateTableAppendAssignmentStepLookupTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))).

Definition coqFourStateTableAppendWitnessTail
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    (context : TemplateContext) : TemplateContext :=
  tl (coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep context).

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

(** The innermost append body is the head assumption of the computed deepest
    context.  This equality audits the eigenvariable order, not merely the
    number of binders. *)
Lemma coqFourStateTableAppendWitnessContext_shape : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep context,
  coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep context =
  coqFourStateTableAppendExtensionBodyTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep ::
  coqFourStateTableAppendWitnessTail
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep context.
Proof.
  intros.
  unfold coqFourStateTableAppendWitnessTail,
    coqFourStateTableAppendWitnessContext,
    coqFourStateTableAppendExtensionBodyTemplate,
    coqFourStateTableAppendExistsTemplate,
    coqFourStateTableAppendInstanceTemplate,
    codedFourStateTableAppendFormula,
    fourStateTableAppendRepeatedAll,
    fixedLevelEx8.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst
    templateExistentialEliminationContext
    templateExistentialBodyMany tl].
  reflexivity.
Qed.

(** The innermost body retains the literal four-way conjunction of append
    prefixes after all universal openings and existential binders are
    removed. *)
Lemma coqFourStateTableAppendExtensionBodyTemplate_components : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  let extension := coqFourStateTableAppendExtensionBodyTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep in
  extension = tfAnd (templateAnd4First extension)
    (tfAnd (templateAnd4Second extension)
      (tfAnd (templateAnd4Third extension)
        (templateAnd4Fourth extension))).
Proof.
  intros.
  cbn zeta.
  unfold coqFourStateTableAppendExtensionBodyTemplate,
    coqFourStateTableAppendExistsTemplate,
    coqFourStateTableAppendInstanceTemplate,
    codedFourStateTableAppendFormula,
    fourStateTableAppendRepeatedAll,
    fourStateTableAppendExtensionBody,
    fixedLevelEx8, fixedLevelAnd4,
    templateAnd4First, templateAnd4Second,
    templateAnd4Third, templateAnd4Fourth.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst
    templateExistentialBodyMany].
  reflexivity.
Qed.

(** Every four-way component is itself the pair
    [append-prefix /\ appended-entry-lookup]. *)
Lemma coqFourStateTableAppendExtensionComponent_shapes : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  let extension := coqFourStateTableAppendExtensionBodyTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep in
  templateAnd4First extension =
      tfAnd (templateAndFirst (templateAnd4First extension))
        (templateAndSecond (templateAnd4First extension)) /\
  templateAnd4Second extension =
      tfAnd (templateAndFirst (templateAnd4Second extension))
        (templateAndSecond (templateAnd4Second extension)) /\
  templateAnd4Third extension =
      tfAnd (templateAndFirst (templateAnd4Third extension))
        (templateAndSecond (templateAnd4Third extension)) /\
  templateAnd4Fourth extension =
      tfAnd (templateAndFirst (templateAnd4Fourth extension))
        (templateAndSecond (templateAnd4Fourth extension)).
Proof.
  intros.
  cbn zeta.
  unfold coqFourStateTableAppendExtensionBodyTemplate,
    coqFourStateTableAppendExistsTemplate,
    coqFourStateTableAppendInstanceTemplate,
    codedFourStateTableAppendFormula,
    fourStateTableAppendRepeatedAll,
    fourStateTableAppendExtensionBody,
    codedAssignmentAppendAtTermAt,
    fixedLevelEx8, fixedLevelAnd4,
    templateAndFirst, templateAndSecond,
    templateAnd4First, templateAnd4Second,
    templateAnd4Third, templateAnd4Fourth.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst
    templateExistentialBodyMany].
  repeat split; reflexivity.
Qed.

(** The second half of every component is literally
    [appended-entry-lookup /\ bound < S bound]. *)
Lemma coqFourStateTableAppendExtensionLookupBound_shapes : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  let extension := coqFourStateTableAppendExtensionBodyTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep in
  templateAndSecond (templateAnd4First extension) =
      tfAnd
        (templateAndFirst (templateAndSecond (templateAnd4First extension)))
        (templateAndSecond (templateAndSecond (templateAnd4First extension))) /\
  templateAndSecond (templateAnd4Second extension) =
      tfAnd
        (templateAndFirst (templateAndSecond (templateAnd4Second extension)))
        (templateAndSecond (templateAndSecond (templateAnd4Second extension))) /\
  templateAndSecond (templateAnd4Third extension) =
      tfAnd
        (templateAndFirst (templateAndSecond (templateAnd4Third extension)))
        (templateAndSecond (templateAndSecond (templateAnd4Third extension))) /\
  templateAndSecond (templateAnd4Fourth extension) =
      tfAnd
        (templateAndFirst (templateAndSecond (templateAnd4Fourth extension)))
        (templateAndSecond (templateAndSecond (templateAnd4Fourth extension))).
Proof.
  intros.
  cbn zeta.
  unfold coqFourStateTableAppendExtensionBodyTemplate,
    coqFourStateTableAppendExistsTemplate,
    coqFourStateTableAppendInstanceTemplate,
    codedFourStateTableAppendFormula,
    fourStateTableAppendRepeatedAll,
    fourStateTableAppendExtensionBody,
    codedAssignmentAppendAtTermAt,
    fixedLevelEx8, fixedLevelAnd4,
    templateAndFirst, templateAndSecond,
    templateAnd4First, templateAnd4Second,
    templateAnd4Third, templateAnd4Fourth.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst
    templateExistentialBodyMany].
  repeat split; reflexivity.
Qed.

(** The append-prefix half begins with the target table's exact
    defined-through-successor field. *)
Lemma coqFourStateTableAppendExtensionDefined_shapes : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  let extension := coqFourStateTableAppendExtensionBodyTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep in
  templateAndFirst (templateAnd4First extension) =
      tfAnd
        (coqFourStateTableAppendModeDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)
        (templateAndSecond (templateAndFirst
          (templateAnd4First extension))) /\
  templateAndFirst (templateAnd4Second extension) =
      tfAnd
        (coqFourStateTableAppendFormulaDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)
        (templateAndSecond (templateAndFirst
          (templateAnd4Second extension))) /\
  templateAndFirst (templateAnd4Third extension) =
      tfAnd
        (coqFourStateTableAppendAssignmentCodeDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)
        (templateAndSecond (templateAndFirst
          (templateAnd4Third extension))) /\
  templateAndFirst (templateAnd4Fourth extension) =
      tfAnd
        (coqFourStateTableAppendAssignmentStepDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)
        (templateAndSecond (templateAndFirst
          (templateAnd4Fourth extension))).
Proof.
  intros.
  cbn zeta.
  unfold coqFourStateTableAppendModeDefinedTemplate,
    coqFourStateTableAppendFormulaDefinedTemplate,
    coqFourStateTableAppendAssignmentCodeDefinedTemplate,
    coqFourStateTableAppendAssignmentStepDefinedTemplate,
    coqFourStateTableAppendExtensionBodyTemplate,
    coqFourStateTableAppendExistsTemplate,
    coqFourStateTableAppendInstanceTemplate,
    codedFourStateTableAppendFormula,
    fourStateTableAppendRepeatedAll,
    fourStateTableAppendExtensionBody,
    codedAssignmentAppendAtTermAt,
    codedAssignmentAppendPrefixTermAt,
    fixedLevelEx8, fixedLevelAnd4,
    templateAndFirst, templateAndSecond,
    templateAnd4First, templateAnd4Second,
    templateAnd4Third, templateAnd4Fourth.
  cbn [templateUniversalOpenMany embedPAFormula
    templateFormulaOpen templateFormulaSubst
    templateExistentialBodyMany].
  repeat split; reflexivity.
Qed.

(** The extension body itself is immediately available as an assumption in
    the deepest context.  Later code can project its four append-prefix
    components without reconstructing the nested context layout. *)
Theorem raw_codedPALocalProofOf_four_state_table_append_extension_assumption :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqFourStateTableAppendWitnessContext
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep context))
      (rawTemplateFormula translation
        (coqFourStateTableAppendExtensionBodyTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) root.
Proof.
  intros M hPA translation context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep.
  rewrite coqFourStateTableAppendWitnessContext_shape.
  cbn [rawTemplateContextCode].
  exists (rawProofAssumptionRoot M
    (rawListNode M
      (rawTemplateFormula translation
        (coqFourStateTableAppendExtensionBodyTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      (rawTemplateContextCode translation
        (coqFourStateTableAppendWitnessTail
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep context)))
    (rawTemplateFormula translation
      (coqFourStateTableAppendExtensionBodyTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep))).
  apply (raw_codedPALocalProofOf_assumption M hPA).
  exact (raw_templateContext_realizable M hPA translation
    (coqFourStateTableAppendWitnessTail
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep context)).
Qed.

(** Project all four append-prefix facts from the deepest assumption with
    represented conjunction-elimination nodes. *)
Theorem raw_codedPALocalProofOf_four_state_table_append_extension_components :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  let extension := coqFourStateTableAppendExtensionBodyTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep in
  let witnessContext := coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep context in
  exists modeRoot formulaRoot assignmentCodeRoot assignmentStepRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation (templateAnd4First extension))
      modeRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation (templateAnd4Second extension))
      formulaRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation (templateAnd4Third extension))
      assignmentCodeRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation (templateAnd4Fourth extension))
      assignmentStepRoot.
Proof.
  intros M hPA translation context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep.
  cbn zeta.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_extension_assumption
      M hPA translation context
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    as [extensionRoot hextension].
  exact (raw_codedPALocalProofOf_templateAnd4_components
    M hPA translation
    (rawTemplateContextCode translation
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep context))
    (coqFourStateTableAppendExtensionBodyTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    extensionRoot
    (coqFourStateTableAppendExtensionBodyTemplate_components
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    hextension).
Qed.

(** Discard the append-prefix halves and retain the four unconditional new
    row lookups. *)
Theorem raw_codedPALocalProofOf_four_state_table_append_lookup_components :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  let witnessContext := coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep context in
  exists modeRoot formulaRoot assignmentCodeRoot assignmentStepRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation
        (coqFourStateTableAppendModeLookupTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) modeRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation
        (coqFourStateTableAppendFormulaLookupTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) formulaRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation
        (coqFourStateTableAppendAssignmentCodeLookupTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) assignmentCodeRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation
        (coqFourStateTableAppendAssignmentStepLookupTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) assignmentStepRoot.
Proof.
  intros M hPA translation context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep.
  cbn zeta.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_extension_components
      M hPA translation context
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    as (modeAppendRoot & formulaAppendRoot &
        assignmentCodeAppendRoot & assignmentStepAppendRoot &
        hmodeAppend & hformulaAppend &
        hassignmentCodeAppend & hassignmentStepAppend).
  destruct (coqFourStateTableAppendExtensionComponent_shapes
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep)
    as [hmodeShape [hformulaShape
      [hassignmentCodeShape hassignmentStepShape]]].
  rewrite hmodeShape, rawTemplateFormula_and in hmodeAppend.
  rewrite hformulaShape, rawTemplateFormula_and in hformulaAppend.
  rewrite hassignmentCodeShape, rawTemplateFormula_and
    in hassignmentCodeAppend.
  rewrite hassignmentStepShape, rawTemplateFormula_and
    in hassignmentStepAppend.
  destruct (coqFourStateTableAppendExtensionLookupBound_shapes
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep)
    as [hmodeLookupBoundShape [hformulaLookupBoundShape
      [hassignmentCodeLookupBoundShape
       hassignmentStepLookupBoundShape]]].
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _
    modeAppendRoot hmodeAppend) as hmodeLookupBound.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _
    formulaAppendRoot hformulaAppend) as hformulaLookupBound.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _
    assignmentCodeAppendRoot hassignmentCodeAppend)
    as hassignmentCodeLookupBound.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _
    assignmentStepAppendRoot hassignmentStepAppend)
    as hassignmentStepLookupBound.
  rewrite hmodeLookupBoundShape, rawTemplateFormula_and
    in hmodeLookupBound.
  rewrite hformulaLookupBoundShape, rawTemplateFormula_and
    in hformulaLookupBound.
  rewrite hassignmentCodeLookupBoundShape, rawTemplateFormula_and
    in hassignmentCodeLookupBound.
  rewrite hassignmentStepLookupBoundShape, rawTemplateFormula_and
    in hassignmentStepLookupBound.
  lazymatch type of hmodeLookupBound with
  | RawCodedPALocalProofOf _ _ _ ?pairRoot =>
      pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _
        pairRoot hmodeLookupBound) as hmodeLookup
  end.
  lazymatch type of hformulaLookupBound with
  | RawCodedPALocalProofOf _ _ _ ?pairRoot =>
      pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _
        pairRoot hformulaLookupBound) as hformulaLookup
  end.
  lazymatch type of hassignmentCodeLookupBound with
  | RawCodedPALocalProofOf _ _ _ ?pairRoot =>
      pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _
        pairRoot hassignmentCodeLookupBound) as hassignmentCodeLookup
  end.
  lazymatch type of hassignmentStepLookupBound with
  | RawCodedPALocalProofOf _ _ _ ?pairRoot =>
      pose proof (raw_codedPALocalProofOf_andE1 M hPA _ _ _
        pairRoot hassignmentStepLookupBound) as hassignmentStepLookup
  end.
  lazymatch type of hmodeLookup with
  | RawCodedPALocalProofOf _ _ _ ?modeRoot =>
    lazymatch type of hformulaLookup with
    | RawCodedPALocalProofOf _ _ _ ?formulaRoot =>
      lazymatch type of hassignmentCodeLookup with
      | RawCodedPALocalProofOf _ _ _ ?assignmentCodeRoot =>
        lazymatch type of hassignmentStepLookup with
        | RawCodedPALocalProofOf _ _ _ ?assignmentStepRoot =>
            exists modeRoot, formulaRoot,
              assignmentCodeRoot, assignmentStepRoot;
            split; [exact hmodeLookup |];
            split; [exact hformulaLookup |];
            split; [exact hassignmentCodeLookup |
              exact hassignmentStepLookup]
        end
      end
    end
  end.
Qed.

(** Project the four defined-through-successor fields from the same extension
    assumption.  The generic [andE11] helper hides the two nested proof roots
    used for each component. *)
Theorem raw_codedPALocalProofOf_four_state_table_append_defined_components :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  let witnessContext := coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep context in
  exists modeRoot formulaRoot assignmentCodeRoot assignmentStepRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation
        (coqFourStateTableAppendModeDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) modeRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation
        (coqFourStateTableAppendFormulaDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) formulaRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation
        (coqFourStateTableAppendAssignmentCodeDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) assignmentCodeRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation
        (coqFourStateTableAppendAssignmentStepDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) assignmentStepRoot.
Proof.
  intros M hPA translation context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep.
  cbn zeta.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_extension_components
      M hPA translation context
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    as (modeAppendRoot & formulaAppendRoot &
        assignmentCodeAppendRoot & assignmentStepAppendRoot &
        hmodeAppend & hformulaAppend &
        hassignmentCodeAppend & hassignmentStepAppend).
  destruct (coqFourStateTableAppendExtensionComponent_shapes
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep)
    as [hmodeShape [hformulaShape
      [hassignmentCodeShape hassignmentStepShape]]].
  destruct (coqFourStateTableAppendExtensionDefined_shapes
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep)
    as [hmodeDefinedShape [hformulaDefinedShape
      [hassignmentCodeDefinedShape hassignmentStepDefinedShape]]].
  rewrite hmodeShape, hmodeDefinedShape, !rawTemplateFormula_and
    in hmodeAppend.
  rewrite hformulaShape, hformulaDefinedShape, !rawTemplateFormula_and
    in hformulaAppend.
  rewrite hassignmentCodeShape, hassignmentCodeDefinedShape,
    !rawTemplateFormula_and in hassignmentCodeAppend.
  rewrite hassignmentStepShape, hassignmentStepDefinedShape,
    !rawTemplateFormula_and in hassignmentStepAppend.
  destruct (raw_codedPALocalProofOf_andE11 M hPA _ _ _ _ _ hmodeAppend)
    as [modeRoot hmodeDefined].
  destruct (raw_codedPALocalProofOf_andE11 M hPA _ _ _ _ _ hformulaAppend)
    as [formulaRoot hformulaDefined].
  destruct (raw_codedPALocalProofOf_andE11 M hPA _ _ _ _ _
    hassignmentCodeAppend) as [assignmentCodeRoot hassignmentCodeDefined].
  destruct (raw_codedPALocalProofOf_andE11 M hPA _ _ _ _ _
    hassignmentStepAppend) as [assignmentStepRoot hassignmentStepDefined].
  exists modeRoot, formulaRoot, assignmentCodeRoot, assignmentStepRoot.
  split; [exact hmodeDefined |].
  split; [exact hformulaDefined |].
  split; [exact hassignmentCodeDefined | exact hassignmentStepDefined].
Qed.

(** Assemble the exact first four right-associated fields of the global
    traversal body. *)
Theorem raw_codedPALocalProofOf_four_state_table_append_new_state_defined :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqFourStateTableAppendWitnessContext
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep context))
      (rawTemplateFormula translation
        (coqFourStateTableAppendNewStateDefinedTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) root.
Proof.
  intros M hPA translation context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_defined_components
      M hPA translation context
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    as (modeRoot & formulaRoot & assignmentCodeRoot & assignmentStepRoot &
        hmode & hformula & hassignmentCode & hassignmentStep).
  apply (raw_codedPALocalProofOf_templateAnd4 M hPA translation
    (rawTemplateContextCode translation
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep context))
    (coqFourStateTableAppendNewStateDefinedTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    modeRoot formulaRoot assignmentCodeRoot assignmentStepRoot).
  - unfold coqFourStateTableAppendNewStateDefinedTemplate,
      templateAnd4First, templateAnd4Second,
      templateAnd4Third, templateAnd4Fourth.
    reflexivity.
  - exact hmode.
  - exact hformula.
  - exact hassignmentCode.
  - exact hassignmentStep.
Qed.

(** The same strengthened component directly supplies the global root-bound
    fact [bound < S bound]. *)
Theorem raw_codedPALocalProofOf_four_state_table_append_root_bound :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqFourStateTableAppendWitnessContext
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep context))
      (rawTemplateFormula translation
        (coqFourStateTableAppendRootBoundTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) root.
Proof.
  intros M hPA translation context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_extension_components
      M hPA translation context
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    as (modeAppendRoot & formulaAppendRoot &
        assignmentCodeAppendRoot & assignmentStepAppendRoot &
        hmodeAppend & _).
  destruct (coqFourStateTableAppendExtensionComponent_shapes
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep)
    as [hmodeShape _].
  destruct (coqFourStateTableAppendExtensionLookupBound_shapes
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep)
    as [hmodeLookupBoundShape _].
  rewrite hmodeShape, rawTemplateFormula_and in hmodeAppend.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _
    modeAppendRoot hmodeAppend) as hmodeLookupBound.
  rewrite hmodeLookupBoundShape, rawTemplateFormula_and
    in hmodeLookupBound.
  lazymatch type of hmodeLookupBound with
  | RawCodedPALocalProofOf _ _ _ ?pairRoot =>
      pose proof (raw_codedPALocalProofOf_andE2 M hPA _ _ _
        pairRoot hmodeLookupBound) as hbound
  end.
  lazymatch type of hbound with
  | RawCodedPALocalProofOf _ _ _ ?root => exists root; exact hbound
  end.
Qed.

(** Reassemble the four lookup facts into the exact state-row conjunction
    consumed by the global truth traversal. *)
Theorem raw_codedPALocalProofOf_four_state_table_append_new_state_lookup :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqFourStateTableAppendWitnessContext
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep context))
      (rawTemplateFormula translation
        (coqFourStateTableAppendNewStateLookupTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) root.
Proof.
  intros M hPA translation context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_lookup_components
      M hPA translation context
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    as (modeRoot & formulaRoot & assignmentCodeRoot & assignmentStepRoot &
        hmode & hformula & hassignmentCode & hassignmentStep).
  apply (raw_codedPALocalProofOf_templateAnd4 M hPA translation
    (rawTemplateContextCode translation
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep context))
    (coqFourStateTableAppendNewStateLookupTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    modeRoot formulaRoot assignmentCodeRoot assignmentStepRoot).
  - unfold coqFourStateTableAppendNewStateLookupTemplate,
      templateAnd4First, templateAnd4Second,
      templateAnd4Third, templateAnd4Fourth.
    reflexivity.
  - exact hmode.
  - exact hformula.
  - exact hassignmentCode.
  - exact hassignmentStep.
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
