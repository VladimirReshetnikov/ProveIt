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
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedTemplateSyntax
  RawCodedTemplateRenamingSubstitution
  RawCodedTemplateProofCompiler
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTotality
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedPALocalProofUniversalIntroductionChain
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
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateRenamingSubstitution.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
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

(** Universally quantified preservation fields for entries strictly below the
    previous bound. *)
Definition coqFourStateTableAppendModePreservationTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  templateAndFirst (templateAndSecond (templateAndFirst (templateAnd4First
    (coqFourStateTableAppendExtensionBodyTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)))).

Definition coqFourStateTableAppendFormulaPreservationTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  templateAndFirst (templateAndSecond (templateAndFirst (templateAnd4Second
    (coqFourStateTableAppendExtensionBodyTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)))).

Definition coqFourStateTableAppendAssignmentCodePreservationTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  templateAndFirst (templateAndSecond (templateAndFirst (templateAnd4Third
    (coqFourStateTableAppendExtensionBodyTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)))).

Definition coqFourStateTableAppendAssignmentStepPreservationTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    : TemplateFormula :=
  templateAndFirst (templateAndSecond (templateAndFirst (templateAnd4Fourth
    (coqFourStateTableAppendExtensionBodyTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)))).

Definition coqFourStateTableAppendPreservationAtTemplate
    (preservation : TemplateFormula) (index value : TemplateTerm)
    : TemplateFormula :=
  templateUniversalOpenManyOrBot preservation [index; value].

Definition coqFourStateTableAppendPreservationCurrentBoundTemplate
    (preservation : TemplateFormula) (index value : TemplateTerm)
    : TemplateFormula :=
  templateImpAntecedent
    (coqFourStateTableAppendPreservationAtTemplate
      preservation index value).

Definition coqFourStateTableAppendPreservationOldBoundTemplate
    (preservation : TemplateFormula) (index value : TemplateTerm)
    : TemplateFormula :=
  templateImpAntecedent (templateImpConsequent
    (coqFourStateTableAppendPreservationAtTemplate
      preservation index value)).

Definition coqFourStateTableAppendPreservationOldLookupTemplate
    (preservation : TemplateFormula) (index value : TemplateTerm)
    : TemplateFormula :=
  templateImpAntecedent (templateImpConsequent (templateImpConsequent
    (coqFourStateTableAppendPreservationAtTemplate
      preservation index value))).

Definition coqFourStateTableAppendPreservationNewLookupTemplate
    (preservation : TemplateFormula) (index value : TemplateTerm)
    : TemplateFormula :=
  templateImpConsequent (templateImpConsequent (templateImpConsequent
    (coqFourStateTableAppendPreservationAtTemplate
      preservation index value))).

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

(** Iterated context shift preserves a literal cons and applies the matching
    iterated formula shift to its head.  This is the scope-order identity used
    when row eigenvariables are introduced *inside* append witnesses. *)
Lemma templateContextShiftMany_cons : forall count head tail,
  templateContextShiftMany count (head :: tail) =
  templateFormulaShiftMany count head ::
    templateContextShiftMany count tail.
Proof.
  induction count as [|smaller ih]; intros head tail.
  - reflexivity.
  - cbn [templateContextShiftMany templateFormulaShiftMany
      templateContextShift templateContextRename].
    apply ih.
Qed.

(** The append extension body remains the head assumption after any number
    of later eigenvariables have shifted the whole witness context. *)
Lemma coqFourStateTableAppendWitnessContext_shift_many_shape : forall
    count
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep context,
  templateContextShiftMany count
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep context) =
  templateFormulaShiftMany count
    (coqFourStateTableAppendExtensionBodyTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep) ::
  templateContextShiftMany count
    (coqFourStateTableAppendWitnessTail
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep context).
Proof.
  intros.
  rewrite coqFourStateTableAppendWitnessContext_shape.
  apply templateContextShiftMany_cons.
Qed.

(** Proof-producing form of the preceding scope identity.  It reconstructs
    only an assumption leaf, so no general proof-code renaming principle is
    hidden here. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_extension_assumption_shift_many :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    count context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (templateContextShiftMany count
          (coqFourStateTableAppendWitnessContext
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            bound mode formula assignmentCode assignmentStep context)))
      (rawTemplateFormula translation
        (templateFormulaShiftMany count
          (coqFourStateTableAppendExtensionBodyTemplate
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            bound mode formula assignmentCode assignmentStep))) root.
Proof.
  intros M hPA translation count context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep.
  rewrite coqFourStateTableAppendWitnessContext_shift_many_shape.
  cbn [rawTemplateContextCode].
  eexists.
  apply (raw_codedPALocalProofOf_assumption M hPA).
  exact (raw_templateContext_realizable M hPA translation
    (templateContextShiftMany count
      (coqFourStateTableAppendWitnessTail
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep context))).
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

(** The tail of each append prefix starts with the two-variable preservation
    law and ends with the guarded new-entry lookup. *)
Lemma coqFourStateTableAppendExtensionPreservation_shapes : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep,
  let extension := coqFourStateTableAppendExtensionBodyTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep in
  templateAndSecond (templateAndFirst (templateAnd4First extension)) =
      tfAnd
        (coqFourStateTableAppendModePreservationTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)
        (templateAndSecond (templateAndSecond (templateAndFirst
          (templateAnd4First extension)))) /\
  templateAndSecond (templateAndFirst (templateAnd4Second extension)) =
      tfAnd
        (coqFourStateTableAppendFormulaPreservationTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)
        (templateAndSecond (templateAndSecond (templateAndFirst
          (templateAnd4Second extension)))) /\
  templateAndSecond (templateAndFirst (templateAnd4Third extension)) =
      tfAnd
        (coqFourStateTableAppendAssignmentCodePreservationTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)
        (templateAndSecond (templateAndSecond (templateAndFirst
          (templateAnd4Third extension)))) /\
  templateAndSecond (templateAndFirst (templateAnd4Fourth extension)) =
      tfAnd
        (coqFourStateTableAppendAssignmentStepPreservationTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)
        (templateAndSecond (templateAndSecond (templateAndFirst
          (templateAnd4Fourth extension)))).
Proof.
  intros.
  cbn zeta.
  unfold coqFourStateTableAppendModePreservationTemplate,
    coqFourStateTableAppendFormulaPreservationTemplate,
    coqFourStateTableAppendAssignmentCodePreservationTemplate,
    coqFourStateTableAppendAssignmentStepPreservationTemplate,
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

(** All four preservation fields have exactly two leading universal binders;
    instantiate them at one candidate predecessor state. *)
Lemma coqFourStateTableAppendPreservationAt_successes : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep,
  templateUniversalOpenMany
    (coqFourStateTableAppendModePreservationTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    [index; rowMode] =
    Some (coqFourStateTableAppendPreservationAtTemplate
      (coqFourStateTableAppendModePreservationTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep)
      index rowMode) /\
  templateUniversalOpenMany
    (coqFourStateTableAppendFormulaPreservationTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    [index; rowFormula] =
    Some (coqFourStateTableAppendPreservationAtTemplate
      (coqFourStateTableAppendFormulaPreservationTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep)
      index rowFormula) /\
  templateUniversalOpenMany
    (coqFourStateTableAppendAssignmentCodePreservationTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    [index; rowAssignmentCode] =
    Some (coqFourStateTableAppendPreservationAtTemplate
      (coqFourStateTableAppendAssignmentCodePreservationTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep)
      index rowAssignmentCode) /\
  templateUniversalOpenMany
    (coqFourStateTableAppendAssignmentStepPreservationTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    [index; rowAssignmentStep] =
    Some (coqFourStateTableAppendPreservationAtTemplate
      (coqFourStateTableAppendAssignmentStepPreservationTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep)
      index rowAssignmentStep).
Proof.
  intros.
  unfold coqFourStateTableAppendPreservationAtTemplate,
    templateUniversalOpenManyOrBot,
    coqFourStateTableAppendModePreservationTemplate,
    coqFourStateTableAppendFormulaPreservationTemplate,
    coqFourStateTableAppendAssignmentCodePreservationTemplate,
    coqFourStateTableAppendAssignmentStepPreservationTemplate,
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

Lemma coqFourStateTableAppendPreservationAt_shapes : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep,
  let modeAt := coqFourStateTableAppendPreservationAtTemplate
    (coqFourStateTableAppendModePreservationTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    index rowMode in
  let formulaAt := coqFourStateTableAppendPreservationAtTemplate
    (coqFourStateTableAppendFormulaPreservationTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    index rowFormula in
  let assignmentCodeAt := coqFourStateTableAppendPreservationAtTemplate
    (coqFourStateTableAppendAssignmentCodePreservationTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    index rowAssignmentCode in
  let assignmentStepAt := coqFourStateTableAppendPreservationAtTemplate
    (coqFourStateTableAppendAssignmentStepPreservationTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    index rowAssignmentStep in
  TemplateImp3Shape modeAt /\
  TemplateImp3Shape formulaAt /\
  TemplateImp3Shape assignmentCodeAt /\
  TemplateImp3Shape assignmentStepAt.
Proof.
  intros.
  cbn zeta.
  unfold TemplateImp3Shape,
    templateImpAntecedent, templateImpConsequent,
    coqFourStateTableAppendPreservationAtTemplate,
    templateUniversalOpenManyOrBot,
    coqFourStateTableAppendModePreservationTemplate,
    coqFourStateTableAppendFormulaPreservationTemplate,
    coqFourStateTableAppendAssignmentCodePreservationTemplate,
    coqFourStateTableAppendAssignmentStepPreservationTemplate,
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

(** Structural views used when four triple implications share their first
    two premises.  The third premises and conclusions are assembled in the
    same right-associated four-column shape used by traversal state rows. *)
Definition templateImp3SecondPremise (source : TemplateFormula)
    : TemplateFormula :=
  templateImpAntecedent (templateImpConsequent source).

Definition templateImp3ThirdPremise (source : TemplateFormula)
    : TemplateFormula :=
  templateImpAntecedent
    (templateImpConsequent (templateImpConsequent source)).

Definition templateImp3Conclusion (source : TemplateFormula)
    : TemplateFormula :=
  templateImpConsequent
    (templateImpConsequent (templateImpConsequent source)).

Definition templateFormulaMapAnd4
    (projection : TemplateFormula -> TemplateFormula)
    (first second third fourth : TemplateFormula) : TemplateFormula :=
  tfAnd (projection first)
    (tfAnd (projection second)
      (tfAnd (projection third) (projection fourth))).

Lemma templateFormulaMapAnd4_shape : forall projection first second third fourth,
  let source := templateFormulaMapAnd4 projection
    first second third fourth in
  source = tfAnd (templateAnd4First source)
    (tfAnd (templateAnd4Second source)
      (tfAnd (templateAnd4Third source) (templateAnd4Fourth source))).
Proof.
  intros. cbn zeta.
  unfold templateFormulaMapAnd4,
    templateAnd4First, templateAnd4Second,
    templateAnd4Third, templateAnd4Fourth.
  reflexivity.
Qed.

(** Apply four represented three-premise implications with one shared proof
    of each of the first two premises.  The theorem is independent of table
    coding; the append specialization below supplies only structural
    equalities between its four arithmetic premise templates. *)
Theorem raw_codedPALocalProofOf_templateImpE3_shared_first_second_and4 :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context firstSource secondSource thirdSource fourthSource
    firstImpRoot secondImpRoot thirdImpRoot fourthImpRoot
    firstRoot secondRoot thirdPremisesRoot,
  TemplateImp3Shape firstSource ->
  TemplateImp3Shape secondSource ->
  TemplateImp3Shape thirdSource ->
  TemplateImp3Shape fourthSource ->
  templateImpAntecedent secondSource =
    templateImpAntecedent firstSource ->
  templateImpAntecedent thirdSource =
    templateImpAntecedent firstSource ->
  templateImpAntecedent fourthSource =
    templateImpAntecedent firstSource ->
  templateImp3SecondPremise secondSource =
    templateImp3SecondPremise firstSource ->
  templateImp3SecondPremise thirdSource =
    templateImp3SecondPremise firstSource ->
  templateImp3SecondPremise fourthSource =
    templateImp3SecondPremise firstSource ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation firstSource) firstImpRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation secondSource) secondImpRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation thirdSource) thirdImpRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation fourthSource) fourthImpRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateImpAntecedent firstSource)) firstRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateImp3SecondPremise firstSource)) secondRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateFormulaMapAnd4 templateImp3ThirdPremise
        firstSource secondSource thirdSource fourthSource))
    thirdPremisesRoot ->
  exists root,
    RawCodedPALocalProofOf M context
      (rawTemplateFormula translation
        (templateFormulaMapAnd4 templateImp3Conclusion
          firstSource secondSource thirdSource fourthSource)) root.
Proof.
  intros M hPA translation context
    firstSource secondSource thirdSource fourthSource
    firstImpRoot secondImpRoot thirdImpRoot fourthImpRoot
    firstRoot secondRoot thirdPremisesRoot
    hfirstShape hsecondShape hthirdShape hfourthShape
    hsecondFirst hthirdFirst hfourthFirst
    hsecondSecond hthirdSecond hfourthSecond
    hfirstImp hsecondImp hthirdImp hfourthImp
    hfirst hsecond hthirdPremises.
  destruct (raw_codedPALocalProofOf_templateAnd4_components
    M hPA translation context
    (templateFormulaMapAnd4 templateImp3ThirdPremise
      firstSource secondSource thirdSource fourthSource)
    thirdPremisesRoot
    (templateFormulaMapAnd4_shape templateImp3ThirdPremise
      firstSource secondSource thirdSource fourthSource)
    hthirdPremises)
    as (firstThirdRoot & secondThirdRoot & thirdThirdRoot & fourthThirdRoot &
        hfirstThird & hsecondThird & hthirdThird & hfourthThird).
  assert (hfirstForSecond : RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateImpAntecedent secondSource)) firstRoot).
  { rewrite hsecondFirst. exact hfirst. }
  assert (hfirstForThird : RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateImpAntecedent thirdSource)) firstRoot).
  { rewrite hthirdFirst. exact hfirst. }
  assert (hfirstForFourth : RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateImpAntecedent fourthSource)) firstRoot).
  { rewrite hfourthFirst. exact hfirst. }
  assert (hsecondForSecond : RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateImp3SecondPremise secondSource)) secondRoot).
  { rewrite hsecondSecond. exact hsecond. }
  assert (hsecondForThird : RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateImp3SecondPremise thirdSource)) secondRoot).
  { rewrite hthirdSecond. exact hsecond. }
  assert (hsecondForFourth : RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateImp3SecondPremise fourthSource)) secondRoot).
  { rewrite hfourthSecond. exact hsecond. }
  destruct (raw_codedPALocalProofOf_templateImpE3 M hPA translation context
    firstSource firstImpRoot firstRoot secondRoot firstThirdRoot
    hfirstShape hfirstImp hfirst hsecond hfirstThird)
    as [firstConclusionRoot hfirstConclusion].
  destruct (raw_codedPALocalProofOf_templateImpE3 M hPA translation context
    secondSource secondImpRoot firstRoot secondRoot secondThirdRoot
    hsecondShape hsecondImp hfirstForSecond hsecondForSecond hsecondThird)
    as [secondConclusionRoot hsecondConclusion].
  destruct (raw_codedPALocalProofOf_templateImpE3 M hPA translation context
    thirdSource thirdImpRoot firstRoot secondRoot thirdThirdRoot
    hthirdShape hthirdImp hfirstForThird hsecondForThird hthirdThird)
    as [thirdConclusionRoot hthirdConclusion].
  destruct (raw_codedPALocalProofOf_templateImpE3 M hPA translation context
    fourthSource fourthImpRoot firstRoot secondRoot fourthThirdRoot
    hfourthShape hfourthImp hfirstForFourth hsecondForFourth hfourthThird)
    as [fourthConclusionRoot hfourthConclusion].
  exact (raw_codedPALocalProofOf_templateAnd4 M hPA translation context
    (templateFormulaMapAnd4 templateImp3Conclusion
      firstSource secondSource thirdSource fourthSource)
    firstConclusionRoot secondConclusionRoot
    thirdConclusionRoot fourthConclusionRoot
    (templateFormulaMapAnd4_shape templateImp3Conclusion
      firstSource secondSource thirdSource fourthSource)
    hfirstConclusion hsecondConclusion hthirdConclusion hfourthConclusion).
Qed.

(** Named instances of the four preservation laws at one candidate row. *)
Definition coqFourStateTableAppendModePreservationAtTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowMode : TemplateTerm) : TemplateFormula :=
  coqFourStateTableAppendPreservationAtTemplate
    (coqFourStateTableAppendModePreservationTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    index rowMode.

Definition coqFourStateTableAppendFormulaPreservationAtTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowFormula : TemplateTerm) : TemplateFormula :=
  coqFourStateTableAppendPreservationAtTemplate
    (coqFourStateTableAppendFormulaPreservationTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    index rowFormula.

Definition coqFourStateTableAppendAssignmentCodePreservationAtTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowAssignmentCode : TemplateTerm) : TemplateFormula :=
  coqFourStateTableAppendPreservationAtTemplate
    (coqFourStateTableAppendAssignmentCodePreservationTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    index rowAssignmentCode.

Definition coqFourStateTableAppendAssignmentStepPreservationAtTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowAssignmentStep : TemplateTerm) : TemplateFormula :=
  coqFourStateTableAppendPreservationAtTemplate
    (coqFourStateTableAppendAssignmentStepPreservationTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    index rowAssignmentStep.

(** The shared arithmetic guards and the old/new four-column lookup rows. *)
Definition coqFourStateTableAppendPredecessorCurrentBoundTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowMode : TemplateTerm) : TemplateFormula :=
  templateImpAntecedent
    (coqFourStateTableAppendModePreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep index rowMode).

Definition coqFourStateTableAppendPredecessorOldBoundTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowMode : TemplateTerm) : TemplateFormula :=
  templateImp3SecondPremise
    (coqFourStateTableAppendModePreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep index rowMode).

Definition coqFourStateTableAppendPredecessorOldStateLookupTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowMode rowFormula rowAssignmentCode rowAssignmentStep
      : TemplateTerm) : TemplateFormula :=
  templateFormulaMapAnd4 templateImp3ThirdPremise
    (coqFourStateTableAppendModePreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep index rowMode)
    (coqFourStateTableAppendFormulaPreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep index rowFormula)
    (coqFourStateTableAppendAssignmentCodePreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowAssignmentCode)
    (coqFourStateTableAppendAssignmentStepPreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowAssignmentStep).

Definition coqFourStateTableAppendPredecessorNewStateLookupTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowMode rowFormula rowAssignmentCode rowAssignmentStep
      : TemplateTerm) : TemplateFormula :=
  templateFormulaMapAnd4 templateImp3Conclusion
    (coqFourStateTableAppendModePreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep index rowMode)
    (coqFourStateTableAppendFormulaPreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep index rowFormula)
    (coqFourStateTableAppendAssignmentCodePreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowAssignmentCode)
    (coqFourStateTableAppendAssignmentStepPreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowAssignmentStep).

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

(** Project the four universally quantified predecessor-preservation laws. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_preservation_components :
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
        (coqFourStateTableAppendModePreservationTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) modeRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation
        (coqFourStateTableAppendFormulaPreservationTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) formulaRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation
        (coqFourStateTableAppendAssignmentCodePreservationTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep)) assignmentCodeRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation
        (coqFourStateTableAppendAssignmentStepPreservationTemplate
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
  destruct (coqFourStateTableAppendExtensionPreservation_shapes
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep)
    as [hmodePreservationShape [hformulaPreservationShape
      [hassignmentCodePreservationShape
       hassignmentStepPreservationShape]]].
  rewrite hmodeShape, hmodeDefinedShape, hmodePreservationShape,
    !rawTemplateFormula_and in hmodeAppend.
  rewrite hformulaShape, hformulaDefinedShape, hformulaPreservationShape,
    !rawTemplateFormula_and in hformulaAppend.
  rewrite hassignmentCodeShape, hassignmentCodeDefinedShape,
    hassignmentCodePreservationShape,
    !rawTemplateFormula_and in hassignmentCodeAppend.
  rewrite hassignmentStepShape, hassignmentStepDefinedShape,
    hassignmentStepPreservationShape,
    !rawTemplateFormula_and in hassignmentStepAppend.
  destruct (raw_codedPALocalProofOf_andE121 M hPA _ _ _ _ _ _ hmodeAppend)
    as [modeRoot hmodePreservation].
  destruct (raw_codedPALocalProofOf_andE121 M hPA _ _ _ _ _ _
    hformulaAppend) as [formulaRoot hformulaPreservation].
  destruct (raw_codedPALocalProofOf_andE121 M hPA _ _ _ _ _ _
    hassignmentCodeAppend)
    as [assignmentCodeRoot hassignmentCodePreservation].
  destruct (raw_codedPALocalProofOf_andE121 M hPA _ _ _ _ _ _
    hassignmentStepAppend)
    as [assignmentStepRoot hassignmentStepPreservation].
  exists modeRoot, formulaRoot, assignmentCodeRoot, assignmentStepRoot.
  split; [exact hmodePreservation |].
  split; [exact hformulaPreservation |].
  split; [exact hassignmentCodePreservation |
    exact hassignmentStepPreservation].
Qed.

(** Instantiate the four preservation laws at one predecessor row while
    retaining the shared witness context. *)
Theorem raw_codedPALocalProofOf_four_state_table_append_preservation_at :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep,
  let witnessContext := coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep context in
  exists modeRoot formulaRoot assignmentCodeRoot assignmentStepRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation
        (coqFourStateTableAppendPreservationAtTemplate
          (coqFourStateTableAppendModePreservationTemplate
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            bound mode formula assignmentCode assignmentStep)
          index rowMode)) modeRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation
        (coqFourStateTableAppendPreservationAtTemplate
          (coqFourStateTableAppendFormulaPreservationTemplate
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            bound mode formula assignmentCode assignmentStep)
          index rowFormula)) formulaRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation
        (coqFourStateTableAppendPreservationAtTemplate
          (coqFourStateTableAppendAssignmentCodePreservationTemplate
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            bound mode formula assignmentCode assignmentStep)
          index rowAssignmentCode)) assignmentCodeRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation
        (coqFourStateTableAppendPreservationAtTemplate
          (coqFourStateTableAppendAssignmentStepPreservationTemplate
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            bound mode formula assignmentCode assignmentStep)
          index rowAssignmentStep)) assignmentStepRoot.
Proof.
  intros M hPA translation context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep.
  cbn zeta.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_preservation_components
      M hPA translation context
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    as (modeRoot & formulaRoot & assignmentCodeRoot & assignmentStepRoot &
        hmode & hformula & hassignmentCode & hassignmentStep).
  destruct (coqFourStateTableAppendPreservationAt_successes
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep)
    as [hmodeOpen [hformulaOpen
      [hassignmentCodeOpen hassignmentStepOpen]]].
  destruct (raw_codedPALocalProofOf_templateUniversalOpenMany
    M hPA translation _ _ [index; rowMode] _ modeRoot hmodeOpen hmode)
    as [modeAtRoot hmodeAt].
  destruct (raw_codedPALocalProofOf_templateUniversalOpenMany
    M hPA translation _ _ [index; rowFormula] _ formulaRoot
    hformulaOpen hformula) as [formulaAtRoot hformulaAt].
  destruct (raw_codedPALocalProofOf_templateUniversalOpenMany
    M hPA translation _ _ [index; rowAssignmentCode] _ assignmentCodeRoot
    hassignmentCodeOpen hassignmentCode)
    as [assignmentCodeAtRoot hassignmentCodeAt].
  destruct (raw_codedPALocalProofOf_templateUniversalOpenMany
    M hPA translation _ _ [index; rowAssignmentStep] _ assignmentStepRoot
    hassignmentStepOpen hassignmentStep)
    as [assignmentStepAtRoot hassignmentStepAt].
  exists modeAtRoot, formulaAtRoot,
    assignmentCodeAtRoot, assignmentStepAtRoot.
  split; [exact hmodeAt |].
  split; [exact hformulaAt |].
  split; [exact hassignmentCodeAt | exact hassignmentStepAt].
Qed.

(** Compile the predecessor branch of the successor traversal row.  The six
    equalities are deliberately structural: a concrete client proves them
    for its fixed de Bruijn row variables, while this theorem remains valid
    for arbitrary template terms and translations. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_predecessor_state_lookup :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep
    currentBoundRoot oldBoundRoot oldStateLookupRoot,
  let witnessContext := coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep context in
  let modeAt := coqFourStateTableAppendModePreservationAtTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep index rowMode in
  let formulaAt := coqFourStateTableAppendFormulaPreservationAtTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep index rowFormula in
  let assignmentCodeAt :=
    coqFourStateTableAppendAssignmentCodePreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowAssignmentCode in
  let assignmentStepAt :=
    coqFourStateTableAppendAssignmentStepPreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowAssignmentStep in
  templateImpAntecedent formulaAt = templateImpAntecedent modeAt ->
  templateImpAntecedent assignmentCodeAt = templateImpAntecedent modeAt ->
  templateImpAntecedent assignmentStepAt = templateImpAntecedent modeAt ->
  templateImp3SecondPremise formulaAt =
    templateImp3SecondPremise modeAt ->
  templateImp3SecondPremise assignmentCodeAt =
    templateImp3SecondPremise modeAt ->
  templateImp3SecondPremise assignmentStepAt =
    templateImp3SecondPremise modeAt ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation witnessContext)
    (rawTemplateFormula translation
      (coqFourStateTableAppendPredecessorCurrentBoundTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep index rowMode))
    currentBoundRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation witnessContext)
    (rawTemplateFormula translation
      (coqFourStateTableAppendPredecessorOldBoundTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep index rowMode))
    oldBoundRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation witnessContext)
    (rawTemplateFormula translation
      (coqFourStateTableAppendPredecessorOldStateLookupTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep
        index rowMode rowFormula rowAssignmentCode rowAssignmentStep))
    oldStateLookupRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation witnessContext)
      (rawTemplateFormula translation
        (coqFourStateTableAppendPredecessorNewStateLookupTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep
          index rowMode rowFormula rowAssignmentCode rowAssignmentStep)) root.
Proof.
  intros M hPA translation context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep
    currentBoundRoot oldBoundRoot oldStateLookupRoot
    witnessContext modeAt formulaAt assignmentCodeAt assignmentStepAt
    hformulaFirst hassignmentCodeFirst hassignmentStepFirst
    hformulaSecond hassignmentCodeSecond hassignmentStepSecond
    hcurrentBound holdBound holdStateLookup.
  cbn zeta in *.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_preservation_at
      M hPA translation context
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowMode rowFormula rowAssignmentCode rowAssignmentStep)
    as (modeRoot & formulaRoot & assignmentCodeRoot & assignmentStepRoot &
        hmode & hformula & hassignmentCode & hassignmentStep).
  destruct (coqFourStateTableAppendPreservationAt_shapes
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    index rowMode rowFormula rowAssignmentCode rowAssignmentStep)
    as [hmodeShape [hformulaShape
      [hassignmentCodeShape hassignmentStepShape]]].
  apply (raw_codedPALocalProofOf_templateImpE3_shared_first_second_and4
    M hPA translation
    (rawTemplateContextCode translation
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep context))
    (coqFourStateTableAppendModePreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep index rowMode)
    (coqFourStateTableAppendFormulaPreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep index rowFormula)
    (coqFourStateTableAppendAssignmentCodePreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowAssignmentCode)
    (coqFourStateTableAppendAssignmentStepPreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowAssignmentStep)
    modeRoot formulaRoot assignmentCodeRoot assignmentStepRoot
    currentBoundRoot oldBoundRoot oldStateLookupRoot).
  - exact hmodeShape.
  - exact hformulaShape.
  - exact hassignmentCodeShape.
  - exact hassignmentStepShape.
  - exact hformulaFirst.
  - exact hassignmentCodeFirst.
  - exact hassignmentStepFirst.
  - exact hformulaSecond.
  - exact hassignmentCodeSecond.
  - exact hassignmentStepSecond.
  - exact hmode.
  - exact hformula.
  - exact hassignmentCode.
  - exact hassignmentStep.
  - exact hcurrentBound.
  - exact holdBound.
  - exact holdStateLookup.
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
