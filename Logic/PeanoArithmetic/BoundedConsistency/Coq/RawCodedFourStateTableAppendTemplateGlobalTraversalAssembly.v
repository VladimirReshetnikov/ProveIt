(**
  Reconstruct an appended global traversal with opaque template rows.

  The original append assembly closes a global source whose two local rows
  are metatheoretic PA formulae.  Native hierarchy successors instead expose
  nonstandard carrier formula codes through [TemplateFormula] leaves.  All
  six stable traversal fields and all witness-management lemmas are already
  independent of the row representation; only the displayed source and its
  opened-body normalization were specialized to [embedPAFormula].

  This module extracts that last layer.  It opens the generalized
  ten-existential source directly, proves that its first six fields still
  coincide with the append traversal record, and reuses the existing growing
  proof compiler to close an arbitrary pair of opaque row leaves.  No
  decoding operation, formula scopedness premise, semantic validity, or
  choice principle is introduced.
*)

From Stdlib Require Import List Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateRenamingSubstitution
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplateTripleUniversalOpening
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofEquality
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofExistentialIntroductionChain
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedPAAxiomWitnessPrefix
  RawCodedLtSuccCasesProofCompilation
  RawCodedFourStateTableAppendSource
  RawCodedFourStateTableAppendProofCompilation
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedFourStateTableAppendGlobalTraversalAssembly.

Module
  PABoundedRawCodedFourStateTableAppendTemplateGlobalTraversalAssembly.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateRenamingSubstitution.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateTripleUniversalOpening.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofEquality.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofExistentialIntroductionChain.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedFourStateTableAppendSource.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.

(** The generalized source has the same ten leading existential binders as
    the concrete source.  Shifting it by the eight append eigenvariables and
    opening the standard ten-witness tuple therefore exposes its traversal
    body without inspecting either row leaf. *)
Definition coqFourStateTableAppendOpenedTemplateGlobalFormula
    (rootMode : nat) (localSigma localPi : TemplateFormula)
    (bound : TemplateTerm) : TemplateFormula :=
  match templateExistentialOpenMany
    (templateFormulaShiftMany 8
      (coqDynamicTruthGlobalExistentialSource
        rootMode localSigma localPi))
    (coqFourStateTableAppendGlobalTraversalWitnesses bound) with
  | Some body => body
  | None => tfBot
  end.

Lemma coqFourStateTableAppendOpenedTemplateGlobalFormula_success : forall
    rootMode localSigma localPi bound,
  templateExistentialOpenMany
    (templateFormulaShiftMany 8
      (coqDynamicTruthGlobalExistentialSource
        rootMode localSigma localPi))
    (coqFourStateTableAppendGlobalTraversalWitnesses bound) =
  Some (coqFourStateTableAppendOpenedTemplateGlobalFormula
    rootMode localSigma localPi bound).
Proof. intros. reflexivity. Qed.

Definition coqFourStateTableAppendOpenedTemplateGlobalRows
    (rootMode : nat) (localSigma localPi : TemplateFormula)
    (bound : TemplateTerm) : TemplateFormula :=
  templateAnd7Seventh
    (coqFourStateTableAppendOpenedTemplateGlobalFormula
      rootMode localSigma localPi bound).

Definition coqFourStateTableAppendOpenedTemplateGlobalRowBody
    (rootMode : nat) (localSigma localPi : TemplateFormula)
    (bound : TemplateTerm) : TemplateFormula :=
  match templateUniversalBodyMany 5
    (coqFourStateTableAppendOpenedTemplateGlobalRows
      rootMode localSigma localPi bound) with
  | Some body => body
  | None => tfBot
  end.

Definition coqFourStateTableAppendOpenedTemplateGlobalRowProduction
    (rootMode : nat) (localSigma localPi : TemplateFormula)
    (bound : TemplateTerm) : TemplateFormula :=
  templateImpConsequent (templateImpConsequent
    (coqFourStateTableAppendOpenedTemplateGlobalRowBody
      rootMode localSigma localPi bound)).

Lemma coqFourStateTableAppendOpenedTemplateGlobalRows_success : forall
    rootMode localSigma localPi bound,
  templateUniversalBodyMany 5
    (coqFourStateTableAppendOpenedTemplateGlobalRows
      rootMode localSigma localPi bound) =
  Some (coqFourStateTableAppendOpenedTemplateGlobalRowBody
    rootMode localSigma localPi bound).
Proof. intros. reflexivity. Qed.

Lemma coqFourStateTableAppendOpenedTemplateGlobalRows_shape : forall
    rootMode localSigma localPi boundName,
  coqFourStateTableAppendOpenedTemplateGlobalRows
    rootMode localSigma localPi (ttParameter boundName) =
  templateFormulaAllMany 5
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
          rootMode localSigma localPi (ttParameter boundName)))).
Proof.
  intros rootMode localSigma localPi boundName.
  unfold coqFourStateTableAppendOpenedTemplateGlobalRows,
    coqFourStateTableAppendOpenedTemplateGlobalRowProduction,
    coqFourStateTableAppendOpenedTemplateGlobalRowBody,
    coqFourStateTableAppendOpenedTemplateGlobalFormula,
    coqDynamicTruthGlobalExistentialSource,
    coqDynamicTruthGlobalTraversalBodyTemplate,
    coqDynamicTruthGlobalRowsTemplate,
    templateAnd7Seventh, templateAndSecond, templateAndFirst,
    templateImpConsequent,
    coqFourStateTableAppendGlobalTraversalWitnesses.
  destruct rootMode as [|[|rootMode]]; reflexivity.
Qed.

Lemma coqFourStateTableAppendOpenedTemplateGlobalRowProduction_local_shape :
  forall rootMode localSigma localPi bound,
  coqFourStateTableAppendOpenedTemplateGlobalRowProduction
    rootMode localSigma localPi bound =
  tfOr
    (tfAnd (tfEq (ttVar 3) ttZero)
      (coqFourStateTableAppendOpenedLocalRowTemplate localSigma bound))
    (tfAnd (tfEq (ttVar 3) (ttSucc ttZero))
      (coqFourStateTableAppendOpenedLocalRowTemplate localPi bound)).
Proof. intros. reflexivity. Qed.

(** General fixed-substitution lemmas for template syntax.  Unlike the older
    embedded-PA versions, these include named parameters and opaque predicate
    applications, whose displayed arguments carry all scoping information. *)
Lemma templateTermSubst_template_scoped_fixed : forall
    scope input substitution,
  TemplateTermScoped scope input ->
  (forall index, index < scope -> substitution index = ttVar index) ->
  templateTermSubst substitution input = input.
Proof.
  intros scope input. revert scope.
  induction input; intros scope substitution hscope hfixed;
    cbn in hscope |- *; try reflexivity.
  - apply hfixed. exact hscope.
  - f_equal. exact (IHinput scope substitution hscope hfixed).
  - destruct hscope as [hleft hright].
    rewrite (IHinput1 scope substitution hleft hfixed),
      (IHinput2 scope substitution hright hfixed).
    reflexivity.
  - destruct hscope as [hleft hright].
    rewrite (IHinput1 scope substitution hleft hfixed),
      (IHinput2 scope substitution hright hfixed).
    reflexivity.
Qed.

Lemma templateTermsSubst_template_scoped_fixed : forall
    scope inputs substitution,
  TemplateTermsScoped scope inputs ->
  (forall index, index < scope -> substitution index = ttVar index) ->
  templateTermsSubst substitution inputs = inputs.
Proof.
  intros scope inputs. revert scope.
  induction inputs as [|input tail ih];
    intros scope substitution hscope hfixed; cbn in hscope |- *.
  - reflexivity.
  - destruct hscope as [hinput htail].
    f_equal.
    + exact (templateTermSubst_template_scoped_fixed
        scope input substitution hinput hfixed).
    + exact (ih scope substitution htail hfixed).
Qed.

Lemma templateFormulaSubst_template_scoped_fixed : forall
    scope input substitution,
  TemplateFormulaScoped scope input ->
  (forall index, index < scope -> substitution index = ttVar index) ->
  templateFormulaSubst substitution input = input.
Proof.
  intros scope input. revert scope.
  induction input; intros scope substitution hscope hfixed;
    cbn in hscope |- *; try reflexivity.
  - destruct hscope as [hleft hright].
    rewrite (templateTermSubst_template_scoped_fixed
      scope t substitution hleft hfixed),
      (templateTermSubst_template_scoped_fixed
        scope t0 substitution hright hfixed).
    reflexivity.
  - destruct hscope as [hleft hright].
    rewrite (IHinput1 scope substitution hleft hfixed),
      (IHinput2 scope substitution hright hfixed).
    reflexivity.
  - destruct hscope as [hleft hright].
    rewrite (IHinput1 scope substitution hleft hfixed),
      (IHinput2 scope substitution hright hfixed).
    reflexivity.
  - destruct hscope as [hleft hright].
    rewrite (IHinput1 scope substitution hleft hfixed),
      (IHinput2 scope substitution hright hfixed).
    reflexivity.
  - f_equal. apply IHinput with (scope := S scope).
    + exact hscope.
    + intros [|index] hindex; cbn [templateTermUpSubst].
      * reflexivity.
      * rewrite hfixed by lia. reflexivity.
  - f_equal. apply IHinput with (scope := S scope).
    + exact hscope.
    + intros [|index] hindex; cbn [templateTermUpSubst].
      * reflexivity.
      * rewrite hfixed by lia. reflexivity.
  - f_equal. exact (templateTermsSubst_template_scoped_fixed
      scope l substitution hscope hfixed).
Qed.

(** The append opening substitution fixes all local indices below thirteen.
    The proof is shared by ordinary and opaque rows through the structural
    scoping predicate above. *)
Lemma coqFourStateTableAppendOpenedLocalRowTemplate_template_scoped_identity :
  forall local bound,
  TemplateFormulaScoped 13 local ->
  coqFourStateTableAppendOpenedLocalRowTemplate local bound = local.
Proof.
  intros local bound hscope.
  unfold coqFourStateTableAppendOpenedLocalRowTemplate.
  cbn [templateFormulaExMany templateFormulaAllMany
    templateFormulaShiftMany templateExistentialOpenMany
    templateUniversalBodyMany templateFormulaOpen templateFormulaRename
    templateUpRenaming coqFourStateTableAppendGlobalTraversalWitnesses
    templateFormulaSubst templateTermUpSubst templateInstTerm].
  repeat rewrite templateFormulaRename_comp.
  repeat rewrite templateFormulaSubst_comp.
  rewrite templateFormulaSubst_rename.
  apply (templateFormulaSubst_template_scoped_fixed 13 local).
  - exact hscope.
  - intros index hindex.
    do 13 (destruct index as [|index]; [reflexivity | ]).
    lia.
Qed.

Theorem
    coqFourStateTableAppendTemplateClosedRowProduction_eq_opened : forall
    rootMode localSigma localPi bound,
  TemplateFormulaScoped 13 localSigma ->
  TemplateFormulaScoped 13 localPi ->
  templateFormulaReplaceParametersDirect
    coqFourStateTableAppendConcreteRowFieldBindings localSigma = localSigma ->
  templateFormulaReplaceParametersDirect
    coqFourStateTableAppendConcreteRowFieldBindings localPi = localPi ->
  coqFourStateTableAppendConcreteClosedRowProductionTemplate
    localSigma localPi =
  coqFourStateTableAppendOpenedTemplateGlobalRowProduction
    rootMode localSigma localPi bound.
Proof.
  intros rootMode localSigma localPi bound hSigma hPi
    hSigmaFields hPiFields.
  unfold coqFourStateTableAppendConcreteClosedRowProductionTemplate.
  rewrite hSigmaFields, hPiFields.
  rewrite
    coqFourStateTableAppendOpenedTemplateGlobalRowProduction_local_shape.
  rewrite
    (coqFourStateTableAppendOpenedLocalRowTemplate_template_scoped_identity
      localSigma bound hSigma),
    (coqFourStateTableAppendOpenedLocalRowTemplate_template_scoped_identity
      localPi bound hPi).
  reflexivity.
Qed.

(** Convert a proof of the concrete row implication into a proof of the
    seventh field extracted from the generalized source.  Notice that the
    argument does not inspect [localSigma] or [localPi]: clients may supply
    native, nonstandard formula codes as opaque template leaves.  The sole
    normalization obligation is the displayed production equality. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_opened_template_global_rows_of_concrete_row :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    rootMode (localSigma localPi : TemplateFormula) boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
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
      (ttVar 0) (ttVar 1) (ttVar 2) [])
    (rawTemplateFormula translation
      (coqFourStateTableAppendOpenedTemplateGlobalRows
        rootMode localSigma localPi (ttParameter boundName))).
Proof.
  intros M hPA translation
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
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
      (ttVar 0) (ttVar 1) (ttVar 2)
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

(** Ordinary PA syntax embeds into the structural template scoping
    predicate.  These compatibility lemmas are useful to old clients and to
    mixed opaque/embedded rows, while the new append endpoint itself remains
    fully template-generic. *)
Lemma templateTermScoped_embedPA : forall scope input,
  StandardTermScoped scope input ->
  TemplateTermScoped scope (embedPATerm input).
Proof.
  intros scope input. revert scope.
  induction input; intros scope hscope;
    cbn [embedPATerm TemplateTermScoped].
  - apply hscope. reflexivity.
  - exact I.
  - apply IHinput. intros index hfree. apply hscope. exact hfree.
  - split.
    + apply IHinput1. intros index hfree. apply hscope. now left.
    + apply IHinput2. intros index hfree. apply hscope. now right.
  - split.
    + apply IHinput1. intros index hfree. apply hscope. now left.
    + apply IHinput2. intros index hfree. apply hscope. now right.
Qed.

Lemma templateFormulaScoped_embedPA : forall scope input,
  StandardFormulaScoped scope input ->
  TemplateFormulaScoped scope (embedPAFormula input).
Proof.
  intros scope input. revert scope.
  induction input; intros scope hscope;
    cbn [embedPAFormula TemplateFormulaScoped].
  - split.
    + apply templateTermScoped_embedPA. intros index hfree.
      apply hscope. now left.
    + apply templateTermScoped_embedPA. intros index hfree.
      apply hscope. now right.
  - exact I.
  - split.
    + apply IHinput1. intros index hfree. apply hscope. now left.
    + apply IHinput2. intros index hfree. apply hscope. now right.
  - split.
    + apply IHinput1. intros index hfree. apply hscope. now left.
    + apply IHinput2. intros index hfree. apply hscope. now right.
  - split.
    + apply IHinput1. intros index hfree. apply hscope. now left.
    + apply IHinput2. intros index hfree. apply hscope. now right.
  - apply IHinput. exact (StandardFormulaScoped_binder scope input hscope).
  - apply IHinput. exact (StandardFormulaScoped_ex_binder scope input hscope).
Qed.

(** The generalized opening is constructor-for-constructor compatible with
    the historical concrete opening.  This regression lemma keeps the new
    API conservative and lets downstream clients migrate independently. *)
Lemma coqFourStateTableAppendOpenedTemplateGlobalFormula_embed : forall
    rootMode localSigma localPi bound,
  coqFourStateTableAppendOpenedTemplateGlobalFormula rootMode
      (embedPAFormula localSigma) (embedPAFormula localPi) bound =
    coqFourStateTableAppendOpenedGlobalFormulaTemplate
      rootMode localSigma localPi bound.
Proof.
  intros rootMode localSigma localPi bound.
  unfold coqFourStateTableAppendOpenedTemplateGlobalFormula,
    coqFourStateTableAppendOpenedGlobalFormulaTemplate.
  rewrite coqDynamicTruthGlobalExistentialSource_embed.
  reflexivity.
Qed.

Lemma coqFourStateTableAppendOpenedTemplateGlobalFormula_and7_shape : forall
    rootMode localSigma localPi bound,
  let source := coqFourStateTableAppendOpenedTemplateGlobalFormula
    rootMode localSigma localPi bound in
  source = tfAnd (templateAnd7First source)
    (tfAnd (templateAnd7Second source)
      (tfAnd (templateAnd7Third source)
        (tfAnd (templateAnd7Fourth source)
          (tfAnd (templateAnd7Fifth source)
            (tfAnd (templateAnd7Sixth source)
              (templateAnd7Seventh source)))))).
Proof. intros. reflexivity. Qed.

(** Only the seventh field contains the opaque rows.  The first six fields
    normalize exactly as before because their syntax depends solely on the
    fixed append witnesses. *)
Lemma coqFourStateTableAppendOpenedTemplateGlobalFormula_field_shapes :
  forall rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep,
  rootMode = 0 \/ rootMode = 1 ->
  let source := coqFourStateTableAppendOpenedTemplateGlobalFormula
    rootMode localSigma localPi (ttParameter boundName) in
  templateAnd7First source =
    coqFourStateTableAppendModeDefinedTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2) /\
  templateAnd7Second source =
    coqFourStateTableAppendFormulaDefinedTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2) /\
  templateAnd7Third source =
    coqFourStateTableAppendAssignmentCodeDefinedTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2) /\
  templateAnd7Fourth source =
    coqFourStateTableAppendAssignmentStepDefinedTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2) /\
  templateAnd7Fifth source =
    coqFourStateTableAppendRootBoundTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2) /\
  templateAnd7Sixth source =
    coqFourStateTableAppendNewStateLookupTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2).
Proof.
  intros rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep [-> | ->];
    cbn zeta; repeat split; reflexivity.
Qed.

Lemma coqFourStateTableAppendOpenedTemplateGlobalFormula_shape : forall
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep,
  rootMode = 0 \/ rootMode = 1 ->
  coqFourStateTableAppendOpenedTemplateGlobalFormula
    rootMode localSigma localPi (ttParameter boundName) =
  coqFourStateTableAppendTraversalBodyTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName)
    (embedPATerm (Term.numeral rootMode))
    (ttVar 0) (ttVar 1) (ttVar 2)
    (coqFourStateTableAppendOpenedTemplateGlobalRows
      rootMode localSigma localPi (ttParameter boundName)).
Proof.
  intros rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep hrootMode.
  pose proof
    (coqFourStateTableAppendOpenedTemplateGlobalFormula_and7_shape
      rootMode localSigma localPi (ttParameter boundName)) as hshape.
  destruct
    (coqFourStateTableAppendOpenedTemplateGlobalFormula_field_shapes
      rootMode localSigma localPi boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep hrootMode)
    as [hmode [hformula [hassignmentCode
      [hassignmentStep [hbound hlookup]]]]].
  rewrite hshape.
  unfold coqFourStateTableAppendTraversalBodyTemplate,
    coqFourStateTableAppendOpenedTemplateGlobalRows.
  rewrite hmode, hformula, hassignmentCode, hassignmentStep, hbound, hlookup.
  reflexivity.
Qed.

(** Generic source reconstruction.  The premise is precisely a growing proof
    of the extracted seventh field; the established append compiler supplies
    the other six fields, introduces the ten global witnesses, and removes
    the eight append eigenvariables. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_template_global_of_append_rows :
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
  let formula := ttVar 0 in
  let assignmentCode := ttVar 1 in
  let assignmentStep := ttVar 2 in
  let prefix := coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep [] in
  let opened := coqFourStateTableAppendOpenedTemplateGlobalFormula
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
      (coqDynamicTruthGlobalExistentialSource
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
    (raw_codedPAGrowingTemplateLocalProofAt_four_state_table_append_traversal_body
      M hPA translation hagreement
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2)
      witnesses
      (coqFourStateTableAppendOpenedTemplateGlobalRows
        rootMode localSigma localPi (ttParameter boundName)) hrows)
    as hbody.
  pose proof
    (coqFourStateTableAppendOpenedTemplateGlobalFormula_shape
      rootMode localSigma localPi boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep hrootMode) as hopenedShape.
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
          (ttVar 0) (ttVar 1) (ttVar 2) []))
      (templateFormulaShiftMany 8
        (coqDynamicTruthGlobalExistentialSource
          rootMode localSigma localPi))
      (coqFourStateTableAppendGlobalTraversalWitnesses
        (ttParameter boundName))
      (coqFourStateTableAppendOpenedTemplateGlobalFormula
        rootMode localSigma localPi (ttParameter boundName))
      bodyRoot
      (coqFourStateTableAppendOpenedTemplateGlobalFormula_success
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
        (ttVar 0) (ttVar 1) (ttVar 2) [])
      (rawTemplateFormula translation
        (templateFormulaShiftMany 8
          (coqDynamicTruthGlobalExistentialSource
            rootMode localSigma localPi)))).
  {
    unfold RawCodedPAGrowingTemplateLocalProofAt.
    exists finalWitnessList, finalContext, globalRoot.
    split; [exact hfinal |].
    split; [exact hincluded | exact hglobal].
  }
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_four_state_table_append_ex8_elimination
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqDynamicTruthGlobalExistentialSource
        rootMode localSigma localPi)
      appendRoot
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2)
      hsource happend hcontinuation).
Qed.

(** Public composition of opaque-row reconstruction with global closure.
    This is the generalized counterpart of the historical embedded-PA
    endpoint.  In particular, its conclusion is the native template source,
    rather than an embedding of a metatheoretic [formula]. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_template_global_of_append_concrete_row :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    rootMode (localSigma localPi : TemplateFormula) boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses sigmaProduction piProduction appendRoot,
  rootMode = 0 \/ rootMode = 1 ->
  coqFourStateTableAppendConcreteClosedRowProductionTemplate
      sigmaProduction piProduction =
    coqFourStateTableAppendOpenedTemplateGlobalRowProduction
      rootMode localSigma localPi (ttParameter boundName) ->
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
            sigmaProduction piProduction)))) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) []
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource
        rootMode localSigma localPi)).
Proof.
  intros M hPA translation hagreement
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses sigmaProduction piProduction appendRoot
    hrootMode hproduction happend hrow.
  apply
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_template_global_of_append_rows
      M hPA translation hagreement
      rootMode localSigma localPi boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      witnesses appendRoot hrootMode happend).
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_opened_template_global_rows_of_concrete_row
      M hPA translation
      rootMode localSigma localPi boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      witnesses sigmaProduction piProduction hproduction hrow).
Qed.

End
  PABoundedRawCodedFourStateTableAppendTemplateGlobalTraversalAssembly.
