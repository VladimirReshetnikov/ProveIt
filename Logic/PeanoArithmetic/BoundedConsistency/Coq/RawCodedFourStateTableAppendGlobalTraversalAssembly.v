(**
  Assemble the seven fields of a global traversal after table append.

  The simultaneous append theorem supplies six stable facts in its deepest
  eight-witness context: four defined-through fields, the new root bound, and
  the lookup at the appended row.  The row compiler supplies the seventh fact
  and may grow the witnessed PA tail.  This module identifies the append
  context as a fixed template prefix over that tail and combines all seven
  facts in the dependency order required by the global successor.
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedRestrictedPAProof
  RawCodedContextLists
  RawCodedProofAssumptionLeaf
  RawCodedProofImpIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPAAxiomWitnessPrefix
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthTraversal
  RawCodedFormulaShiftSourceAtomicAdequacy
  RawCodedTemplateSyntax
  RawCodedTemplateRenamingSubstitution
  RawCodedTemplateStructuralTranslation
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateParameterAbstraction
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedPALocalProofExistentialIntroductionChain
  RawCodedPALocalProofEquality
  RawCodedLtSuccCasesProofCompilation
  RawCodedBetaLookupFunctionalitySource
  RawCodedBetaLookupFunctionalityProofCompilation
  RawCodedFourStateTableAppendSource
  RawCodedFourStateTableAppendProofCompilation
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedPAGrowingTemplateConjunction.

Module PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFormulaShiftSourceAtomicAdequacy.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateRenamingSubstitution.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedPALocalProofExistentialIntroductionChain.
Import PABoundedRawCodedPALocalProofEquality.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedBetaLookupFunctionalitySource.
Import PABoundedRawCodedBetaLookupFunctionalityProofCompilation.
Import PABoundedRawCodedFourStateTableAppendSource.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedPAGrowingTemplateConjunction.

(** Atomic adequacy is already implicit in the template-translation
    contract.  Its represented unit-shift trace proves the source formula
    adequate, even when that source is a genuinely nonstandard code. *)
Theorem raw_codedTemplateFormula_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M) input,
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation input).
Proof.
  intros M hPA translation input.
  exact (raw_codedFormulaShift_source_atomically_adequate_core
    M hPA (raw_zero M) (rawNumeralValue M 1)
    (rawTemplateFormula translation input)
    (rawTemplateFormula translation (templateFormulaRename S input))
    (rawTemplateFormula_shift translation input)).
Qed.

(** Hence every finite template prefix is adequate.  Retaining the list
    argument makes this a drop-in discharge for all prefix-general proof
    compilers, without imposing structural-translation-specific premises. *)
Corollary raw_codedTemplatePrefix_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M) prefix,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix.
Proof.
  intros M hPA translation prefix input _.
  exact (raw_codedTemplateFormula_atomically_adequate
    M hPA translation input).
Qed.

(** The deepest append context is affine in its caller-provided tail.  Eight
    eigenvariables shift the tail eight times, while the finite assumption
    prefix is exactly the context obtained from an empty tail. *)
Lemma coqFourStateTableAppendWitnessContext_affine : forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep context,
  coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep context =
  coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep [] ++
  templateContextShiftMany 8 context.
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
    templateExistentialEliminationContext
    templateContextShiftMany templateContextShift templateContextRename].
  reflexivity.
Qed.

(** Carrier-code form of the affine identity for a standard witnessed PA
    tail.  Agreement is used only to identify the embedded axiom list with
    the synchronized carrier-coded context selected by that witness batch. *)
Lemma raw_fourStateTableAppendWitnessContext_witnessed_tail_code : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep witnesses,
  rawTemplateContextCode translation
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      (embedPAContext (map witnessedAxiom witnesses))) =
  rawTemplateContextCodeOnTail translation
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep []).
Proof.
  intros M translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep witnesses.
  rewrite coqFourStateTableAppendWitnessContext_affine.
  rewrite templateContextShiftMany_embedPAAxiomWitnesses_fixed.
  rewrite raw_templateContextCode_app_on_tail_general.
  rewrite (raw_templateContextCode_embedPAAxiomWitnesses
    M translation hagreement witnesses).
  reflexivity.
Qed.

(** The literal right-associated record shape consumed by the global truth
    traversal.  The row field is left abstract so the assembler can be reused
    before and after its five universal introductions. *)
Definition coqFourStateTableAppendTraversalBodyTemplate
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep : TemplateTerm)
    (rows : TemplateFormula) : TemplateFormula :=
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
        (tfAnd
          (coqFourStateTableAppendAssignmentStepDefinedTemplate
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            bound mode formula assignmentCode assignmentStep)
          (tfAnd
            (coqFourStateTableAppendRootBoundTemplate
              modeCode modeStep formulaCode formulaStep
              assignmentCodeCode assignmentCodeStep
              assignmentStepCode assignmentStepStep
              bound mode formula assignmentCode assignmentStep)
            (tfAnd
              (coqFourStateTableAppendNewStateLookupTemplate
                modeCode modeStep formulaCode formulaStep
                assignmentCodeCode assignmentCodeStep
                assignmentStepCode assignmentStepStep
                bound mode formula assignmentCode assignmentStep)
              rows))))).

(** Witness tuple for the shifted global formula.  The first two entries are
    the successor traversal bound and its root index.  The remaining eight
    entries are precisely the append eigenvariables, in the same code/step
    order as [fixedTruthTraversalEx10]. *)
Definition coqFourStateTableAppendGlobalTraversalWitnesses
    (bound : TemplateTerm) : list TemplateTerm :=
  [ttSucc bound; bound;
   ttVar 7; ttVar 6; ttVar 5; ttVar 4;
   ttVar 3; ttVar 2; ttVar 1; ttVar 0].

Definition coqFourStateTableAppendOpenedGlobalFormulaTemplate
    (rootMode : nat) (localSigma localPi : formula)
    (bound : TemplateTerm) : TemplateFormula :=
  match templateExistentialOpenMany
    (templateFormulaShiftMany 8
      (embedPAFormula
        (dynamicTruthGlobalFormula (Term.numeral rootMode)
          localSigma localPi)))
    (coqFourStateTableAppendGlobalTraversalWitnesses bound) with
  | Some body => body
  | None => tfBot
  end.

(** The global formula has exactly ten leading existential binders, so the
    fallback in the preceding client-facing definition is unreachable. *)
Lemma coqFourStateTableAppendOpenedGlobalFormulaTemplate_success : forall
    rootMode localSigma localPi bound,
  templateExistentialOpenMany
    (templateFormulaShiftMany 8
      (embedPAFormula
        (dynamicTruthGlobalFormula (Term.numeral rootMode)
          localSigma localPi)))
    (coqFourStateTableAppendGlobalTraversalWitnesses bound) =
  Some (coqFourStateTableAppendOpenedGlobalFormulaTemplate
    rootMode localSigma localPi bound).
Proof.
  intros.
  reflexivity.
Qed.

(** Named projections of a right-associated seven-way conjunction. *)
Definition templateAnd7First (source : TemplateFormula)
    : TemplateFormula := templateAndFirst source.
Definition templateAnd7Second (source : TemplateFormula)
    : TemplateFormula := templateAndFirst (templateAndSecond source).
Definition templateAnd7Third (source : TemplateFormula)
    : TemplateFormula :=
  templateAndFirst (templateAndSecond (templateAndSecond source)).
Definition templateAnd7Fourth (source : TemplateFormula)
    : TemplateFormula :=
  templateAndFirst (templateAndSecond
    (templateAndSecond (templateAndSecond source))).
Definition templateAnd7Fifth (source : TemplateFormula)
    : TemplateFormula :=
  templateAndFirst (templateAndSecond (templateAndSecond
    (templateAndSecond (templateAndSecond source)))).
Definition templateAnd7Sixth (source : TemplateFormula)
    : TemplateFormula :=
  templateAndFirst (templateAndSecond (templateAndSecond
    (templateAndSecond (templateAndSecond (templateAndSecond source))))).
Definition templateAnd7Seventh (source : TemplateFormula)
    : TemplateFormula :=
  templateAndSecond (templateAndSecond (templateAndSecond
    (templateAndSecond (templateAndSecond (templateAndSecond source))))).

(** Partial inverse of a finite universal prefix.  This is kept separate from
    [templateFormulaAllMany]: success certifies the literal binder count. *)
Fixpoint templateUniversalBodyMany
    (count : nat) (source : TemplateFormula) : option TemplateFormula :=
  match count with
  | 0 => Some source
  | S smaller =>
      match source with
      | tfAll body => templateUniversalBodyMany smaller body
      | _ => None
      end
  end.

Definition coqFourStateTableAppendOpenedGlobalRowsTemplate
    (rootMode : nat) (localSigma localPi : formula)
    (bound : TemplateTerm) : TemplateFormula :=
  templateAnd7Seventh
    (coqFourStateTableAppendOpenedGlobalFormulaTemplate
      rootMode localSigma localPi bound).

Definition coqFourStateTableAppendOpenedGlobalRowBodyTemplate
    (rootMode : nat) (localSigma localPi : formula)
    (bound : TemplateTerm) : TemplateFormula :=
  match templateUniversalBodyMany 5
    (coqFourStateTableAppendOpenedGlobalRowsTemplate
      rootMode localSigma localPi bound) with
  | Some body => body
  | None => tfBot
  end.

Definition coqFourStateTableAppendOpenedGlobalRowProductionTemplate
    (rootMode : nat) (localSigma localPi : formula)
    (bound : TemplateTerm) : TemplateFormula :=
  templateImpConsequent (templateImpConsequent
    (coqFourStateTableAppendOpenedGlobalRowBodyTemplate
      rootMode localSigma localPi bound)).

Lemma coqFourStateTableAppendOpenedGlobalRowsTemplate_success : forall
    rootMode localSigma localPi bound,
  templateUniversalBodyMany 5
    (coqFourStateTableAppendOpenedGlobalRowsTemplate
      rootMode localSigma localPi bound) =
  Some (coqFourStateTableAppendOpenedGlobalRowBodyTemplate
    rootMode localSigma localPi bound).
Proof.
  intros. reflexivity.
Qed.

(** The extracted row has exactly the premise spine compiled earlier:
    [i < S b], followed by lookup of all four row values.  Only the final
    polarity production remains abstract in this theorem. *)
Lemma coqFourStateTableAppendOpenedGlobalRowsTemplate_shape : forall
    rootMode localSigma localPi boundName,
  coqFourStateTableAppendOpenedGlobalRowsTemplate
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
        (coqFourStateTableAppendOpenedGlobalRowProductionTemplate
          rootMode localSigma localPi (ttParameter boundName)))).
Proof.
  intros.
  reflexivity.
Qed.

(** Ordinary embedded PA syntax contains no named template parameters.
    Direct parameter replacement is therefore inert at every binder depth.
    These small structural lemmas keep that fact explicit instead of asking
    reduction to traverse an arbitrary client formula repeatedly. *)
Lemma templateTermReplaceParameterAt_embedPATerm : forall
    name depth replacement input,
  templateTermReplaceParameterAt name depth replacement
    (embedPATerm input) = embedPATerm input.
Proof.
  intros name depth replacement input.
  induction input; cbn [embedPATerm templateTermReplaceParameterAt];
    try reflexivity.
  - now rewrite IHinput.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
Qed.

Lemma templateFormulaReplaceParameterAt_embedPAFormula : forall
    name depth replacement input,
  templateFormulaReplaceParameterAt name depth replacement
    (embedPAFormula input) = embedPAFormula input.
Proof.
  intros name depth replacement input. revert depth.
  induction input; intro depth;
    cbn [embedPAFormula templateFormulaReplaceParameterAt].
  - now rewrite !templateTermReplaceParameterAt_embedPATerm.
  - reflexivity.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput.
  - now rewrite IHinput.
Qed.

(** A template substitution which fixes the advertised free-variable scope
    fixes embedded ordinary PA syntax.  The formulation is intentionally
    generic: later opening calculations only need to establish the
    pointwise behavior of their (possibly very large) composed substitution. *)
Lemma templateTermSubst_embedPATerm_scoped_fixed : forall
    scope input substitution,
  StandardTermScoped scope input ->
  (forall index, index < scope -> substitution index = ttVar index) ->
  templateTermSubst substitution (embedPATerm input) = embedPATerm input.
Proof.
  intros scope input. revert scope.
  induction input; intros scope substitution hscope hfixed;
    cbn [embedPATerm templateTermSubst].
  - apply hfixed. apply hscope. reflexivity.
  - reflexivity.
  - f_equal. apply IHinput with (scope := scope).
    + intros index hfree. apply hscope. exact hfree.
    + exact hfixed.
  - f_equal.
    + apply IHinput1 with (scope := scope).
      * intros index hfree. apply hscope. now left.
      * exact hfixed.
    + apply IHinput2 with (scope := scope).
      * intros index hfree. apply hscope. now right.
      * exact hfixed.
  - f_equal.
    + apply IHinput1 with (scope := scope).
      * intros index hfree. apply hscope. now left.
      * exact hfixed.
    + apply IHinput2 with (scope := scope).
      * intros index hfree. apply hscope. now right.
      * exact hfixed.
Qed.

Lemma templateFormulaSubst_embedPAFormula_scoped_fixed : forall
    scope input substitution,
  StandardFormulaScoped scope input ->
  (forall index, index < scope -> substitution index = ttVar index) ->
  templateFormulaSubst substitution (embedPAFormula input) =
  embedPAFormula input.
Proof.
  intros scope input. revert scope.
  induction input; intros scope substitution hscope hfixed;
    cbn [embedPAFormula templateFormulaSubst].
  - f_equal.
    + apply templateTermSubst_embedPATerm_scoped_fixed with (scope := scope).
      * intros index hfree. apply hscope. now left.
      * exact hfixed.
    + apply templateTermSubst_embedPATerm_scoped_fixed with (scope := scope).
      * intros index hfree. apply hscope. now right.
      * exact hfixed.
  - reflexivity.
  - f_equal.
    + apply IHinput1 with (scope := scope).
      * intros index hfree. apply hscope. now left.
      * exact hfixed.
    + apply IHinput2 with (scope := scope).
      * intros index hfree. apply hscope. now right.
      * exact hfixed.
  - f_equal.
    + apply IHinput1 with (scope := scope).
      * intros index hfree. apply hscope. now left.
      * exact hfixed.
    + apply IHinput2 with (scope := scope).
      * intros index hfree. apply hscope. now right.
      * exact hfixed.
  - f_equal.
    + apply IHinput1 with (scope := scope).
      * intros index hfree. apply hscope. now left.
      * exact hfixed.
    + apply IHinput2 with (scope := scope).
      * intros index hfree. apply hscope. now right.
      * exact hfixed.
  - f_equal. apply IHinput with (scope := S scope).
    + exact (StandardFormulaScoped_binder scope input hscope).
    + intros [|index] hindex; [reflexivity |].
      cbn [templateTermUpSubst].
      rewrite (hfixed index) by lia.
      reflexivity.
  - f_equal. apply IHinput with (scope := S scope).
    + exact (StandardFormulaScoped_ex_binder scope input hscope).
    + intros [|index] hindex; [reflexivity |].
      cbn [templateTermUpSubst].
      rewrite (hfixed index) by lia.
      reflexivity.
Qed.

Lemma templateFormulaReplaceParametersDirect_embedPAFormula : forall
    bindings input,
  templateFormulaReplaceParametersDirect bindings (embedPAFormula input) =
  embedPAFormula input.
Proof.
  induction bindings as [|[name replacement] remaining ih]; intro input.
  - reflexivity.
  - cbn [templateFormulaReplaceParametersDirect].
    unfold templateFormulaReplaceParameter.
    rewrite templateFormulaReplaceParameterAt_embedPAFormula.
    exact (ih input).
Qed.

(** The concrete row normal form already agrees with the desired polarity
    split when its two bodies are embedded ordinary PA formulae. *)
Lemma
    coqFourStateTableAppendConcreteClosedRowProductionTemplate_embedded_shape :
  forall localSigma localPi,
  coqFourStateTableAppendConcreteClosedRowProductionTemplate
    (embedPAFormula localSigma) (embedPAFormula localPi) =
  tfOr
    (tfAnd (tfEq (ttVar 3) ttZero) (embedPAFormula localSigma))
    (tfAnd (tfEq (ttVar 3) (ttSucc ttZero))
      (embedPAFormula localPi)).
Proof.
  intros localSigma localPi.
  unfold coqFourStateTableAppendConcreteClosedRowProductionTemplate.
  now rewrite !templateFormulaReplaceParametersDirect_embedPAFormula.
Qed.

(** A small template-only view of the ten global existential binders around
    the five local-row binders.  Isolating this spine prevents the scoped
    normalization proof from reducing the unrelated six traversal fields. *)
Fixpoint templateFormulaExMany
    (count : nat) (body : TemplateFormula) : TemplateFormula :=
  match count with
  | 0 => body
  | S smaller => tfEx (templateFormulaExMany smaller body)
  end.

Definition coqFourStateTableAppendOpenedLocalRowTemplate
    (local : TemplateFormula) (bound : TemplateTerm) : TemplateFormula :=
  match templateExistentialOpenMany
    (templateFormulaShiftMany 8
      (templateFormulaExMany 10 (templateFormulaAllMany 5 local)))
    (coqFourStateTableAppendGlobalTraversalWitnesses bound) with
  | Some rows =>
      match templateUniversalBodyMany 5 rows with
      | Some body => body
      | None => tfBot
      end
  | None => tfBot
  end.

(** Projection from the complete opened traversal to the two local polarity
    bodies.  This is definitional, but naming it makes the expensive global
    normalization happen only once in downstream proofs. *)
Lemma coqFourStateTableAppendOpenedGlobalRowProductionTemplate_local_shape :
  forall rootMode localSigma localPi bound,
  coqFourStateTableAppendOpenedGlobalRowProductionTemplate
    rootMode localSigma localPi bound =
  tfOr
    (tfAnd (tfEq (ttVar 3) ttZero)
      (coqFourStateTableAppendOpenedLocalRowTemplate
        (embedPAFormula localSigma) bound))
    (tfAnd (tfEq (ttVar 3) (ttSucc ttZero))
      (coqFourStateTableAppendOpenedLocalRowTemplate
        (embedPAFormula localPi) bound)).
Proof. intros. reflexivity. Qed.

(** The eight append witnesses occupy exactly local indices [5..12].
    After fusing the eight shifts with all ten openings, the resulting
    substitution fixes those indices and the five row indices [0..4].
    Values at indices [13] and above may mention [bound], so the scope
    hypothesis is both sufficient and necessary. *)
Lemma coqFourStateTableAppendOpenedLocalRowTemplate_scoped_identity : forall
    local bound,
  StandardFormulaScoped 13 local ->
  coqFourStateTableAppendOpenedLocalRowTemplate
    (embedPAFormula local) bound = embedPAFormula local.
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
  apply (templateFormulaSubst_embedPAFormula_scoped_fixed 13 local).
  - exact hscope.
  - intros index hindex.
    do 13 (destruct index as [|index]; [reflexivity | ]).
    lia.
Qed.

(** The final production equality consumed by the concrete-row/global
    adapter.  It is independent of the root mode and of the bound term once
    the two local rows are scoped to their advertised thirteen variables. *)
Theorem
    coqFourStateTableAppendConcreteClosedRowProductionTemplate_embedded_eq_opened :
  forall rootMode localSigma localPi bound,
  StandardFormulaScoped 13 localSigma ->
  StandardFormulaScoped 13 localPi ->
  coqFourStateTableAppendConcreteClosedRowProductionTemplate
    (embedPAFormula localSigma) (embedPAFormula localPi) =
  coqFourStateTableAppendOpenedGlobalRowProductionTemplate
    rootMode localSigma localPi bound.
Proof.
  intros rootMode localSigma localPi bound hSigma hPi.
  rewrite
    coqFourStateTableAppendConcreteClosedRowProductionTemplate_embedded_shape.
  rewrite
    coqFourStateTableAppendOpenedGlobalRowProductionTemplate_local_shape.
  rewrite (coqFourStateTableAppendOpenedLocalRowTemplate_scoped_identity
    localSigma bound hSigma).
  rewrite (coqFourStateTableAppendOpenedLocalRowTemplate_scoped_identity
    localPi bound hPi).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Parameter replacement and context shifts.

    A temporary prefix is shifted once whenever a new row variable is
    introduced.  Named parameters are inert under that shift, whereas the
    concrete term replacing a parameter must itself be shifted.  The
    following depth-indexed lemmas establish that these two orders agree,
    including below quantifiers and inside opaque argument lists. *)

Lemma templateOpeningSubstAt_rename_succ_at_depth : forall
    depth replacement,
  templateOpeningSubstAt depth (templateTermRename S replacement) depth =
  templateTermRename (templateShiftRenamingAt depth)
    (templateOpeningSubstAt depth replacement depth).
Proof.
  induction depth as [|depth ih]; intro replacement.
  - reflexivity.
  - cbn [templateOpeningSubstAt templateTermUpSubst].
    rewrite ih, !templateTermRename_comp.
    apply templateTermRename_ext. intro index.
    rewrite templateShiftRenamingAt_succ.
    destruct index; reflexivity.
Qed.

Lemma templateTermReplaceParameterAt_rename_succ : forall
    name depth replacement input,
  templateTermReplaceParameterAt name depth
    (templateTermRename S replacement)
    (templateTermRename (templateShiftRenamingAt depth) input) =
  templateTermRename (templateShiftRenamingAt depth)
    (templateTermReplaceParameterAt name depth replacement input).
Proof.
  intros name depth replacement input.
  induction input;
    cbn [templateTermReplaceParameterAt templateTermRename].
  - reflexivity.
  - destruct (Nat.eqb t name).
    + apply templateOpeningSubstAt_rename_succ_at_depth.
    + reflexivity.
  - reflexivity.
  - now rewrite IHinput.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
Qed.

Lemma templateFormulaReplaceParameterAt_rename_succ : forall
    name depth replacement input,
  templateFormulaReplaceParameterAt name depth
    (templateTermRename S replacement)
    (templateFormulaRename (templateShiftRenamingAt depth) input) =
  templateFormulaRename (templateShiftRenamingAt depth)
    (templateFormulaReplaceParameterAt name depth replacement input).
Proof.
  intros name depth replacement input. revert depth.
  induction input; intro depth;
    cbn [templateFormulaReplaceParameterAt templateFormulaRename].
  - now rewrite !templateTermReplaceParameterAt_rename_succ.
  - reflexivity.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - f_equal. rewrite <- !templateFormulaRename_shift_succ.
    apply IHinput.
  - f_equal. rewrite <- !templateFormulaRename_shift_succ.
    apply IHinput.
  - unfold templateTermsReplaceParameterAt, templateTermsRename.
    rewrite !map_map. f_equal.
    apply map_ext. intro argument.
    apply templateTermReplaceParameterAt_rename_succ.
Qed.

Corollary templateFormulaReplaceParameter_rename_succ : forall
    name replacement input,
  templateFormulaReplaceParameter name (templateTermRename S replacement)
    (templateFormulaRename S input) =
  templateFormulaRename S
    (templateFormulaReplaceParameter name replacement input).
Proof.
  intros name replacement input.
  unfold templateFormulaReplaceParameter.
  change
    (templateFormulaReplaceParameterAt name 0
      (templateTermRename S replacement)
      (templateFormulaRename (templateShiftRenamingAt 0) input) =
     templateFormulaRename (templateShiftRenamingAt 0)
      (templateFormulaReplaceParameterAt name 0 replacement input)).
  apply templateFormulaReplaceParameterAt_rename_succ.
Qed.

Definition templateParameterBindingsRename
    (renaming : nat -> nat)
    (bindings : list (TemplateParameterName * TemplateTerm))
    : list (TemplateParameterName * TemplateTerm) :=
  map (fun binding =>
    (fst binding, templateTermRename renaming (snd binding))) bindings.

Lemma templateFormulaReplaceParametersDirect_rename_succ : forall
    bindings input,
  templateFormulaReplaceParametersDirect
    (templateParameterBindingsRename S bindings)
    (templateFormulaRename S input) =
  templateFormulaRename S
    (templateFormulaReplaceParametersDirect bindings input).
Proof.
  induction bindings as [|[name replacement] remaining ih]; intro input.
  - reflexivity.
  - change
      (templateFormulaReplaceParametersDirect
        (templateParameterBindingsRename S remaining)
        (templateFormulaReplaceParameter name
          (templateTermRename S replacement)
          (templateFormulaRename S input)) =
       templateFormulaRename S
        (templateFormulaReplaceParametersDirect remaining
          (templateFormulaReplaceParameter name replacement input))).
    rewrite templateFormulaReplaceParameter_rename_succ.
    apply ih.
Qed.

Definition templateContextReplaceParametersDirect
    (bindings : list (TemplateParameterName * TemplateTerm))
    (context : TemplateContext) : TemplateContext :=
  map (templateFormulaReplaceParametersDirect bindings) context.

Lemma templateContextReplaceParametersDirect_shift : forall
    bindings context,
  templateContextReplaceParametersDirect
    (templateParameterBindingsRename S bindings)
    (templateContextShift context) =
  templateContextShift
    (templateContextReplaceParametersDirect bindings context).
Proof.
  intros bindings context.
  unfold templateContextReplaceParametersDirect,
    templateContextShift, templateContextRename.
  rewrite !map_map.
  apply map_ext. intro formula.
  apply templateFormulaReplaceParametersDirect_rename_succ.
Qed.

Fixpoint templateParameterBindingsShiftMany
    (count : nat)
    (bindings : list (TemplateParameterName * TemplateTerm))
    : list (TemplateParameterName * TemplateTerm) :=
  match count with
  | 0 => bindings
  | S smaller =>
      templateParameterBindingsShiftMany smaller
        (templateParameterBindingsRename S bindings)
  end.

Lemma templateContextReplaceParametersDirect_shift_many : forall
    count bindings context,
  templateContextReplaceParametersDirect
    (templateParameterBindingsShiftMany count bindings)
    (templateContextShiftMany count context) =
  templateContextShiftMany count
    (templateContextReplaceParametersDirect bindings context).
Proof.
  induction count as [|smaller ih]; intros bindings context.
  - reflexivity.
  - cbn [templateParameterBindingsShiftMany templateContextShiftMany].
    rewrite (ih (templateParameterBindingsRename S bindings)
      (templateContextShift context)).
    rewrite templateContextReplaceParametersDirect_shift.
    reflexivity.
Qed.

(** The four carrier parameters used by the row compiler are instantiated at
    the root of the five row binders.  At that root, the mode is the closed
    metatheoretic numeral and the other three fields are the surrounding
    global-traversal variables. *)
Definition coqFourStateTableAppendRootFieldBindings
    (rootMode : nat) :
    list (TemplateParameterName * TemplateTerm) :=
  coqFourStateTableAppendEqualityFieldBindings
    coqFourStateTableAppendRowModeParameterName
    coqFourStateTableAppendRowFormulaParameterName
    coqFourStateTableAppendRowAssignmentCodeParameterName
    coqFourStateTableAppendRowAssignmentStepParameterName
    (embedPATerm (Term.numeral rootMode))
    (ttVar 0) (ttVar 1) (ttVar 2).

(** In the literal global successor, the eight append code/step witnesses
    are variables [#7..#0] before the five row binders.  After shifting the
    fixed append lookup through those binders and replacing the append bound
    by the row index, its mode projection is exactly the first premise of a
    beta-functionality instance at variables [#12/#11].  Only modes zero and
    one occur in the paired dynamic-truth construction, which lets this
    fixed calculation normalize the embedded mode numeral completely. *)
Lemma
    coqFourStateTableAppendConcreteGlobalModeLookup_matches_beta_first :
  forall rootMode boundName,
  rootMode = 0 \/ rootMode = 1 ->
  templateAnd4First
    (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
      boundName (ttVar 4)
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2)) =
  coqBetaLookupFunctionalityFirstLookupTemplate
    (embedPATerm (Term.numeral rootMode))
    (ttVar 3) (ttVar 12) (ttVar 11) (ttVar 4).
Proof.
  intros rootMode boundName [-> | ->];
    vm_compute;
    repeat rewrite Nat.eqb_refl;
    reflexivity.
Qed.

(** The first projection of the row-side lookup is its mode lookup.  Although
    the historical row template carries four names for the fixed first
    outputs, the second beta premise does not mention any of them.  The
    concrete first output can therefore be the actual root-mode numeral. *)
Lemma
    coqFourStateTableAppendNamedRowModeLookup_matches_concrete_beta_second :
  forall rootMode modeName formulaName assignmentCodeName assignmentStepName,
  rootMode = 0 \/ rootMode = 1 ->
  templateAnd4First
    (coqFourStateTableAppendEqualityRowLookupTemplate
      modeName formulaName assignmentCodeName assignmentStepName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)) =
  coqBetaLookupFunctionalitySecondLookupTemplate
    (embedPATerm (Term.numeral rootMode))
    (ttVar 3) (ttVar 12) (ttVar 11) (ttVar 4).
Proof.
  intros rootMode modeName formulaName
    assignmentCodeName assignmentStepName [-> | ->];
    vm_compute;
    reflexivity.
Qed.

Lemma coqFourStateTableAppendConcreteGlobalLookup_and4_shape : forall
    rootMode boundName,
  rootMode = 0 \/ rootMode = 1 ->
  let source :=
    coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
      boundName (ttVar 4)
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2) in
  source = tfAnd (templateAnd4First source)
    (tfAnd (templateAnd4Second source)
      (tfAnd (templateAnd4Third source) (templateAnd4Fourth source))).
Proof.
  intros rootMode boundName [-> | ->] source;
    vm_compute;
    repeat rewrite Nat.eqb_refl;
    reflexivity.
Qed.

(** Compare only the mode column of the fixed appended lookup and the
    independently quantified row lookup.  Formula and assignment columns do
    not occur in the embedded local production after the scoped-normal-form
    theorem, so compiling their equalities would add witnesses without
    strengthening the result needed by the global successor. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_concrete_global_mode_equality :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode boundName
    baseWitnessList baseContext prefix fixedLookupRoot rowLookupRoot,
  rootMode = 0 \/ rootMode = 1 ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
        boundName (ttVar 4)
        (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
        (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
        (embedPATerm (Term.numeral rootMode))
        (ttVar 0) (ttVar 1) (ttVar 2))) fixedLookupRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityRowLookupTemplate
        coqFourStateTableAppendRowModeParameterName
        coqFourStateTableAppendRowFormulaParameterName
        coqFourStateTableAppendRowAssignmentCodeParameterName
        coqFourStateTableAppendRowAssignmentStepParameterName
        (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0))) rowLookupRoot ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) equalityRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext) prefix)
      (rawTemplateFormula translation
        (tfEq (ttVar 3) (embedPATerm (Term.numeral rootMode))))
      equalityRoot.
Proof.
  intros M hPA translation hagreement rootMode boundName
    baseWitnessList baseContext prefix fixedLookupRoot rowLookupRoot
    hrootMode hprefix hbase hfixedLookup hrowLookup.
  destruct (raw_codedPALocalProofOf_templateAnd4_components
    M hPA translation
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
      boundName (ttVar 4)
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2))
    fixedLookupRoot
    (coqFourStateTableAppendConcreteGlobalLookup_and4_shape
      rootMode boundName hrootMode)
    hfixedLookup)
    as (fixedModeRoot & _ & _ & _ & hfixedMode & _).
  destruct (raw_codedPALocalProofOf_templateAnd4_components
    M hPA translation
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (coqFourStateTableAppendEqualityRowLookupTemplate
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0))
    rowLookupRoot (eq_refl _) hrowLookup)
    as (rowModeRoot & _ & _ & _ & hrowMode & _).
  rewrite (coqFourStateTableAppendConcreteGlobalModeLookup_matches_beta_first
    rootMode boundName hrootMode) in hfixedMode.
  rewrite
    (coqFourStateTableAppendNamedRowModeLookup_matches_concrete_beta_second
      rootMode
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      hrootMode) in hrowMode.
  destruct
    (raw_codedPALocalProofOf_beta_lookup_functionality_on_witnessed_tail_under_prefix
      M hPA translation hagreement
      baseWitnessList baseContext prefix
      (embedPATerm (Term.numeral rootMode)) (ttVar 3)
      (ttVar 12) (ttVar 11) (ttVar 4)
      fixedModeRoot rowModeRoot hprefix hbase hfixedMode hrowMode)
    as (witnesses & equalityRoot & hextended & hequality).
  exists witnesses, equalityRoot.
  split; [exact hextended |].
  rewrite coqBetaLookupFunctionalityEqualityTemplate_eq in hequality.
  exact hequality.
Qed.

(** One-variable motive for transporting the fixed root-mode polarity split
    to the independently quantified row mode.  Shifting the two embedded
    local bodies protects all of their free row/witness variables from the
    distinguished motive variable. *)
Definition coqFourStateTableAppendEmbeddedModeProductionMotive
    (localSigma localPi : formula) : TemplateFormula :=
  tfOr
    (tfAnd (tfEq (ttVar 0) ttZero)
      (templateFormulaRename S (embedPAFormula localSigma)))
    (tfAnd (tfEq (ttVar 0) (ttSucc ttZero))
      (templateFormulaRename S (embedPAFormula localPi))).

Lemma coqFourStateTableAppendEmbeddedModeProductionMotive_open : forall
    localSigma localPi replacement,
  templateFormulaOpen replacement
    (coqFourStateTableAppendEmbeddedModeProductionMotive
      localSigma localPi) =
  tfOr
    (tfAnd (tfEq replacement ttZero) (embedPAFormula localSigma))
    (tfAnd (tfEq replacement (ttSucc ttZero))
      (embedPAFormula localPi)).
Proof.
  intros localSigma localPi replacement.
  unfold coqFourStateTableAppendEmbeddedModeProductionMotive.
  change
    (tfOr
      (tfAnd (tfEq replacement ttZero)
        (templateFormulaOpen replacement
          (templateFormulaRename S (embedPAFormula localSigma))))
      (tfAnd (tfEq replacement (ttSucc ttZero))
        (templateFormulaOpen replacement
          (templateFormulaRename S (embedPAFormula localPi)))) =
     tfOr
      (tfAnd (tfEq replacement ttZero) (embedPAFormula localSigma))
      (tfAnd (tfEq replacement (ttSucc ttZero))
        (embedPAFormula localPi))).
  now rewrite !templateFormulaOpen_rename_succ.
Qed.

Lemma coqFourStateTableAppendEmbeddedModeProductionMotive_open_row : forall
    localSigma localPi,
  templateFormulaOpen (ttVar 3)
    (coqFourStateTableAppendEmbeddedModeProductionMotive
      localSigma localPi) =
  coqFourStateTableAppendConcreteClosedRowProductionTemplate
    (embedPAFormula localSigma) (embedPAFormula localPi).
Proof.
  intros localSigma localPi.
  rewrite coqFourStateTableAppendEmbeddedModeProductionMotive_open.
  symmetry.
  apply
    coqFourStateTableAppendConcreteClosedRowProductionTemplate_embedded_shape.
Qed.

(** Transport a fixed root-mode production across the represented equality
    produced by the preceding beta-functionality compiler.  The target is
    the exact concrete production consumed by the existing row case split. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_concrete_production_of_mode_equality :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context rootMode localSigma localPi equalityRoot fixedProductionRoot,
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (tfEq (ttVar 3) (embedPATerm (Term.numeral rootMode))))
    equalityRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
        (coqFourStateTableAppendEmbeddedModeProductionMotive
          localSigma localPi))) fixedProductionRoot ->
  exists productionRoot,
    RawCodedPALocalProofOf M context
      (rawTemplateFormula translation
        (coqFourStateTableAppendConcreteClosedRowProductionTemplate
          (embedPAFormula localSigma) (embedPAFormula localPi)))
      productionRoot.
Proof.
  intros M hPA translation context rootMode localSigma localPi
    equalityRoot fixedProductionRoot hequality hfixedProduction.
  destruct (raw_codedPALocalProofOf_templateEqTransport_reverse
    M hPA translation context
    (ttVar 3) (embedPATerm (Term.numeral rootMode))
    (coqFourStateTableAppendEmbeddedModeProductionMotive
      localSigma localPi)
    equalityRoot fixedProductionRoot hequality hfixedProduction)
    as [productionRoot hproduction].
  exists productionRoot.
  rewrite coqFourStateTableAppendEmbeddedModeProductionMotive_open_row
    in hproduction.
  exact hproduction.
Qed.

(** End-to-end equality-branch production over an arbitrary concrete row
    prefix.  Beta functionality may select a finite PA theorem batch; the
    fixed root-mode production is transported to that exact enlarged tail
    before the represented mode equality is consumed. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_four_state_table_append_concrete_global_equality_production :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode boundName localSigma localPi
    baseWitnessList baseContext prefix
    fixedLookupRoot rowLookupRoot fixedProductionRoot,
  rootMode = 0 \/ rootMode = 1 ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
        boundName (ttVar 4)
        (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
        (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
        (embedPATerm (Term.numeral rootMode))
        (ttVar 0) (ttVar 1) (ttVar 2))) fixedLookupRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityRowLookupTemplate
        coqFourStateTableAppendRowModeParameterName
        coqFourStateTableAppendRowFormulaParameterName
        coqFourStateTableAppendRowAssignmentCodeParameterName
        coqFourStateTableAppendRowAssignmentStepParameterName
        (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0))) rowLookupRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext prefix)
    (rawTemplateFormula translation
      (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
        (coqFourStateTableAppendEmbeddedModeProductionMotive
          localSigma localPi))) fixedProductionRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    baseWitnessList baseContext prefix
    (rawTemplateFormula translation
      (coqFourStateTableAppendConcreteClosedRowProductionTemplate
        (embedPAFormula localSigma) (embedPAFormula localPi))).
Proof.
  intros M hPA translation hagreement
    rootMode boundName localSigma localPi
    baseWitnessList baseContext prefix
    fixedLookupRoot rowLookupRoot fixedProductionRoot
    hrootMode hprefix hbase hfixedLookup hrowLookup hfixedProduction.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_concrete_global_mode_equality
      M hPA translation hagreement rootMode boundName
      baseWitnessList baseContext prefix fixedLookupRoot rowLookupRoot
      hrootMode hprefix hbase hfixedLookup hrowLookup)
    as (witnesses & equalityRoot & hextended & hequality).
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses baseWitnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses baseContext).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext extendedWitnessList extendedContext
      prefix
      (rawTemplateFormula translation
        (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            localSigma localPi)))
      fixedProductionRoot hbase hextended
      (raw_standardPAAxiomWitnessPrefixContextCode_target_included
        M hPA witnesses baseContext)
      hfixedProduction)
    as [transportedFixedProductionRoot htransportedFixedProduction].
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_concrete_production_of_mode_equality
      M hPA translation
      (rawTemplateContextCodeOnTail translation extendedContext prefix)
      rootMode localSigma localPi equalityRoot
      transportedFixedProductionRoot hequality
      htransportedFixedProduction)
    as [productionRoot hproduction].
  unfold RawCodedPAGrowingTemplateLocalProofAt.
  exists extendedWitnessList, extendedContext, productionRoot.
  split; [exact hextended |].
  split.
  - exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA witnesses baseContext).
  - exact hproduction.
Qed.

(** The three roots needed by the concrete equality branch, all in one
    dependency-ordered context: the fixed appended mode lookup, the row-side
    lookup assumption, and the production at the fixed root mode. *)
Definition RawFourStateTableAppendConcreteGlobalEqualityInputsAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (context : M) (prefix : TemplateContext)
    (rootMode : nat) (boundName : TemplateParameterName)
    (localSigma localPi : formula) : Prop :=
  exists fixedLookupRoot rowLookupRoot fixedProductionRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation context prefix)
      (rawTemplateFormula translation
        (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
          boundName (ttVar 4)
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 0) (ttVar 1) (ttVar 2))) fixedLookupRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation context prefix)
      (rawTemplateFormula translation
        (coqFourStateTableAppendEqualityRowLookupTemplate
          coqFourStateTableAppendRowModeParameterName
          coqFourStateTableAppendRowFormulaParameterName
          coqFourStateTableAppendRowAssignmentCodeParameterName
          coqFourStateTableAppendRowAssignmentStepParameterName
          (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)))
      rowLookupRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation context prefix)
      (rawTemplateFormula translation
        (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            localSigma localPi))) fixedProductionRoot.

Arguments RawFourStateTableAppendConcreteGlobalEqualityInputsAt
  M translation context prefix rootMode boundName localSigma localPi
  : clear implicits.

(** Transport the complete equality package to any dependency-ordered
    witnessed-tail extension while preserving its finite template prefix. *)
Theorem raw_fourStateTableAppendConcreteGlobalEqualityInputsAt_transport :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    baseWitnessList baseContext sourceWitnessList sourceContext prefix
    rootMode boundName localSigma localPi,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawContextListIncluded M baseContext sourceContext ->
  RawFourStateTableAppendConcreteGlobalEqualityInputsAt
    M translation baseContext prefix
    rootMode boundName localSigma localPi ->
  RawFourStateTableAppendConcreteGlobalEqualityInputsAt
    M translation sourceContext prefix
    rootMode boundName localSigma localPi.
Proof.
  intros M hPA translation
    baseWitnessList baseContext sourceWitnessList sourceContext prefix
    rootMode boundName localSigma localPi
    hbase hsource hincluded
    (fixedLookupRoot & rowLookupRoot & fixedProductionRoot &
      hfixedLookup & hrowLookup & hfixedProduction).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext sourceWitnessList sourceContext prefix
      (rawTemplateFormula translation
        (coqFourStateTableAppendEqualityTransportedNewStateLookupTemplate
          boundName (ttVar 4)
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 0) (ttVar 1) (ttVar 2)))
      fixedLookupRoot hbase hsource hincluded hfixedLookup)
    as [transportedFixedLookupRoot htransportedFixedLookup].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext sourceWitnessList sourceContext prefix
      (rawTemplateFormula translation
        (coqFourStateTableAppendEqualityRowLookupTemplate
          coqFourStateTableAppendRowModeParameterName
          coqFourStateTableAppendRowFormulaParameterName
          coqFourStateTableAppendRowAssignmentCodeParameterName
          coqFourStateTableAppendRowAssignmentStepParameterName
          (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)))
      rowLookupRoot hbase hsource hincluded hrowLookup)
    as [transportedRowLookupRoot htransportedRowLookup].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      baseWitnessList baseContext sourceWitnessList sourceContext prefix
      (rawTemplateFormula translation
        (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            localSigma localPi)))
      fixedProductionRoot hbase hsource hincluded hfixedProduction)
    as [transportedFixedProductionRoot htransportedFixedProduction].
  exists transportedFixedLookupRoot, transportedRowLookupRoot,
    transportedFixedProductionRoot.
  split; [exact htransportedFixedLookup |].
  split; [exact htransportedRowLookup |].
  exact htransportedFixedProduction.
Qed.

(** Assemble the concrete global equality inputs below an arbitrary finite
    prefix.  Unlike the older named-row assembler, the fixed append lookup
    is instantiated with the literal global variables and root mode.  The
    row lookup and fixed-mode production are caller roots in the combined
    context; both are weakened once beneath the equality branch head. *)
Theorem
    raw_fourStateTableAppendConcreteGlobalEqualityInputsAt_on_witnessed_row_context_under_prefix_of_local_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode boundName localSigma localPi witnesses
    extraPrefix rowBound rowLookupRoot fixedProductionRoot,
  let baseContext := rawStandardPAAxiomWitnessPrefixContextCode M
    witnesses (raw_zero M) in
  let rowPrefix := coqFourStateTableAppendRowPrefix
    (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
    (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
    (ttParameter boundName)
    (embedPATerm (Term.numeral rootMode))
    (ttVar 0) (ttVar 1) (ttVar 2) in
  let equalityHead :=
    coqLtSuccCasesEqualTemplate (ttVar 4) rowBound in
  let fixedProduction :=
    templateFormulaOpen (embedPATerm (Term.numeral rootMode))
      (coqFourStateTableAppendEmbeddedModeProductionMotive
        localSigma localPi) in
  RawCodedTemplatePrefixAtomicallyAdequate M translation extraPrefix ->
  equalityHead = tfEq (ttVar 4) (ttParameter boundName) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation equalityHead) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
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
    (rawTemplateContextCodeOnTail translation baseContext
      (extraPrefix ++ rowPrefix))
    (rawTemplateFormula translation fixedProduction) fixedProductionRoot ->
  RawFourStateTableAppendConcreteGlobalEqualityInputsAt
    M translation baseContext (equalityHead :: extraPrefix ++ rowPrefix)
    rootMode boundName localSigma localPi.
Proof.
  intros M hPA translation hagreement
    rootMode boundName localSigma localPi witnesses
    extraPrefix rowBound rowLookupRoot fixedProductionRoot
    baseContext rowPrefix equalityHead fixedProduction
    hextraPrefix hequalityHead hhead hrowLookup hfixedProduction.
  cbn zeta in *.
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_equality_branch_lookup_parameter_under_prefix
      M hPA translation
      (embedPAContext (map witnessedAxiom witnesses)) extraPrefix
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      boundName (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2)
      (ttVar 4) rowBound hextraPrefix hequalityHead hhead)
    as [fixedLookupRoot hfixedLookup].
  rewrite
    (raw_fourStateTableAppendRowContext_witnessed_tail_code
      M translation hagreement
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      (ttParameter boundName)
      (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2) witnesses)
    in hfixedLookup.
  rewrite <- (rawTemplateContextCodeOnTail_app M translation
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) extraPrefix
    (coqFourStateTableAppendRowPrefix
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      (ttParameter boundName)
      (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2))) in hfixedLookup.
  assert (hbase : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement witnesses) as hbaseTemplate.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hbaseTemplate.
    exact hbaseTemplate.
  }
  assert (hcombinedContext : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        (extraPrefix ++
          coqFourStateTableAppendRowPrefix
            (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
            (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
            (ttParameter boundName)
            (embedPATerm (Term.numeral rootMode))
            (ttVar 0) (ttVar 1) (ttVar 2)))).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) hbase).
  }
  assert (hequalityPrefix :
      RawCodedTemplatePrefixAtomicallyAdequate M translation [equalityHead]).
  {
    intros input [hinput | hinput].
    - subst input. exact hhead.
    - contradiction.
  }
  destruct (raw_codedPALocalProof_templatePrefix
    M hPA translation
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (extraPrefix ++
        coqFourStateTableAppendRowPrefix
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter boundName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 0) (ttVar 1) (ttVar 2)))
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
  destruct (raw_codedPALocalProof_templatePrefix
    M hPA translation
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (extraPrefix ++
        coqFourStateTableAppendRowPrefix
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter boundName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 0) (ttVar 1) (ttVar 2)))
    [equalityHead]
    (rawTemplateFormula translation
      (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
        (coqFourStateTableAppendEmbeddedModeProductionMotive
          localSigma localPi)))
    fixedProductionRoot hcombinedContext hequalityPrefix hfixedProduction)
    as [shiftedFixedProductionRoot hshiftedFixedProduction].
  unfold RawFourStateTableAppendConcreteGlobalEqualityInputsAt.
  exists fixedLookupRoot, shiftedRowLookupRoot,
    shiftedFixedProductionRoot.
  cbn in hfixedLookup, hshiftedRowLookup,
    hshiftedFixedProduction |- *.
  split; [exact hfixedLookup |].
  split; [exact hshiftedRowLookup | exact hshiftedFixedProduction].
Qed.

(** Run the predecessor/equality split in the literal global row context.
    The predecessor branch only needs the inherited traversal and old lookup;
    the equality branch consumes the concrete three-root package above.  No
    named row-field freshness hypotheses survive this specialization. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_concrete_global_closed_row_of_inherited_local_roots_under_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode boundName localSigma localPi witnesses
    extraPrefix rowBound inheritedTraversal oldLookup
    antecedentRoot rowLookupRoot fixedProductionRoot,
  let baseWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M) in
  let baseContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M) in
  let rowPrefix := coqFourStateTableAppendRowPrefix
    (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
    (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
    (ttParameter boundName)
    (embedPATerm (Term.numeral rootMode))
    (ttVar 0) (ttVar 1) (ttVar 2) in
  let combinedPrefix := extraPrefix ++ rowPrefix in
  let below := coqLtSuccCasesBelowTemplate (ttVar 4) rowBound in
  let equalityHead := coqLtSuccCasesEqualTemplate (ttVar 4) rowBound in
  let fixedProduction :=
    templateFormulaOpen (embedPATerm (Term.numeral rootMode))
      (coqFourStateTableAppendEmbeddedModeProductionMotive
        localSigma localPi) in
  let result := coqFourStateTableAppendConcreteClosedRowProductionTemplate
    (embedPAFormula localSigma) (embedPAFormula localPi) in
  rootMode = 0 \/ rootMode = 1 ->
  templateUniversalOpenMany inheritedTraversal
    coqFourStateTableAppendConcreteRowVariables =
    Some (tfImp below (tfImp oldLookup result)) ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation combinedPrefix ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation below) ->
  equalityHead = tfEq (ttVar 4) (ttParameter boundName) ->
  RawCodedFormulaAtomicallyAdequate M
    (rawTemplateFormula translation equalityHead) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext combinedPrefix)
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate (ttVar 4) rowBound))
    antecedentRoot ->
  RawFourStateTableAppendInheritedLocalRootsAt M translation
    baseContext combinedPrefix inheritedTraversal oldLookup ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext combinedPrefix)
    (rawTemplateFormula translation
      (coqFourStateTableAppendEqualityRowLookupTemplate
        coqFourStateTableAppendRowModeParameterName
        coqFourStateTableAppendRowFormulaParameterName
        coqFourStateTableAppendRowAssignmentCodeParameterName
        coqFourStateTableAppendRowAssignmentStepParameterName
        (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)))
    rowLookupRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext combinedPrefix)
    (rawTemplateFormula translation fixedProduction) fixedProductionRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    baseWitnessList baseContext combinedPrefix
    (rawTemplateFormula translation result).
Proof.
  intros M hPA translation hagreement
    rootMode boundName localSigma localPi witnesses
    extraPrefix rowBound inheritedTraversal oldLookup
    antecedentRoot rowLookupRoot fixedProductionRoot
    baseWitnessList baseContext rowPrefix combinedPrefix below
    equalityHead fixedProduction result
    hrootMode hopen hprefix hbelowAdequate hequalityHead
    hequalityAdequate hantecedent hinheritedRoots hrowLookup
    hfixedProduction.
  cbn zeta in *.
  assert (hbase : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement witnesses) as hbaseTemplate.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hbaseTemplate.
    exact hbaseTemplate.
  }
  assert (hextraPrefix :
      RawCodedTemplatePrefixAtomicallyAdequate M translation extraPrefix).
  {
    intros input hinput.
    apply hprefix. apply in_or_app. left. exact hinput.
  }
  pose proof
    (raw_fourStateTableAppendConcreteGlobalEqualityInputsAt_on_witnessed_row_context_under_prefix_of_local_roots
      M hPA translation hagreement
      rootMode boundName localSigma localPi witnesses
      extraPrefix rowBound rowLookupRoot fixedProductionRoot
      hextraPrefix hequalityHead hequalityAdequate
      hrowLookup hfixedProduction)
    as hequalityBaseInputs.
  assert (hequalityBranchPrefix :
      RawCodedTemplatePrefixAtomicallyAdequate M translation
        (equalityHead :: extraPrefix ++
          coqFourStateTableAppendRowPrefix
            (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
            (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
            (ttParameter boundName)
            (embedPATerm (Term.numeral rootMode))
            (ttVar 0) (ttVar 1) (ttVar 2))).
  {
    intros input [hinput | hinput].
    - subst input. exact hequalityAdequate.
    - exact (hprefix input hinput).
  }
  eapply
    (raw_codedPALocalProofOf_lt_succ_cases_eliminate_on_base_included_growing_witnessed_tail_under_prefix
      M hPA translation hagreement
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (extraPrefix ++ coqFourStateTableAppendRowPrefix
        (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
        (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
        (ttParameter boundName)
        (embedPATerm (Term.numeral rootMode))
        (ttVar 0) (ttVar 1) (ttVar 2))
      (ttVar 4) rowBound antecedentRoot
      (rawTemplateFormula translation
        (coqFourStateTableAppendConcreteClosedRowProductionTemplate
          (embedPAFormula localSigma) (embedPAFormula localPi)))).
  - exact hprefix.
  - exact hbase.
  - exact hantecedent.
  - intros sourceWitnessList sourceContext hsource hbaseIncluded.
    pose proof
      (raw_fourStateTableAppendInheritedLocalRootsAt_transport
        M hPA translation
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          witnesses (raw_zero M))
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        sourceWitnessList sourceContext
        (extraPrefix ++ coqFourStateTableAppendRowPrefix
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter boundName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 0) (ttVar 1) (ttVar 2))
        inheritedTraversal oldLookup
        hbase hsource hbaseIncluded hinheritedRoots)
      as hsourceInheritedRoots.
    pose proof
      (raw_fourStateTableAppendInheritedProductionInputsAt_of_local_root_package
        M hPA translation sourceWitnessList sourceContext
        (extraPrefix ++ coqFourStateTableAppendRowPrefix
          (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
          (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
          (ttParameter boundName)
          (embedPATerm (Term.numeral rootMode))
          (ttVar 0) (ttVar 1) (ttVar 2))
        inheritedTraversal
        (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound)
        oldLookup hsource hbelowAdequate hsourceInheritedRoots)
      as hpredecessorInputs.
    exact
      (raw_codedPALocalProofOf_four_state_table_append_inherited_row_production_growing_tail
        M hPA translation sourceWitnessList sourceContext
        (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound ::
          extraPrefix ++ coqFourStateTableAppendRowPrefix
            (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
            (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
            (ttParameter boundName)
            (embedPATerm (Term.numeral rootMode))
            (ttVar 0) (ttVar 1) (ttVar 2))
        inheritedTraversal
        (coqLtSuccCasesBelowTemplate (ttVar 4) rowBound)
        oldLookup
        (coqFourStateTableAppendConcreteClosedRowProductionTemplate
          (embedPAFormula localSigma) (embedPAFormula localPi))
        hsource hopen hpredecessorInputs).
  - intros sourceWitnessList sourceContext hsource hbaseIncluded.
    pose proof
      (raw_fourStateTableAppendConcreteGlobalEqualityInputsAt_transport
        M hPA translation
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          witnesses (raw_zero M))
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        sourceWitnessList sourceContext
        (coqLtSuccCasesEqualTemplate (ttVar 4) rowBound ::
          extraPrefix ++ coqFourStateTableAppendRowPrefix
            (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
            (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
            (ttParameter boundName)
            (embedPATerm (Term.numeral rootMode))
            (ttVar 0) (ttVar 1) (ttVar 2))
        rootMode boundName localSigma localPi
        hbase hsource hbaseIncluded hequalityBaseInputs)
      as hsourceEqualityInputs.
    destruct hsourceEqualityInputs as
      (fixedLookupRoot & sourceRowLookupRoot & sourceFixedProductionRoot &
        hfixedLookup & hsourceRowLookup & hsourceFixedProduction).
    exact
      (raw_codedPAGrowingTemplateLocalProofAt_four_state_table_append_concrete_global_equality_production
        M hPA translation hagreement rootMode boundName localSigma localPi
        sourceWitnessList sourceContext
        (coqLtSuccCasesEqualTemplate (ttVar 4) rowBound ::
          extraPrefix ++ coqFourStateTableAppendRowPrefix
            (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
            (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
            (ttParameter boundName)
            (embedPATerm (Term.numeral rootMode))
            (ttVar 0) (ttVar 1) (ttVar 2))
        fixedLookupRoot sourceRowLookupRoot sourceFixedProductionRoot
        hrootMode hequalityBranchPrefix hsource
        hfixedLookup hsourceRowLookup hsourceFixedProduction).
Qed.

(** Discharge two represented assumptions from a growing local proof without
    changing its selected witness extension.  The list order is the proof
    order: [second] is the current context head and is introduced first. *)
Theorem raw_codedPAGrowingTemplateLocalProofAt_impI_two : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext prefix first second conclusion,
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext (second :: first :: prefix)
    (rawTemplateFormula translation conclusion) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext prefix
    (rawTemplateFormula translation
      (tfImp first (tfImp second conclusion))).
Proof.
  intros M hPA translation sourceWitnessList sourceContext
    prefix first second conclusion
    (targetWitnessList & targetContext & conclusionRoot &
      htarget & hincluded & hconclusion).
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawTemplateContextCodeOnTail translation targetContext
      (first :: prefix))
    (rawTemplateFormula translation second)
    (rawTemplateFormula translation conclusion)
    conclusionRoot hconclusion) as hsecond.
  rewrite <- rawTemplateFormula_imp in hsecond.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawTemplateContextCodeOnTail translation targetContext prefix)
    (rawTemplateFormula translation first)
    (rawTemplateFormula translation (tfImp second conclusion))
    (rawProofImpIRoot M
      (rawTemplateContextCodeOnTail translation targetContext
        (first :: prefix))
      (rawTemplateFormula translation second)
      (rawTemplateFormula translation conclusion) conclusionRoot)
    hsecond) as hfirst.
  rewrite <- rawTemplateFormula_imp in hfirst.
  unfold RawCodedPAGrowingTemplateLocalProofAt.
  exists targetWitnessList, targetContext.
  eexists.
  split; [exact htarget |].
  split; [exact hincluded | exact hfirst].
Qed.

(** Instantiate the concrete row compiler with its two literal premises,
    build both as represented assumption leaves, and discharge them with the
    generic two-assumption growing-proof lemma. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_concrete_global_closed_row_implications_on_witnessed_row_context :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode boundName localSigma localPi witnesses rowBound
    inheritedTraversal oldLookup fixedProductionRoot,
  let baseWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M) in
  let baseContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M) in
  let rowPrefix := coqFourStateTableAppendRowPrefix
    (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
    (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
    (ttParameter boundName)
    (embedPATerm (Term.numeral rootMode))
    (ttVar 0) (ttVar 1) (ttVar 2) in
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
  let fixedProduction :=
    templateFormulaOpen (embedPATerm (Term.numeral rootMode))
      (coqFourStateTableAppendEmbeddedModeProductionMotive
        localSigma localPi) in
  let result := coqFourStateTableAppendConcreteClosedRowProductionTemplate
    (embedPAFormula localSigma) (embedPAFormula localPi) in
  rootMode = 0 \/ rootMode = 1 ->
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
  RawFourStateTableAppendInheritedLocalRootsAt M translation
    baseContext rowPrefix inheritedTraversal oldLookup ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext rowPrefix)
    (rawTemplateFormula translation fixedProduction) fixedProductionRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    baseWitnessList baseContext rowPrefix
    (rawTemplateFormula translation
      (tfImp antecedent (tfImp rowLookup result))).
Proof.
  intros M hPA translation hagreement
    rootMode boundName localSigma localPi witnesses rowBound
    inheritedTraversal oldLookup fixedProductionRoot
    baseWitnessList baseContext rowPrefix antecedent rowLookup below
    equalityHead fixedProduction result
    hrootMode hopen hrowPrefix hantecedentAdequate hrowLookupAdequate
    hbelowAdequate hequalityHead hequalityAdequate
    hinheritedRoots hfixedProduction.
  cbn zeta in *.
  assert (hbase : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement witnesses) as hbaseTemplate.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hbaseTemplate.
    exact hbaseTemplate.
  }
  set (actualRowPrefix := coqFourStateTableAppendRowPrefix
    (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
    (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
    (ttParameter boundName)
    (embedPATerm (Term.numeral rootMode))
    (ttVar 0) (ttVar 1) (ttVar 2)).
  set (actualAntecedent :=
    coqLtSuccCasesAntecedentTemplate (ttVar 4) rowBound).
  set (actualRowLookup :=
    coqFourStateTableAppendEqualityRowLookupTemplate
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)).
  set (actualFixedProduction :=
    templateFormulaOpen (embedPATerm (Term.numeral rootMode))
      (coqFourStateTableAppendEmbeddedModeProductionMotive
        localSigma localPi)).
  set (actualResult :=
    coqFourStateTableAppendConcreteClosedRowProductionTemplate
      (embedPAFormula localSigma) (embedPAFormula localPi)).
  set (extraPrefix := [actualRowLookup; actualAntecedent]).
  assert (hextraPrefix :
      RawCodedTemplatePrefixAtomicallyAdequate M translation extraPrefix).
  {
    intros input [hinput | [hinput | hinput]].
    - subst input. exact hrowLookupAdequate.
    - subst input. exact hantecedentAdequate.
    - contradiction.
  }
  assert (hcombinedPrefix :
      RawCodedTemplatePrefixAtomicallyAdequate M translation
        (extraPrefix ++ actualRowPrefix)).
  {
    intros input hinput.
    apply in_app_or in hinput.
    destruct hinput as [hinput | hinput].
    - exact (hextraPrefix input hinput).
    - exact (hrowPrefix input hinput).
  }
  assert (hrowContext : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M)) actualRowPrefix)).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) hbase).
  }
  destruct hinheritedRoots as
    (traversalRoot & oldLookupRoot & htraversal & holdLookup).
  destruct (raw_codedPALocalProof_templatePrefix
    M hPA translation
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) actualRowPrefix)
    extraPrefix (rawTemplateFormula translation inheritedTraversal)
    traversalRoot hrowContext hextraPrefix htraversal)
    as [prefixedTraversalRoot hprefixedTraversal].
  destruct (raw_codedPALocalProof_templatePrefix
    M hPA translation
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) actualRowPrefix)
    extraPrefix (rawTemplateFormula translation oldLookup)
    oldLookupRoot hrowContext hextraPrefix holdLookup)
    as [prefixedOldLookupRoot hprefixedOldLookup].
  destruct (raw_codedPALocalProof_templatePrefix
    M hPA translation
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) actualRowPrefix)
    extraPrefix (rawTemplateFormula translation actualFixedProduction)
    fixedProductionRoot hrowContext hextraPrefix hfixedProduction)
    as [prefixedFixedProductionRoot hprefixedFixedProduction].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) actualRowPrefix)
    (rawTemplateFormula translation actualAntecedent)
    hrowContext) as hantecedentHead.
  assert (hrowLookupSingleton :
      RawCodedTemplatePrefixAtomicallyAdequate M translation
        [actualRowLookup]).
  {
    intros input [hinput | hinput].
    - subst input. exact hrowLookupAdequate.
    - contradiction.
  }
  assert (hantecedentContext : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        (actualAntecedent :: actualRowPrefix))).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) hbase).
  }
  destruct (raw_codedPALocalProof_templatePrefix
    M hPA translation
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (actualAntecedent :: actualRowPrefix))
    [actualRowLookup]
    (rawTemplateFormula translation actualAntecedent)
    (rawProofAssumptionRoot M
      (rawListNode M (rawTemplateFormula translation actualAntecedent)
        (rawTemplateContextCodeOnTail translation
          (rawStandardPAAxiomWitnessPrefixContextCode M
            witnesses (raw_zero M)) actualRowPrefix))
      (rawTemplateFormula translation actualAntecedent))
    hantecedentContext hrowLookupSingleton hantecedentHead)
    as [antecedentRoot hantecedent].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (actualAntecedent :: actualRowPrefix))
    (rawTemplateFormula translation actualRowLookup)
    hantecedentContext) as hrowLookup.
  pose proof
    (raw_codedPALocalProofOf_four_state_table_append_concrete_global_closed_row_of_inherited_local_roots_under_prefix
      M hPA translation hagreement
      rootMode boundName localSigma localPi witnesses
      extraPrefix rowBound inheritedTraversal oldLookup
      antecedentRoot
      (rawProofAssumptionRoot M
        (rawListNode M (rawTemplateFormula translation actualRowLookup)
          (rawTemplateContextCodeOnTail translation
            (rawStandardPAAxiomWitnessPrefixContextCode M
              witnesses (raw_zero M))
            (actualAntecedent :: actualRowPrefix)))
        (rawTemplateFormula translation actualRowLookup))
      prefixedFixedProductionRoot
      hrootMode hopen hcombinedPrefix hbelowAdequate
      hequalityHead hequalityAdequate hantecedent
      (ex_intro _ prefixedTraversalRoot
        (ex_intro _ prefixedOldLookupRoot
          (conj hprefixedTraversal hprefixedOldLookup)))
      hrowLookup hprefixedFixedProduction) as hresult.
  exact (raw_codedPAGrowingTemplateLocalProofAt_impI_two
    M hPA translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    actualRowPrefix actualAntecedent actualRowLookup actualResult hresult).
Qed.

(** Public concrete-row interface with all atomic-adequacy obligations
    discharged from the generic translation contract. *)
Corollary
    raw_codedPALocalProofOf_four_state_table_append_concrete_global_closed_row_implications :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode boundName localSigma localPi witnesses
    inheritedTraversal oldLookup fixedProductionRoot,
  let baseWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M) in
  let baseContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M) in
  let rowPrefix := coqFourStateTableAppendRowPrefix
    (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
    (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
    (ttParameter boundName)
    (embedPATerm (Term.numeral rootMode))
    (ttVar 0) (ttVar 1) (ttVar 2) in
  let antecedent := coqLtSuccCasesAntecedentTemplate
    (ttVar 4) (ttParameter boundName) in
  let rowLookup :=
    coqFourStateTableAppendEqualityRowLookupTemplate
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0) in
  let below := coqLtSuccCasesBelowTemplate
    (ttVar 4) (ttParameter boundName) in
  let fixedProduction :=
    templateFormulaOpen (embedPATerm (Term.numeral rootMode))
      (coqFourStateTableAppendEmbeddedModeProductionMotive
        localSigma localPi) in
  let result := coqFourStateTableAppendConcreteClosedRowProductionTemplate
    (embedPAFormula localSigma) (embedPAFormula localPi) in
  rootMode = 0 \/ rootMode = 1 ->
  templateUniversalOpenMany inheritedTraversal
    coqFourStateTableAppendConcreteRowVariables =
    Some (tfImp below (tfImp oldLookup result)) ->
  RawFourStateTableAppendInheritedLocalRootsAt M translation
    baseContext rowPrefix inheritedTraversal oldLookup ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext rowPrefix)
    (rawTemplateFormula translation fixedProduction) fixedProductionRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    baseWitnessList baseContext rowPrefix
    (rawTemplateFormula translation
      (tfImp antecedent (tfImp rowLookup result))).
Proof.
  intros M hPA translation hagreement
    rootMode boundName localSigma localPi witnesses
    inheritedTraversal oldLookup fixedProductionRoot
    baseWitnessList baseContext rowPrefix antecedent rowLookup below
    fixedProduction result hrootMode hopen hinheritedRoots
    hfixedProduction.
  cbn zeta in *.
  exact
    (raw_codedPALocalProofOf_four_state_table_append_concrete_global_closed_row_implications_on_witnessed_row_context
      M hPA translation hagreement
      rootMode boundName localSigma localPi witnesses
      (ttParameter boundName) inheritedTraversal oldLookup
      fixedProductionRoot hrootMode hopen
      (raw_codedTemplatePrefix_atomically_adequate M hPA translation _)
      (raw_codedTemplateFormula_atomically_adequate M hPA translation _)
      (raw_codedTemplateFormula_atomically_adequate M hPA translation _)
      (raw_codedTemplateFormula_atomically_adequate M hPA translation _)
      eq_refl
      (raw_codedTemplateFormula_atomically_adequate M hPA translation _)
      hinheritedRoots hfixedProduction).
Qed.

(** Pointwise equality of translated context entries is enough to identify
    their folds over every raw tail.  This formulation avoids requiring the
    template syntax itself to be equal: named carrier parameters and concrete
    de Bruijn terms may translate to the same raw code. *)
Lemma rawTemplateContextCodeOnTail_Forall2_eq : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    source target,
  Forall2
    (fun sourceFormula targetFormula =>
      rawTemplateFormula translation sourceFormula =
      rawTemplateFormula translation targetFormula)
    source target ->
  forall tail,
    rawTemplateContextCodeOnTail translation tail source =
    rawTemplateContextCodeOnTail translation tail target.
Proof.
  intros M translation source target hequal.
  induction hequal; intro tail; cbn [rawTemplateContextCodeOnTail].
  - reflexivity.
  - now rewrite H, IHhequal.
Qed.

(** Re-identify the finite temporary prefix of a growing local proof while
    retaining its chosen target witness list, target context, inclusion
    certificate, conclusion, and proof root. *)
Lemma raw_codedPAGrowingTemplateLocalProofAt_prefix_code_eq : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext sourcePrefix targetPrefix conclusion,
  (forall tail,
    rawTemplateContextCodeOnTail translation tail sourcePrefix =
    rawTemplateContextCodeOnTail translation tail targetPrefix) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext sourcePrefix conclusion ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext targetPrefix conclusion.
Proof.
  intros M translation sourceWitnessList sourceContext
    sourcePrefix targetPrefix conclusion hprefix hproof.
  destruct hproof as
    (targetWitnessList & targetContext & root &
      hwitness & hincluded & hroot).
  exists targetWitnessList, targetContext, root.
  split; [exact hwitness |].
  split; [exact hincluded |].
  rewrite <- (hprefix targetContext).
  exact hroot.
Qed.

(** Simultaneous prefix/conclusion congruence, convenient at syntax
    normalization boundaries. *)
Corollary
    raw_codedPAGrowingTemplateLocalProofAt_prefix_and_conclusion_code_eq :
  forall (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext sourcePrefix targetPrefix
    sourceConclusion targetConclusion,
  (forall tail,
    rawTemplateContextCodeOnTail translation tail sourcePrefix =
    rawTemplateContextCodeOnTail translation tail targetPrefix) ->
  sourceConclusion = targetConclusion ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext sourcePrefix sourceConclusion ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext targetPrefix targetConclusion.
Proof.
  intros M translation sourceWitnessList sourceContext
    sourcePrefix targetPrefix sourceConclusion targetConclusion
    hprefix <- hproof.
  exact (raw_codedPAGrowingTemplateLocalProofAt_prefix_code_eq
    M translation sourceWitnessList sourceContext
    sourcePrefix targetPrefix sourceConclusion hprefix hproof).
Qed.

(** Convert the completed concrete row implication into the exact extracted
    seventh field.  The only client-specific obligation is the final
    production equality; all five binders and both implication premises are
    handled here.  This keeps local Sigma/Pi normalization independent of the
    growing-context proof machinery. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_opened_global_rows_of_concrete_row :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses sigmaProduction piProduction,
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
  let rowPrefix := coqFourStateTableAppendRowPrefix
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep in
  let antecedent := coqLtSuccCasesAntecedentTemplate (ttVar 4) bound in
  let rowLookup :=
    coqFourStateTableAppendEqualityRowLookupTemplate
      coqFourStateTableAppendRowModeParameterName
      coqFourStateTableAppendRowFormulaParameterName
      coqFourStateTableAppendRowAssignmentCodeParameterName
      coqFourStateTableAppendRowAssignmentStepParameterName
      (ttVar 4) (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0) in
  let concreteProduction :=
    coqFourStateTableAppendConcreteClosedRowProductionTemplate
      sigmaProduction piProduction in
  concreteProduction =
    coqFourStateTableAppendOpenedGlobalRowProductionTemplate
      rootMode localSigma localPi bound ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext rowPrefix
    (rawTemplateFormula translation
      (tfImp antecedent (tfImp rowLookup concreteProduction))) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep [])
    (rawTemplateFormula translation
      (coqFourStateTableAppendOpenedGlobalRowsTemplate
        rootMode localSigma localPi bound)).
Proof.
  intros M hPA translation
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses sigmaProduction piProduction
    sourceWitnessList sourceContext bound mode formula
    assignmentCode assignmentStep rowPrefix antecedent rowLookup
    concreteProduction hproduction hrow.
  cbn zeta in *.
  subst bound.
  change
    (coqFourStateTableAppendConcreteClosedRowProductionTemplate
      sigmaProduction piProduction =
     coqFourStateTableAppendOpenedGlobalRowProductionTemplate
      rootMode localSigma localPi (ttParameter boundName))
    in hproduction.
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
            (coqFourStateTableAppendOpenedGlobalRowProductionTemplate
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
            (coqFourStateTableAppendOpenedGlobalRowProductionTemplate
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
          (coqFourStateTableAppendOpenedGlobalRowProductionTemplate
            rootMode localSigma localPi (ttParameter boundName))))
      hrowOpened) as hall5.
  fold coqFourStateTableAppendOpenedGlobalRowsTemplate.
  rewrite coqFourStateTableAppendOpenedGlobalRowsTemplate_shape.
  exact hall5.
Qed.

Lemma coqFourStateTableAppendOpenedGlobalFormulaTemplate_and7_shape : forall
    rootMode localSigma localPi bound,
  let source := coqFourStateTableAppendOpenedGlobalFormulaTemplate
    rootMode localSigma localPi bound in
  source = tfAnd (templateAnd7First source)
    (tfAnd (templateAnd7Second source)
      (tfAnd (templateAnd7Third source)
        (tfAnd (templateAnd7Fourth source)
          (tfAnd (templateAnd7Fifth source)
            (tfAnd (templateAnd7Sixth source)
              (templateAnd7Seventh source)))))).
Proof.
  intros.
  reflexivity.
Qed.

Lemma coqFourStateTableAppendOpenedGlobalFormulaTemplate_field_shapes : forall
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep,
  rootMode = 0 \/ rootMode = 1 ->
  let source := coqFourStateTableAppendOpenedGlobalFormulaTemplate
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
    assignmentStepCode assignmentStepStep [-> | ->].
  - cbn zeta. repeat split; reflexivity.
  - cbn zeta. repeat split; reflexivity.
Qed.

(** Exact syntactic alignment of the six table fields.  The local-row field
    is intentionally selected from the opened global body itself; the next
    row-specific bridge can therefore be proved independently of all table
    projections.  The old table terms disappear computationally because the
    selected append projections mention only the eight new witnesses. *)
Lemma coqFourStateTableAppendOpenedGlobalFormulaTemplate_shape : forall
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep,
  rootMode = 0 \/ rootMode = 1 ->
  coqFourStateTableAppendOpenedGlobalFormulaTemplate
    rootMode localSigma localPi (ttParameter boundName) =
  coqFourStateTableAppendTraversalBodyTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    (ttParameter boundName)
    (embedPATerm (Term.numeral rootMode))
    (ttVar 0) (ttVar 1) (ttVar 2)
    (templateAnd7Seventh
      (coqFourStateTableAppendOpenedGlobalFormulaTemplate
        rootMode localSigma localPi (ttParameter boundName))).
Proof.
  intros rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep hrootMode.
  pose proof
    (coqFourStateTableAppendOpenedGlobalFormulaTemplate_and7_shape
      rootMode localSigma localPi (ttParameter boundName)) as hshape.
  destruct
    (coqFourStateTableAppendOpenedGlobalFormulaTemplate_field_shapes
      rootMode localSigma localPi boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep hrootMode)
    as [hmode [hformula [hassignmentCode
      [hassignmentStep [hbound hlookup]]]]].
  rewrite hshape.
  unfold coqFourStateTableAppendTraversalBodyTemplate.
  rewrite hmode, hformula, hassignmentCode, hassignmentStep, hbound, hlookup.
  reflexivity.
Qed.

(** Assemble the exact seven-field append record.  All six stable projections
    are produced over the initial standard witnessed tail.  The generic
    dependency-ordered conjunction compiler transports them to the final tail
    chosen by [hrows] and retains its source-context inclusion certificate. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_four_state_table_append_traversal_body :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    witnesses rows,
  let sourceWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M) in
  let sourceContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M) in
  let prefix := coqFourStateTableAppendWitnessContext
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep [] in
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext prefix
    (rawTemplateFormula translation rows) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext prefix
    (rawTemplateFormula translation
      (coqFourStateTableAppendTraversalBodyTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep rows)).
Proof.
  intros M hPA translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    witnesses rows sourceWitnessList sourceContext prefix hrows.
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
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_defined_components
      M hPA translation
      (embedPAContext (map witnessedAxiom witnesses))
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    as (modeRoot & formulaRoot & assignmentCodeRoot & assignmentStepRoot &
      hmode & hformula & hassignmentCode & hassignmentStep).
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_root_bound
      M hPA translation
      (embedPAContext (map witnessedAxiom witnesses))
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    as [boundRoot hbound].
  destruct
    (raw_codedPALocalProofOf_four_state_table_append_new_state_lookup
      M hPA translation
      (embedPAContext (map witnessedAxiom witnesses))
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep)
    as [lookupRoot hlookup].
  rewrite (raw_fourStateTableAppendWitnessContext_witnessed_tail_code
    M translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep witnesses)
    in hmode, hformula, hassignmentCode, hassignmentStep, hbound, hlookup.
  pose proof
    (raw_codedPAGrowingTemplateLocalProofAt_and7_of_six_local
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep [])
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
      modeRoot formulaRoot assignmentCodeRoot assignmentStepRoot
      boundRoot lookupRoot
      hsource hmode hformula hassignmentCode hassignmentStep
      hbound hlookup hrows) as hrecord.
  unfold coqFourStateTableAppendTraversalBodyTemplate.
  rewrite !rawTemplateFormula_and.
  exact hrecord.
Qed.

(** Close the global successor from a proof of its extracted row field.

    The table append source remains over the initial standard witnessed PA
    context.  The row proof may grow that context.  We first assemble the
    seven-field body, introduce the ten global witnesses in the deep append
    context, and finally eliminate the eight append eigenvariables using the
    dependency-ordered growing eliminator.  Thus no proof is silently moved
    between independently selected contexts. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_global_of_append_rows :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    rootMode localSigma localPi boundName
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
  let opened := coqFourStateTableAppendOpenedGlobalFormulaTemplate
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
      (embedPAFormula
        (dynamicTruthGlobalFormula (Term.numeral rootMode)
          localSigma localPi))).
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
      (templateAnd7Seventh
        (coqFourStateTableAppendOpenedGlobalFormulaTemplate
          rootMode localSigma localPi (ttParameter boundName))) hrows)
    as hbody.
  pose proof
    (coqFourStateTableAppendOpenedGlobalFormulaTemplate_shape
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
        (embedPAFormula
          (dynamicTruthGlobalFormula (Term.numeral rootMode)
            localSigma localPi)))
      (coqFourStateTableAppendGlobalTraversalWitnesses
        (ttParameter boundName))
      (coqFourStateTableAppendOpenedGlobalFormulaTemplate
        rootMode localSigma localPi (ttParameter boundName))
      bodyRoot
      (coqFourStateTableAppendOpenedGlobalFormulaTemplate_success
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
          (embedPAFormula
            (dynamicTruthGlobalFormula (Term.numeral rootMode)
              localSigma localPi))))).
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
      (embedPAFormula
        (dynamicTruthGlobalFormula (Term.numeral rootMode)
          localSigma localPi))
      appendRoot
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName) (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2)
      hsource happend hcontinuation).
Qed.

(** Public composition of the concrete row compiler with global append
    closure.  All context growth, five row binders, ten global witness
    introductions, and eight append eliminations are internal to this
    theorem.  Its single syntactic premise deliberately exposes the remaining
    local-row normalization seam. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_global_of_append_concrete_row :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses sigmaProduction piProduction appendRoot,
  rootMode = 0 \/ rootMode = 1 ->
  coqFourStateTableAppendConcreteClosedRowProductionTemplate
    sigmaProduction piProduction =
  coqFourStateTableAppendOpenedGlobalRowProductionTemplate
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
      (embedPAFormula
        (dynamicTruthGlobalFormula (Term.numeral rootMode)
          localSigma localPi))).
Proof.
  intros M hPA translation hagreement
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses sigmaProduction piProduction appendRoot
    hrootMode hproduction happend hrow.
  apply
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_global_of_append_rows
      M hPA translation hagreement
      rootMode localSigma localPi boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      witnesses appendRoot hrootMode happend).
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_opened_global_rows_of_concrete_row
      M hPA translation
      rootMode localSigma localPi boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      witnesses sigmaProduction piProduction hproduction hrow).
Qed.

(** Scoped client of the composed endpoint.  The two concrete polarity
    bodies are the ordinary embeddings of the local Sigma/Pi rows, so the
    preceding normalization theorem discharges the former equality premise
    internally. *)
Corollary
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_global_of_append_scoped_concrete_row :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses appendRoot,
  rootMode = 0 \/ rootMode = 1 ->
  StandardFormulaScoped 13 localSigma ->
  StandardFormulaScoped 13 localPi ->
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
            (embedPAFormula localSigma) (embedPAFormula localPi))))) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) []
    (rawTemplateFormula translation
      (embedPAFormula
        (dynamicTruthGlobalFormula (Term.numeral rootMode)
          localSigma localPi))).
Proof.
  intros M hPA translation hagreement
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses appendRoot hrootMode hSigma hPi happend hrow.
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_global_of_append_concrete_row
      M hPA translation hagreement
      rootMode localSigma localPi boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      witnesses (embedPAFormula localSigma) (embedPAFormula localPi)
      appendRoot hrootMode
      (coqFourStateTableAppendConcreteClosedRowProductionTemplate_embedded_eq_opened
        rootMode localSigma localPi (ttParameter boundName) hSigma hPi)
      happend hrow).
Qed.

(** Close the literal global append successor from the pre-split row roots.
    The concrete row compiler above supplies the seventh traversal field;
    the scoped append endpoint supplies all universal/existential closure and
    the other six fields.  No row proof or prefix-identification premise is
    exposed by this composition. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_global_of_append_concrete_global_row_inputs :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall rootMode localSigma localPi boundName witnesses
    appendRoot inheritedTraversal oldLookup fixedProductionRoot,
  rootMode = 0 \/ rootMode = 1 ->
  StandardFormulaScoped 13 localSigma ->
  StandardFormulaScoped 13 localPi ->
  templateUniversalOpenMany inheritedTraversal
    coqFourStateTableAppendConcreteRowVariables =
    Some
      (tfImp
        (coqLtSuccCasesBelowTemplate
          (ttVar 4) (ttParameter boundName))
        (tfImp oldLookup
          (coqFourStateTableAppendConcreteClosedRowProductionTemplate
            (embedPAFormula localSigma) (embedPAFormula localPi)))) ->
  RawFourStateTableAppendInheritedLocalRootsAt M translation
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (coqFourStateTableAppendRowPrefix
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      (ttParameter boundName)
      (embedPATerm (Term.numeral rootMode))
      (ttVar 0) (ttVar 1) (ttVar 2))
    inheritedTraversal oldLookup ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqFourStateTableAppendRowPrefix
        (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
        (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
        (ttParameter boundName)
        (embedPATerm (Term.numeral rootMode))
        (ttVar 0) (ttVar 1) (ttVar 2)))
    (rawTemplateFormula translation
      (templateFormulaOpen (embedPATerm (Term.numeral rootMode))
        (coqFourStateTableAppendEmbeddedModeProductionMotive
          localSigma localPi))) fixedProductionRoot ->
  RawCodedPALocalProofOf M
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (rawTemplateFormula translation
      (coqFourStateTableAppendExistsTemplate
        (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
        (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
        (ttParameter boundName)
        (embedPATerm (Term.numeral rootMode))
        (ttVar 0) (ttVar 1) (ttVar 2))) appendRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) []
    (rawTemplateFormula translation
      (embedPAFormula
        (dynamicTruthGlobalFormula (Term.numeral rootMode)
          localSigma localPi))).
Proof.
  intros M hPA translation hagreement
    rootMode localSigma localPi boundName witnesses
    appendRoot inheritedTraversal oldLookup fixedProductionRoot
    hrootMode hSigma hPi hopen hinheritedRoots hfixedProduction happend.
  apply
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_global_of_append_scoped_concrete_row
      M hPA translation hagreement
      rootMode localSigma localPi boundName
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      witnesses appendRoot hrootMode hSigma hPi happend).
  exact
    (raw_codedPALocalProofOf_four_state_table_append_concrete_global_closed_row_implications
      M hPA translation hagreement
      rootMode boundName localSigma localPi witnesses
      inheritedTraversal oldLookup fixedProductionRoot
      hrootMode hopen hinheritedRoots hfixedProduction).
Qed.

(** The row compiler may use a syntactically different temporary prefix—for
    example one containing named carrier parameters.  Equality of translated
    prefix codes over every raw tail is the exact and weakest condition needed
    to feed that proof to the scoped global endpoint. *)
Corollary
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_global_of_append_code_equivalent_row_prefix :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses appendRoot rowPrefix,
  rootMode = 0 \/ rootMode = 1 ->
  StandardFormulaScoped 13 localSigma ->
  StandardFormulaScoped 13 localPi ->
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
            (embedPAFormula localSigma) (embedPAFormula localPi))))) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) []
    (rawTemplateFormula translation
      (embedPAFormula
        (dynamicTruthGlobalFormula (Term.numeral rootMode)
          localSigma localPi))).
Proof.
  intros M hPA translation hagreement
    rootMode localSigma localPi boundName
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses appendRoot rowPrefix
    hrootMode hSigma hPi hprefix happend hrow.
  apply
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_global_of_append_scoped_concrete_row
      M hPA translation hagreement
      rootMode localSigma localPi boundName
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      witnesses appendRoot hrootMode hSigma hPi happend).
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
              (embedPAFormula localSigma) (embedPAFormula localPi)))))
      hprefix hrow).
Qed.

End PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
