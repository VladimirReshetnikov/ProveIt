(**
  Assemble the seven fields of a global traversal after table append.

  The simultaneous append theorem supplies six stable facts in its deepest
  eight-witness context: four defined-through fields, the new root bound, and
  the lookup at the appended row.  The row compiler supplies the seventh fact
  and may grow the witnessed PA tail.  This module identifies the append
  context as a fixed template prefix over that tail and combines all seven
  facts in the dependency order required by the global successor.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPAAxiomWitnessPrefix
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedPALocalProofExistentialIntroductionChain
  RawCodedLtSuccCasesProofCompilation
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
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedPALocalProofExistentialIntroductionChain.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedFourStateTableAppendSource.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedPAGrowingTemplateConjunction.

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

End PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
