(**
  Dynamic pointwise truth for model-internal coded contexts.

  There are two deliberately separate layers in this file.

  The semantic layer is parameterized by an ordinary Rocq formula constructor
  [sigmaEvidence] and an external carrier relation [Sigma].  It proves the
  exact meaning of the context formula in every law-free raw arithmetic
  structure:

      there is one honest context-spine traversal, and every value in a live
      head-table slot satisfies [Sigma] under the displayed assignment.

  The code layer starts instead from a possibly nonstandard carrier code for
  a deeply closed ternary Sigma predicate.  Such a code cannot honestly be
  decoded into a Rocq [formula], so no semantic satisfaction claim is made
  about it.  We apply it through [RawCodedTernaryApplicationSelector] at the
  innermost pointwise leaf, surround it by quoted traversal/lookup formulas,
  and prove directly that the resulting carrier code is again a deeply
  closed ternary predicate.  This is the exact structural boundary needed by
  the direct derivation-soundness template.

  The de Bruijn layout of the code layer is worth recording.  The public
  arguments are

      context = #2, assignmentCode = #1, assignmentStep = #0.

  Five existential traversal witnesses and then two universal pointwise
  witnesses put the Sigma leaf at

      formula = #0, assignmentCode = #8, assignmentStep = #7.

  Thus the leaf has scope nine.  The surrounding body has scope eight before
  the two universal binders, and the five existential wrappers lower the
  final deep-closure root from eight back to three.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedAssignmentTotality
  RawCodedContextLists
  RawCodedFormulaRankStep
  RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality
  RawCodedProofAtomicAdequacyStandard
  RawCodedTemplateTernaryApplication
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedTernaryPredicateDeepClosure
  RawCodedDynamicTruthGlobalSuccessorDeepClosure
  RawCodedDynamicTruthLowerApplicationDeepClosure
  RawCodedDynamicTruthPairedSuccessorLocalDeepClosure.

Module PABoundedRawCodedDynamicContextTruthSelector.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorDeepClosure.
Import PABoundedRawCodedDynamicTruthLowerApplicationDeepClosure.
Import PABoundedRawCodedDynamicTruthPairedSuccessorLocalDeepClosure.

(** ------------------------------------------------------------------
    Exact formula semantics, relative to an arbitrary Sigma relation. *)

Definition RawDynamicContextAllSigmaWithTables (M : RawPAModel)
    (Sigma : M -> M -> M -> Prop)
    (bound headCode headStep assignmentCode assignmentStep : M) : Prop :=
  forall index,
    rawLt M index bound ->
    forall formulaCode,
      RawCodedAssignmentLookup M
        headCode headStep index formulaCode ->
      Sigma formulaCode assignmentCode assignmentStep.

Arguments RawDynamicContextAllSigmaWithTables
  M Sigma bound headCode headStep assignmentCode assignmentStep
  : clear implicits.

(** [sigmaEvidence] is used only at the innermost leaf.  Under its two
    universal binders [formulaCode] is [#0], while the two displayed
    assignment terms have been lifted through both binders. *)
Definition dynamicContextAllSigmaWithTablesTermAt
    (sigmaEvidence : term -> term -> term -> formula)
    (bound headCode headStep assignmentCode assignmentStep : term)
    : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
      (pAll
        (pImp
          (codedAssignmentLookupTermAt
            (liftTerm 2 headCode) (liftTerm 2 headStep)
            (tVar 1) (tVar 0))
          (sigmaEvidence
            (tVar 0) (liftTerm 2 assignmentCode)
            (liftTerm 2 assignmentStep))))).

(** Pointwise semantic adequacy is the weakest honest interface between a
    metatheoretic formula constructor and an external relation.  In
    particular it says nothing about any carrier formula code. *)
Definition RawDynamicTernaryFormulaSemantics (M : RawPAModel)
    (sigmaEvidence : term -> term -> term -> formula)
    (Sigma : M -> M -> M -> Prop) : Prop :=
  forall (e : nat -> M) first second third,
    raw_formula_sat M e (sigmaEvidence first second third) <->
    Sigma
      (raw_term_eval M e first)
      (raw_term_eval M e second)
      (raw_term_eval M e third).

Arguments RawDynamicTernaryFormulaSemantics
  M sigmaEvidence Sigma : clear implicits.

Lemma raw_dynamicContext_eval_liftTerm_two : forall
    (M : RawPAModel) a b (e : nat -> M) input,
  raw_term_eval M (scons M a (scons M b e)) (liftTerm 2 input) =
  raw_term_eval M e input.
Proof.
  intros M a b e input. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 2) with (S (S index)) by lia. reflexivity.
Qed.

Theorem raw_sat_dynamicContextAllSigmaWithTablesTermAt_iff : forall
    (M : RawPAModel)
    (sigmaEvidence : term -> term -> term -> formula)
    (Sigma : M -> M -> M -> Prop),
  RawDynamicTernaryFormulaSemantics M sigmaEvidence Sigma ->
  forall (e : nat -> M) bound headCode headStep
      assignmentCode assignmentStep,
  raw_formula_sat M e
    (dynamicContextAllSigmaWithTablesTermAt sigmaEvidence
      bound headCode headStep assignmentCode assignmentStep) <->
  RawDynamicContextAllSigmaWithTables M Sigma
    (raw_term_eval M e bound)
    (raw_term_eval M e headCode) (raw_term_eval M e headStep)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep).
Proof.
  intros M sigmaEvidence Sigma hsigma e
    bound headCode headStep assignmentCode assignmentStep.
  unfold RawDynamicTernaryFormulaSemantics in hsigma.
  unfold dynamicContextAllSigmaWithTablesTermAt,
    RawDynamicContextAllSigmaWithTables.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  setoid_rewrite hsigma.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_one.
  repeat setoid_rewrite raw_dynamicContext_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** The public relation shares the head table between the traversal and the
    pointwise condition.  This prevents malformed context codes from making
    the universal clause vacuous. *)
Definition RawDynamicContextAllSigma (M : RawPAModel)
    (Sigma : M -> M -> M -> Prop)
    (context assignmentCode assignmentStep : M) : Prop :=
  exists bound tailCode tailStep headCode headStep : M,
    RawContextListTraversal M context
      bound tailCode tailStep headCode headStep /\
    RawDynamicContextAllSigmaWithTables M Sigma
      bound headCode headStep assignmentCode assignmentStep.

Arguments RawDynamicContextAllSigma
  M Sigma context assignmentCode assignmentStep : clear implicits.

Definition dynamicContextAllSigmaTermAt
    (sigmaEvidence : term -> term -> term -> formula)
    (context assignmentCode assignmentStep : term) : formula :=
  contextListEx5
    (pAnd
      (contextListTraversalTermAt
        (liftTerm 5 context)
        (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0))
      (dynamicContextAllSigmaWithTablesTermAt sigmaEvidence
        (tVar 4) (tVar 1) (tVar 0)
        (liftTerm 5 assignmentCode) (liftTerm 5 assignmentStep))).

Definition dynamicContextAllSigmaFormula
    (sigmaEvidence : term -> term -> term -> formula) : formula :=
  dynamicContextAllSigmaTermAt sigmaEvidence
    (tVar 2) (tVar 1) (tVar 0).

Theorem raw_sat_dynamicContextAllSigmaTermAt_iff : forall
    (M : RawPAModel)
    (sigmaEvidence : term -> term -> term -> formula)
    (Sigma : M -> M -> M -> Prop),
  RawDynamicTernaryFormulaSemantics M sigmaEvidence Sigma ->
  forall (e : nat -> M) context assignmentCode assignmentStep,
  raw_formula_sat M e
    (dynamicContextAllSigmaTermAt sigmaEvidence
      context assignmentCode assignmentStep) <->
  RawDynamicContextAllSigma M Sigma
    (raw_term_eval M e context)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep).
Proof.
  intros M sigmaEvidence Sigma hsigma e
    context assignmentCode assignmentStep.
  unfold dynamicContextAllSigmaTermAt, contextListEx5,
    RawDynamicContextAllSigma.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_contextListTraversalTermAt_iff.
  setoid_rewrite
    (raw_sat_dynamicContextAllSigmaWithTablesTermAt_iff
      M sigmaEvidence Sigma hsigma).
  repeat setoid_rewrite raw_contextList_eval_liftTerm_five.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Corollary raw_sat_dynamicContextAllSigmaFormula_iff : forall
    (M : RawPAModel)
    (sigmaEvidence : term -> term -> term -> formula)
    (Sigma : M -> M -> M -> Prop),
  RawDynamicTernaryFormulaSemantics M sigmaEvidence Sigma ->
  forall e,
  raw_formula_sat M e (dynamicContextAllSigmaFormula sigmaEvidence) <->
  RawDynamicContextAllSigma M Sigma (e 2) (e 1) (e 0).
Proof.
  intros M sigmaEvidence Sigma hsigma e.
  unfold dynamicContextAllSigmaFormula.
  rewrite (raw_sat_dynamicContextAllSigmaTermAt_iff
    M sigmaEvidence Sigma hsigma).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    The carrier formula-code constructor. *)

(** These three ordinary formula fragments are quoted independently.  Their
    variables are already written at the exact depths at which the fragments
    occur in the final code. *)
Definition dynamicContextTruthTraversalBody : formula :=
  contextListTraversalTermAt
    (tVar 7) (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0).

Definition dynamicContextTruthLiveIndexBody : formula :=
  Formula.ltTermAt (tVar 0) (tVar 5).

Definition dynamicContextTruthHeadLookupBody : formula :=
  codedAssignmentLookupTermAt
    (tVar 3) (tVar 2) (tVar 1) (tVar 0).

(** At the innermost pointwise leaf the selected Sigma predicate is applied
    to [formulaCode, assignmentCode, assignmentStep] = [#0,#8,#7]. *)
Definition rawDynamicContextSigmaApplicationCode
    {M : RawPAModel} {sigmaCode : M}
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode) : M :=
  rawTernaryApplicationOutput sigmaSelector
    (rawQuotedTermCode M (tVar 0))
    (rawQuotedTermCode M (tVar 8))
    (rawQuotedTermCode M (tVar 7)).

Arguments rawDynamicContextSigmaApplicationCode
  {M sigmaCode} _.

Definition rawDynamicContextAllSigmaWithTablesCode
    {M : RawPAModel} {sigmaCode : M}
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode) : M :=
  rawFormulaAllCode M
    (rawFormulaImpCode M
      (rawQuotedFormulaCode M dynamicContextTruthLiveIndexBody)
      (rawFormulaAllCode M
        (rawFormulaImpCode M
          (rawQuotedFormulaCode M dynamicContextTruthHeadLookupBody)
          (rawDynamicContextSigmaApplicationCode sigmaSelector)))).

Arguments rawDynamicContextAllSigmaWithTablesCode
  {M sigmaCode} _.

Definition rawDynamicContextFormulaEx5Code
    (M : RawPAModel) (body : M) : M :=
  rawFormulaExCode M
    (rawFormulaExCode M
      (rawFormulaExCode M
        (rawFormulaExCode M
          (rawFormulaExCode M body)))).

Definition rawDynamicContextAllSigmaCode
    {M : RawPAModel} {sigmaCode : M}
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode) : M :=
  rawDynamicContextFormulaEx5Code M
    (rawFormulaAndCode M
      (rawQuotedFormulaCode M dynamicContextTruthTraversalBody)
      (rawDynamicContextAllSigmaWithTablesCode sigmaSelector)).

Arguments rawDynamicContextAllSigmaCode {M sigmaCode} _.

(** Every quoted finite term is in the selector's honest syntax domain.  The
    all-zero beta assignment supplies the hidden realization columns. *)
Lemma raw_dynamicContext_quotedTerm_syntax : forall
    (M : RawPAModel), RawPASatisfies M -> forall input,
  RawCodedTermSyntax M (rawQuotedTermCode M input).
Proof.
  intros M hPA input.
  exists (raw_zero M), (raw_zero M).
  apply (raw_quotedTerm_syntax_realizable_of_assignment M hPA
    input (raw_zero M) (raw_zero M)).
  exact (raw_codedZeroAssignment_defined_all M hPA
    (raw_succ M (rawQuotedTermCode M input))).
Qed.

Lemma raw_dynamicContextSigmaApplication_trace : forall
    (M : RawPAModel), RawPASatisfies M -> forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode),
  RawCodedTernaryApplication M sigmaCode
    (rawQuotedTermCode M (tVar 0))
    (rawQuotedTermCode M (tVar 8))
    (rawQuotedTermCode M (tVar 7))
    (rawDynamicContextSigmaApplicationCode sigmaSelector).
Proof.
  intros M hPA sigmaCode sigmaSelector.
  apply rawTernaryApplicationOutput_trace;
    apply raw_dynamicContext_quotedTerm_syntax; exact hPA.
Qed.

(** Atomic adequacy of the selected leaf follows from its genuine five-trace
    application, not from any semantic interpretation of [sigmaCode]. *)
Lemma raw_dynamicContextSigmaApplication_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode),
  RawCodedFormulaAtomicallyAdequate M sigmaCode ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicContextSigmaApplicationCode sigmaSelector).
Proof.
  intros M hPA sigmaCode sigmaSelector hsigma.
  eapply (raw_codedTernaryApplication_target_atomically_adequate
    M hPA sigmaCode
    (rawQuotedTermCode M (tVar 0))
    (rawQuotedTermCode M (tVar 8))
    (rawQuotedTermCode M (tVar 7))).
  - exact hsigma.
  - apply raw_dynamicContext_quotedTerm_syntax. exact hPA.
  - apply raw_dynamicContextSigmaApplication_trace. exact hPA.
Qed.

(** The three arguments have scopes one, nine, and eight, respectively.
    The generalized ternary-application lemma therefore closes the selected
    Sigma leaf from the common root nine. *)
Lemma raw_dynamicContextSigmaApplication_deep_closed_from_nine : forall
    (M : RawPAModel), RawPASatisfies M -> forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode),
  RawCodedTernaryPredicateDeepClosed M sigmaCode ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 9)
    (rawDynamicContextSigmaApplicationCode sigmaSelector).
Proof.
  intros M hPA sigmaCode sigmaSelector hsigma.
  eapply (raw_standardTernaryApplication_deep_closed_from_root_scope
    M hPA 9 sigmaCode
    1 (tVar 0) 9 (tVar 8) 8 (tVar 7)).
  - exact hsigma.
  - intros index hfree. cbn in hfree. lia.
  - lia.
  - intros index hfree. cbn in hfree. lia.
  - lia.
  - intros index hfree. cbn in hfree. lia.
  - lia.
  - apply raw_dynamicContextSigmaApplication_trace. exact hPA.
  - apply raw_dynamicContextSigmaApplication_atomically_adequate.
    + exact hPA.
    + exact (proj1 hsigma).
Qed.

(** The fixed traversal body mentions variables only below eight. *)
Lemma raw_dynamicContextTraversalBody_deep_closed_from_eight : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 8)
    (rawQuotedFormulaCode M dynamicContextTruthTraversalBody).
Proof.
  intros M hPA.
  apply raw_quotedFormula_deep_closed_from_scope; [exact hPA |].
  intros index hfree. cbn in hfree. lia.
Qed.

(** The live-index test is used under one pointwise binder, hence root eight;
    its actual free-variable support is much smaller. *)
Lemma raw_dynamicContextLiveIndexBody_deep_closed_from_eight : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 8)
    (rawQuotedFormulaCode M dynamicContextTruthLiveIndexBody).
Proof.
  intros M hPA.
  apply raw_quotedFormula_deep_closed_from_scope; [exact hPA |].
  intros index hfree. cbn in hfree. lia.
Qed.

(** The head lookup is compared with the Sigma leaf under both pointwise
    binders, so we state its closure at the common root nine. *)
Lemma raw_dynamicContextHeadLookupBody_deep_closed_from_nine : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 9)
    (rawQuotedFormulaCode M dynamicContextTruthHeadLookupBody).
Proof.
  intros M hPA.
  apply raw_quotedFormula_deep_closed_from_scope; [exact hPA |].
  intros index hfree. cbn in hfree. lia.
Qed.

(** Constructor-by-constructor closure of the pointwise code. *)
Theorem raw_dynamicContextAllSigmaWithTablesCode_deep_closed_from_seven :
  forall (M : RawPAModel), RawPASatisfies M -> forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode),
  RawCodedTernaryPredicateDeepClosed M sigmaCode ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 7)
    (rawDynamicContextAllSigmaWithTablesCode sigmaSelector).
Proof.
  intros M hPA sigmaCode sigmaSelector hsigma.
  unfold rawDynamicContextAllSigmaWithTablesCode.
  apply (rawFormulaAllCode_deep_closed_from M hPA).
  apply (rawFormulaImpCode_deep_closed_from M hPA).
  - apply raw_dynamicContextLiveIndexBody_deep_closed_from_eight.
    exact hPA.
  - apply (rawFormulaAllCode_deep_closed_from M hPA).
    apply (rawFormulaImpCode_deep_closed_from M hPA).
    + apply raw_dynamicContextHeadLookupBody_deep_closed_from_nine.
      exact hPA.
    + apply raw_dynamicContextSigmaApplication_deep_closed_from_nine.
      * exact hPA.
      * exact hsigma.
Qed.

(** Five existential wrappers lower scope eight to the public ternary root
    three.  This is the main structural theorem of the code layer. *)
Theorem raw_dynamicContextAllSigmaCode_deep_closed : forall
    (M : RawPAModel), RawPASatisfies M -> forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode),
  RawCodedTernaryPredicateDeepClosed M sigmaCode ->
  RawCodedTernaryPredicateDeepClosed M
    (rawDynamicContextAllSigmaCode sigmaSelector).
Proof.
  intros M hPA sigmaCode sigmaSelector hsigma.
  apply (proj1 (rawCodedFormulaDeepClosedFrom_three_iff M _)).
  unfold rawDynamicContextAllSigmaCode,
    rawDynamicContextFormulaEx5Code.
  repeat apply (rawFormulaExCode_deep_closed_from M hPA).
  apply (rawFormulaAndCode_deep_closed_from M hPA).
  - apply raw_dynamicContextTraversalBody_deep_closed_from_eight.
    exact hPA.
  - change (RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 8)
      (rawDynamicContextAllSigmaWithTablesCode sigmaSelector)).
    apply (rawCodedFormulaDeepClosedFrom_weaken M hPA
      (rawNumeralValue M 7) (rawNumeralValue M 8)).
    + apply rawLe_numerals_of_le; [exact hPA | lia].
    + apply raw_dynamicContextAllSigmaWithTablesCode_deep_closed_from_seven
        with (sigmaCode := sigmaCode).
      * exact hPA.
      * exact hsigma.
Qed.

Corollary raw_dynamicContextAllSigmaCode_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode),
  RawCodedTernaryPredicateDeepClosed M sigmaCode ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicContextAllSigmaCode sigmaSelector).
Proof.
  intros M hPA sigmaCode sigmaSelector hsigma.
  exact (proj1 (raw_dynamicContextAllSigmaCode_deep_closed
    M hPA sigmaCode sigmaSelector hsigma)).
Qed.

(** Finally choose a genuine ternary application selector for the newly
    constructed context predicate.  Classical choice occurs only inside the
    already audited generic selector theorem. *)
Theorem raw_dynamicContextAllSigmaApplicationSelector_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode),
  RawCodedTernaryPredicateDeepClosed M sigmaCode ->
  exists contextSelector : RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaSelector),
    RawCodedTernaryPredicateDeepClosed M
      (rawDynamicContextAllSigmaCode sigmaSelector).
Proof.
  intros M hPA sigmaCode sigmaSelector hsigma.
  pose proof (raw_dynamicContextAllSigmaCode_deep_closed
    M hPA sigmaCode sigmaSelector hsigma) as hcontext.
  destruct (raw_codedTernaryApplicationSelector_exists M hPA
    (rawDynamicContextAllSigmaCode sigmaSelector) (proj1 hcontext))
    as [contextSelector _].
  exists contextSelector. exact hcontext.
Qed.

End PABoundedRawCodedDynamicContextTruthSelector.
