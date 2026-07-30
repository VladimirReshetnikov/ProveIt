(**
  Extensible direct inputs for restricted-PA soundness templates.

  The restricted soundness compiler reserves opaque predicate names zero and
  one for its five-argument context- and conclusion-truth families.  Dynamic
  truth successor rows additionally need two independent three-argument
  families.  Reusing either reserved name would silently identify unrelated
  carrier formula codes at nonstandard levels.

  This module factors the mixed-arity dispatch into a reusable tail
  interface.  Names zero and one retain exactly their existing meanings;
  name [S (S p)] is delegated to a caller-supplied tail at local name [p].
  The concrete tail provided below maps local names zero and one to two
  ternary-application selectors and maps every remaining shape to bottom.

  Crucially, all operation laws are required only on structurally translated
  finite template terms.  This is the honest domain on which the represented
  ternary selectors commute with shift and opening; no claim is made about
  arbitrary elements of a nonstandard model.
*)

From Stdlib Require Import List Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateNumeralTermSyntax
  RawCodedTemplateTernaryApplication
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateNumeralTermSyntax.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.

(** ------------------------------------------------------------------
    An abstract tail for predicate names at least two. *)

Record RawCoqRestrictedPAOpaqueTailDirectSelector
    (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M) : Type := {
  rawCoqRestrictedPAOpaqueTailOutput :
    TemplatePredicateName -> list M -> M;

  rawCoqRestrictedPAOpaqueTailShiftAt : forall
      depth predicate arguments,
    RawCodedFormulaShift M
      (rawNumeralValue M depth) (rawNumeralValue M 1)
      (rawCoqRestrictedPAOpaqueTailOutput predicate
        (rawCoqRestrictedPADerivationSoundnessTemplateTermsView
          M parameters arguments))
      (rawCoqRestrictedPAOpaqueTailOutput predicate
        (rawCoqRestrictedPADerivationSoundnessTemplateTermsView
          M parameters
          (templateTermsRename
            (templateShiftRenamingAt depth) arguments)));

  rawCoqRestrictedPAOpaqueTailOpeningAt : forall
      depth replacement predicate arguments,
    RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters replacement)
      (rawNumeralValue M depth)
      (rawCoqRestrictedPAOpaqueTailOutput predicate
        (rawCoqRestrictedPADerivationSoundnessTemplateTermsView
          M parameters arguments))
      (rawCoqRestrictedPAOpaqueTailOutput predicate
        (rawCoqRestrictedPADerivationSoundnessTemplateTermsView
          M parameters
          (templateTermsSubst
            (templateOpeningSubstAt depth replacement) arguments)))
}.

Arguments rawCoqRestrictedPAOpaqueTailOutput
  {M parameters} _ _ _.
Arguments rawCoqRestrictedPAOpaqueTailShiftAt
  {M parameters} _ _ _ _.
Arguments rawCoqRestrictedPAOpaqueTailOpeningAt
  {M parameters} _ _ _ _ _.

(** ------------------------------------------------------------------
    Exact-arity adapter for one ternary selector. *)

Definition rawCoqRestrictedPATernaryDirectSelectorCode
    {M : RawPAModel} {predicateCode : M}
    (selector : RawCodedTernaryApplicationSelector M predicateCode)
    (arguments : list M) : M :=
  match arguments with
  | [first; second; third] =>
      rawTernaryApplicationOutput selector first second third
  | _ => rawFormulaBotCode M
  end.

Arguments rawCoqRestrictedPATernaryDirectSelectorCode
  {M predicateCode} _ _.

Lemma rawCoqRestrictedPATernaryDirectSelectorCode_shiftAt : forall
    (M : RawPAModel), RawPASatisfies M -> forall parameters predicateCode
    (selector : RawCodedTernaryApplicationSelector M predicateCode),
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    M predicateCode selector ->
  forall depth arguments,
  RawCodedFormulaShift M
    (rawNumeralValue M depth) (rawNumeralValue M 1)
    (rawCoqRestrictedPATernaryDirectSelectorCode selector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermsView
        M parameters arguments))
    (rawCoqRestrictedPATernaryDirectSelectorCode selector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermsView
        M parameters
        (templateTermsRename
          (templateShiftRenamingAt depth) arguments))).
Proof.
  intros M hPA parameters predicateCode selector hcommuting
    depth arguments.
  destruct arguments as
    [|first [|second [|third [|fourth rest]]]];
    cbn [rawCoqRestrictedPADerivationSoundnessTemplateTermsView
      rawCoqRestrictedPATernaryDirectSelectorCode templateTermsRename].
  all: try
    (apply raw_coqRestrictedPADerivationSoundness_bottom_shift; exact hPA).
  eapply
    (rawCoqDynamicTruthTemplateTernary_shift_commuting_on_syntax
      hcommuting).
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_shift.
    exact hPA.
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_shift.
    exact hPA.
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_shift.
    exact hPA.
Qed.

Lemma rawCoqRestrictedPATernaryDirectSelectorCode_openingAt : forall
    (M : RawPAModel), RawPASatisfies M -> forall parameters predicateCode
    (selector : RawCodedTernaryApplicationSelector M predicateCode),
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    M predicateCode selector ->
  forall depth replacement arguments,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters replacement)
    (rawNumeralValue M depth)
    (rawCoqRestrictedPATernaryDirectSelectorCode selector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermsView
        M parameters arguments))
    (rawCoqRestrictedPATernaryDirectSelectorCode selector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermsView
        M parameters
        (templateTermsSubst
          (templateOpeningSubstAt depth replacement) arguments))).
Proof.
  intros M hPA parameters predicateCode selector hcommuting
    depth replacement arguments.
  destruct arguments as
    [|first [|second [|third [|fourth rest]]]];
    cbn [rawCoqRestrictedPADerivationSoundnessTemplateTermsView
      rawCoqRestrictedPATernaryDirectSelectorCode templateTermsSubst].
  all: try
    (apply raw_coqRestrictedPADerivationSoundness_bottom_opening; exact hPA).
  eapply
    (rawCoqDynamicTruthTemplateTernary_opening_commuting_on_syntax
      hcommuting).
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_opening.
    exact hPA.
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_opening.
    exact hPA.
  - apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_opening.
    exact hPA.
Qed.

(** Two independent ternary families occupy local tail slots zero and one.
    The local numbering matters: the enclosing extension adds two, yielding
    global predicate names two and three. *)
Definition rawCoqRestrictedPATernaryPairTailCode
    {M : RawPAModel} {firstPredicateCode secondPredicateCode : M}
    (firstSelector :
      RawCodedTernaryApplicationSelector M firstPredicateCode)
    (secondSelector :
      RawCodedTernaryApplicationSelector M secondPredicateCode)
    (predicate : TemplatePredicateName) (arguments : list M) : M :=
  match predicate with
  | 0 => rawCoqRestrictedPATernaryDirectSelectorCode
      firstSelector arguments
  | 1 => rawCoqRestrictedPATernaryDirectSelectorCode
      secondSelector arguments
  | S (S _) => rawFormulaBotCode M
  end.

Arguments rawCoqRestrictedPATernaryPairTailCode
  {M firstPredicateCode secondPredicateCode} _ _ _ _.

Definition rawCoqRestrictedPATernaryPairTailDirectSelector
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (firstPredicateCode secondPredicateCode : M)
    (firstSelector :
      RawCodedTernaryApplicationSelector M firstPredicateCode)
    (secondSelector :
      RawCodedTernaryApplicationSelector M secondPredicateCode)
    (firstCommuting :
      RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
        M firstPredicateCode firstSelector)
    (secondCommuting :
      RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
        M secondPredicateCode secondSelector)
    : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters.
Proof.
  refine
    {| rawCoqRestrictedPAOpaqueTailOutput :=
         rawCoqRestrictedPATernaryPairTailCode
           firstSelector secondSelector |}.
  - intros depth [|[|predicate]] arguments.
    + cbn [rawCoqRestrictedPATernaryPairTailCode].
      apply rawCoqRestrictedPATernaryDirectSelectorCode_shiftAt;
        assumption.
    + cbn [rawCoqRestrictedPATernaryPairTailCode].
      apply rawCoqRestrictedPATernaryDirectSelectorCode_shiftAt;
        assumption.
    + cbn [rawCoqRestrictedPATernaryPairTailCode].
      apply raw_coqRestrictedPADerivationSoundness_bottom_shift.
      exact hPA.
  - intros depth replacement [|[|predicate]] arguments.
    + cbn [rawCoqRestrictedPATernaryPairTailCode].
      apply rawCoqRestrictedPATernaryDirectSelectorCode_openingAt;
        assumption.
    + cbn [rawCoqRestrictedPATernaryPairTailCode].
      apply rawCoqRestrictedPATernaryDirectSelectorCode_openingAt;
        assumption.
    + cbn [rawCoqRestrictedPATernaryPairTailCode].
      apply raw_coqRestrictedPADerivationSoundness_bottom_opening.
      exact hPA.
Defined.

Arguments rawCoqRestrictedPATernaryPairTailDirectSelector
  M _ _ _ _ _ _ _ _ : clear implicits.

(** ------------------------------------------------------------------
    Extension of the two reserved soundness predicates. *)

Definition rawCoqRestrictedPADerivationSoundnessExtendedOpaqueCode
    {M : RawPAModel}
    {parameters : RawCodedTemplateNumeralParameters M}
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    (tail : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters)
    (predicate : TemplatePredicateName) (arguments : list M) : M :=
  match predicate with
  | 0 => rawCoqRestrictedPATruthDirectSelectorCode
      contextTruth arguments
  | 1 => rawCoqRestrictedPATruthDirectSelectorCode
      conclusionTruth arguments
  | S (S tailPredicate) =>
      rawCoqRestrictedPAOpaqueTailOutput tail tailPredicate arguments
  end.

Arguments rawCoqRestrictedPADerivationSoundnessExtendedOpaqueCode
  {M parameters} _ _ _ _ _.

Definition rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
    (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    (tail : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters)
    : RawCodedTemplateStructuralSymbols M :=
  rawNumeralTemplateSymbols M parameters
    (rawCoqRestrictedPADerivationSoundnessExtendedOpaqueCode
      contextTruth conclusionTruth tail).

Arguments
  rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
  M _ _ _ _ : clear implicits.

Lemma rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerm_symbols :
    forall M parameters
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      (tail : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters)
      input,
  rawStructuralTemplateTermWith M
    (rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
      M parameters contextTruth conclusionTruth tail) input =
  rawCoqRestrictedPADerivationSoundnessTemplateTermView
    M parameters input.
Proof.
  intros M parameters contextTruth conclusionTruth tail input.
  induction input as
      [index | name | | child IHchild
      | lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs];
    cbn [rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
      rawCoqRestrictedPADerivationSoundnessTemplateTermView
      rawCoqRestrictedPADerivationSoundnessTermViewSymbols
      rawStructuralTemplateTermWith rawNumeralTemplateSymbols];
    try rewrite IHchild; try rewrite IHlhs, IHrhs; reflexivity.
Qed.

Lemma rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerms_symbols :
    forall M parameters
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      (tail : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters)
      inputs,
  rawStructuralTemplateTermsWith M
    (rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
      M parameters contextTruth conclusionTruth tail) inputs =
  rawCoqRestrictedPADerivationSoundnessTemplateTermsView
    M parameters inputs.
Proof.
  intros M parameters contextTruth conclusionTruth tail inputs.
  unfold rawStructuralTemplateTermsWith,
    rawCoqRestrictedPADerivationSoundnessTemplateTermsView.
  apply map_ext. intro input.
  apply
    rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerm_symbols.
Qed.

Definition
    rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    (tail : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters)
    : RawCodedTemplateDirectStructuralInputs M.
Proof.
  refine
    {| rawDirectTemplateSymbols :=
         rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
           M parameters contextTruth conclusionTruth tail;
       rawDirectTemplateTermShiftAt := _;
       rawDirectTemplateTermOpeningAt := _;
       rawDirectTemplateOpaqueShiftAt := _;
       rawDirectTemplateOpaqueOpeningAt := _ |}.
  - apply raw_numeralTemplateTerm_shift. exact hPA.
  - apply raw_numeralTemplateTerm_substitutionAtom. exact hPA.
  - intros depth [|[|predicate]] arguments.
    + cbn [rawCoqRestrictedPADerivationSoundnessExtendedOpaqueCode
        rawStructuralTemplateFormulaWith templateFormulaRename].
      rewrite
        !rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerms_symbols.
      apply rawCoqRestrictedPATruthDirectSelectorCode_view_shiftAt.
      exact hPA.
    + cbn [rawCoqRestrictedPADerivationSoundnessExtendedOpaqueCode
        rawStructuralTemplateFormulaWith templateFormulaRename].
      rewrite
        !rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerms_symbols.
      apply rawCoqRestrictedPATruthDirectSelectorCode_view_shiftAt.
      exact hPA.
    + cbn [rawCoqRestrictedPADerivationSoundnessExtendedOpaqueCode
        rawStructuralTemplateFormulaWith templateFormulaRename].
      rewrite
        !rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerms_symbols.
      apply rawCoqRestrictedPAOpaqueTailShiftAt.
  - intros depth replacement [|[|predicate]] arguments.
    + cbn [rawCoqRestrictedPADerivationSoundnessExtendedOpaqueCode
        rawStructuralTemplateFormulaWith templateFormulaSubst].
      rewrite
        rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerm_symbols.
      rewrite
        !rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerms_symbols.
      apply rawCoqRestrictedPATruthDirectSelectorCode_view_openingAt.
      exact hPA.
    + cbn [rawCoqRestrictedPADerivationSoundnessExtendedOpaqueCode
        rawStructuralTemplateFormulaWith templateFormulaSubst].
      rewrite
        rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerm_symbols.
      rewrite
        !rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerms_symbols.
      apply rawCoqRestrictedPATruthDirectSelectorCode_view_openingAt.
      exact hPA.
    + cbn [rawCoqRestrictedPADerivationSoundnessExtendedOpaqueCode
        rawStructuralTemplateFormulaWith templateFormulaSubst].
      rewrite
        rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerm_symbols.
      rewrite
        !rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerms_symbols.
      apply rawCoqRestrictedPAOpaqueTailOpeningAt.
Defined.

Arguments
  rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
  M _ _ _ _ _ : clear implicits.

(** ------------------------------------------------------------------
    Exact views of the three dispatch regions. *)

Section ExtendedViews.

Context (M : RawPAModel) (hPA : RawPASatisfies M).
Context (parameters : RawCodedTemplateNumeralParameters M).
Context (contextTruth conclusionTruth :
  RawCoqRestrictedPATruthDirectSelector M parameters).
Context (tail : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters).

Local Definition extendedInputs :=
  rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
    M hPA parameters contextTruth conclusionTruth tail.

Lemma rawCoqRestrictedPADerivationSoundnessExtendedDirectTerm_view :
    forall input,
  rawDirectTemplateTerm extendedInputs input =
  rawCoqRestrictedPADerivationSoundnessTemplateTermView
    M parameters input.
Proof.
  intro input.
  apply
    rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerm_symbols.
Qed.

(** Extended opaque selectors do not affect term translation.  Expose the
    arbitrary finite shift theorem explicitly so clients of the extended
    input record need not reconstruct the numeral-template symbol view. *)
Lemma rawCoqRestrictedPADerivationSoundnessExtendedDirectTerm_shift_by :
    forall cutoff amount input,
  RawCodedTermShift M
    (rawNumeralValue M cutoff) (rawNumeralValue M amount)
    (rawDirectTemplateTerm extendedInputs input)
    (rawDirectTemplateTerm extendedInputs
      (templateTermRename
        (templateShiftRenamingBy cutoff amount) input)).
Proof.
  intros cutoff amount input.
  rewrite !rawCoqRestrictedPADerivationSoundnessExtendedDirectTerm_view.
  unfold rawCoqRestrictedPADerivationSoundnessTemplateTermView,
    rawCoqRestrictedPADerivationSoundnessTermViewSymbols.
  apply raw_numeralTemplateTerm_shift_by.
  exact hPA.
Qed.

Lemma rawCoqRestrictedPADerivationSoundnessExtendedDirectFormula_view :
    forall formula,
  rawDirectTemplateFormula extendedInputs formula =
  rawStructuralTemplateFormulaWith M
    (rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
      M parameters contextTruth conclusionTruth tail) formula.
Proof. reflexivity. Qed.

Lemma rawCoqRestrictedPADerivationSoundnessExtendedContextTruthLeaf_view :
    forall first second third fourth fifth,
  rawDirectTemplateFormula extendedInputs
    (tfOpaque 0 [first; second; third; fourth; fifth]) =
  rawCoqRestrictedPATruthDirectOutput contextTruth
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters first)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters second)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters third)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters fourth)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters fifth).
Proof.
  intros first second third fourth fifth.
  rewrite
    rawCoqRestrictedPADerivationSoundnessExtendedDirectFormula_view.
  change
    (rawCoqRestrictedPATruthDirectOutput contextTruth
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
          M parameters contextTruth conclusionTruth tail) first)
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
          M parameters contextTruth conclusionTruth tail) second)
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
          M parameters contextTruth conclusionTruth tail) third)
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
          M parameters contextTruth conclusionTruth tail) fourth)
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
          M parameters contextTruth conclusionTruth tail) fifth) =
     rawCoqRestrictedPATruthDirectOutput contextTruth
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters first)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters second)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)).
  repeat rewrite
    rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerm_symbols.
  reflexivity.
Qed.

Lemma
    rawCoqRestrictedPADerivationSoundnessExtendedConclusionTruthLeaf_view :
    forall first second third fourth fifth,
  rawDirectTemplateFormula extendedInputs
    (tfOpaque 1 [first; second; third; fourth; fifth]) =
  rawCoqRestrictedPATruthDirectOutput conclusionTruth
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters first)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters second)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters third)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters fourth)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters fifth).
Proof.
  intros first second third fourth fifth.
  rewrite
    rawCoqRestrictedPADerivationSoundnessExtendedDirectFormula_view.
  change
    (rawCoqRestrictedPATruthDirectOutput conclusionTruth
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
          M parameters contextTruth conclusionTruth tail) first)
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
          M parameters contextTruth conclusionTruth tail) second)
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
          M parameters contextTruth conclusionTruth tail) third)
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
          M parameters contextTruth conclusionTruth tail) fourth)
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
          M parameters contextTruth conclusionTruth tail) fifth) =
     rawCoqRestrictedPATruthDirectOutput conclusionTruth
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters first)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters second)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)).
  repeat rewrite
    rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerm_symbols.
  reflexivity.
Qed.

(** The tail view is intentionally arity-independent.  A concrete tail may
    impose exact arities internally, as the ternary pair does below. *)
Lemma rawCoqRestrictedPADerivationSoundnessExtendedTailLeaf_view : forall
    predicate arguments,
  rawDirectTemplateFormula extendedInputs
    (tfOpaque (S (S predicate)) arguments) =
  rawCoqRestrictedPAOpaqueTailOutput tail predicate
    (rawCoqRestrictedPADerivationSoundnessTemplateTermsView
      M parameters arguments).
Proof.
  intros predicate arguments.
  rewrite
    rawCoqRestrictedPADerivationSoundnessExtendedDirectFormula_view.
  change
    (rawCoqRestrictedPAOpaqueTailOutput tail predicate
      (rawStructuralTemplateTermsWith M
        (rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols
          M parameters contextTruth conclusionTruth tail) arguments) =
     rawCoqRestrictedPAOpaqueTailOutput tail predicate
      (rawCoqRestrictedPADerivationSoundnessTemplateTermsView
        M parameters arguments)).
  rewrite
    rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerms_symbols.
  reflexivity.
Qed.

End ExtendedViews.

(** Global names for the dynamic-truth tail. *)
Definition coqRestrictedPALowerPiTruthPredicateName :
    TemplatePredicateName := 2.
Definition coqRestrictedPALowerSigmaTruthPredicateName :
    TemplatePredicateName := 3.

(** Compatibility equations make the slot discipline explicit and allow
    downstream identification proofs to avoid unfolding the direct record. *)
Lemma rawCoqRestrictedPADerivationSoundnessExtendedOpaqueCode_context :
    forall M parameters
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      (tail : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters)
      first second third fourth fifth,
  rawCoqRestrictedPADerivationSoundnessExtendedOpaqueCode
    contextTruth conclusionTruth tail 0
    [first; second; third; fourth; fifth] =
  rawCoqRestrictedPATruthDirectOutput contextTruth
    first second third fourth fifth.
Proof. reflexivity. Qed.

Lemma rawCoqRestrictedPADerivationSoundnessExtendedOpaqueCode_conclusion :
    forall M parameters
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      (tail : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters)
      first second third fourth fifth,
  rawCoqRestrictedPADerivationSoundnessExtendedOpaqueCode
    contextTruth conclusionTruth tail 1
    [first; second; third; fourth; fifth] =
  rawCoqRestrictedPATruthDirectOutput conclusionTruth
    first second third fourth fifth.
Proof. reflexivity. Qed.

(** The useful equations are stated for an arbitrary well-formed pair tail;
    proof fields are irrelevant because projection selects only its code. *)
Lemma rawCoqRestrictedPATernaryPairTailCode_first : forall
    M firstPredicateCode secondPredicateCode
    (firstSelector :
      RawCodedTernaryApplicationSelector M firstPredicateCode)
    (secondSelector :
      RawCodedTernaryApplicationSelector M secondPredicateCode)
    first second third,
  rawCoqRestrictedPATernaryPairTailCode
    firstSelector secondSelector 0 [first; second; third] =
  rawTernaryApplicationOutput firstSelector first second third.
Proof. reflexivity. Qed.

Lemma rawCoqRestrictedPATernaryPairTailCode_second : forall
    M firstPredicateCode secondPredicateCode
    (firstSelector :
      RawCodedTernaryApplicationSelector M firstPredicateCode)
    (secondSelector :
      RawCodedTernaryApplicationSelector M secondPredicateCode)
    first second third,
  rawCoqRestrictedPATernaryPairTailCode
    firstSelector secondSelector 1 [first; second; third] =
  rawTernaryApplicationOutput secondSelector first second third.
Proof. reflexivity. Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.
