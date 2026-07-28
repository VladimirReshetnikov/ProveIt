(**
  Abstract direct inputs for the carrier-level derivation-soundness template.

  The soundness template has two genuinely opaque formula families: truth of
  a context and truth of a conclusion.  This file does not manufacture either
  family.  Instead, each family is supplied by a direct selector carrying the
  exact represented shift and opening traces required at its opaque leaves.

  Named parameters are interpreted by represented numeral terms.  Their
  existing structural trace construction supplies the two term fields of
  [RawCodedTemplateDirectStructuralInputs].  Predicate names zero and one are
  dispatched to the context- and conclusion-truth selectors, respectively;
  unused predicate names receive bottom.  Thus the resulting package is a
  finite structural boundary only, with no hidden semantic truth producer.
*)

From Stdlib Require Import List Arith.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFormulaShiftTreeRealization
  RawCodedFormulaOperationTreeRealization
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateNumeralTermSyntax
  RawCodedTemplateTernaryApplication
  RawCodedRestrictedPAConsistencyFromUniversalSoundness.

Import ListNotations.

Module PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaOperationTreeRealization.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateNumeralTermSyntax.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.

(** ------------------------------------------------------------------
    A selector-independent view of translated template terms. *)

(** Formula interpretations cannot affect term translation.  We nevertheless
    need a complete structural-symbol record to invoke the shared translator,
    so this canonical term view fills its irrelevant opaque component with
    bottom. *)
Definition rawCoqRestrictedPADerivationSoundnessTermViewSymbols
    (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M)
    : RawCodedTemplateStructuralSymbols M :=
  rawNumeralTemplateSymbols M parameters
    (fun _ _ => rawFormulaBotCode M).

Definition rawCoqRestrictedPADerivationSoundnessTemplateTermView
    (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M)
    (input : TemplateTerm) : M :=
  rawStructuralTemplateTermWith M
    (rawCoqRestrictedPADerivationSoundnessTermViewSymbols M parameters)
    input.

Definition rawCoqRestrictedPADerivationSoundnessTemplateTermsView
    (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : list TemplateTerm) : list M :=
  map
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters)
    inputs.

Arguments rawCoqRestrictedPADerivationSoundnessTermViewSymbols
  M _ : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessTemplateTermView
  M _ _ : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessTemplateTermsView
  M _ _ : clear implicits.

(** These three facts are shared by every adapter from a deeply closed
    ternary predicate to the five-argument truth interface.  Keeping them at
    the selector-independent term view prevents the context and conclusion
    adapters from carrying parallel copies of the same syntax argument. *)
Lemma rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (parameters : RawCodedTemplateNumeralParameters M) input,
  RawCodedTermSyntax M
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters input).
Proof.
  intros M hPA parameters input.
  unfold rawCoqRestrictedPADerivationSoundnessTemplateTermView,
    rawCoqRestrictedPADerivationSoundnessTermViewSymbols.
  apply raw_numeralTemplateTerm_syntax.
  exact hPA.
Qed.

Lemma rawCoqRestrictedPADerivationSoundnessTemplateTermView_shift : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (parameters : RawCodedTemplateNumeralParameters M) depth input,
  RawCodedTermShift M
    (rawNumeralValue M depth) (rawNumeralValue M 1)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters input)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
      (templateTermRename (templateShiftRenamingAt depth) input)).
Proof.
  intros M hPA parameters depth input.
  unfold rawCoqRestrictedPADerivationSoundnessTemplateTermView,
    rawCoqRestrictedPADerivationSoundnessTermViewSymbols.
  apply raw_numeralTemplateTerm_shift.
  exact hPA.
Qed.

Lemma rawCoqRestrictedPADerivationSoundnessTemplateTermView_opening : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (parameters : RawCodedTemplateNumeralParameters M)
      depth replacement input,
  RawCodedFormulaSubstitutionAtom M
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters replacement)
    (rawNumeralValue M depth)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters input)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
      (templateTermSubst
        (templateOpeningSubstAt depth replacement) input)).
Proof.
  intros M hPA parameters depth replacement input.
  unfold rawCoqRestrictedPADerivationSoundnessTemplateTermView,
    rawCoqRestrictedPADerivationSoundnessTermViewSymbols.
  apply raw_numeralTemplateTerm_substitutionAtom.
  exact hPA.
Qed.

(** ------------------------------------------------------------------
    Abstract direct selectors for the two opaque truth families. *)

(** A selector chooses a carrier formula code from exactly five translated
    argument terms.  Its laws are deliberately phrased only on honest finite
    template terms.  They neither assert a semantic truth law nor claim that
    arbitrary carrier inputs commute with syntax operations. *)
Record RawCoqRestrictedPATruthDirectSelector
    (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M) : Type := {
  rawCoqRestrictedPATruthDirectOutput : M -> M -> M -> M -> M -> M;

  rawCoqRestrictedPATruthDirectShiftAt : forall
      depth first second third fourth fifth,
    RawCodedFormulaShift M
      (rawNumeralValue M depth) (rawNumeralValue M 1)
      (rawCoqRestrictedPATruthDirectOutput
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters first)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters second)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters third)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters fourth)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters fifth))
      (rawCoqRestrictedPATruthDirectOutput
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
          (templateTermRename (templateShiftRenamingAt depth) first))
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
          (templateTermRename (templateShiftRenamingAt depth) second))
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
          (templateTermRename (templateShiftRenamingAt depth) third))
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
          (templateTermRename (templateShiftRenamingAt depth) fourth))
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
          (templateTermRename (templateShiftRenamingAt depth) fifth)));

  rawCoqRestrictedPATruthDirectOpeningAt : forall
      depth replacement first second third fourth fifth,
    RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters replacement)
      (rawNumeralValue M depth)
      (rawCoqRestrictedPATruthDirectOutput
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters first)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters second)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters third)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters fourth)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters fifth))
      (rawCoqRestrictedPATruthDirectOutput
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
          (templateTermSubst (templateOpeningSubstAt depth replacement)
            first))
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
          (templateTermSubst (templateOpeningSubstAt depth replacement)
            second))
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
          (templateTermSubst (templateOpeningSubstAt depth replacement)
            third))
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
          (templateTermSubst (templateOpeningSubstAt depth replacement)
            fourth))
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
          (templateTermSubst (templateOpeningSubstAt depth replacement)
            fifth)))
}.

Arguments rawCoqRestrictedPATruthDirectOutput
  {M parameters} _ _ _ _ _ _.
Arguments rawCoqRestrictedPATruthDirectShiftAt
  {M parameters} _ _ _ _ _ _ _.
Arguments rawCoqRestrictedPATruthDirectOpeningAt
  {M parameters} _ _ _ _ _ _ _ _.

(** Exact-arity dispatch for one selector.  Rename and substitution preserve
    list length, so malformed arities may consistently use bottom at both
    endpoints of every direct operation. *)
Definition rawCoqRestrictedPATruthDirectSelectorCode
    {M : RawPAModel}
    {parameters : RawCodedTemplateNumeralParameters M}
    (selector : RawCoqRestrictedPATruthDirectSelector M parameters)
    (arguments : list M) : M :=
  match arguments with
  | [first; second; third; fourth; fifth] =>
      rawCoqRestrictedPATruthDirectOutput selector
        first second third fourth fifth
  | _ => rawFormulaBotCode M
  end.

Arguments rawCoqRestrictedPATruthDirectSelectorCode
  {M parameters} _ _.

(** Predicate-name dispatch is total.  Names zero and one are exactly those
    fixed by [coqRestrictedPAContextTruthPredicateName] and
    [coqRestrictedPAConclusionTruthPredicateName].  A wrong arity or unused
    name receives the transparent one-node bottom formula. *)
Definition rawCoqRestrictedPADerivationSoundnessOpaqueCode
    {M : RawPAModel}
    {parameters : RawCodedTemplateNumeralParameters M}
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    (predicate : TemplatePredicateName) (arguments : list M) : M :=
  match predicate with
  | 0 => rawCoqRestrictedPATruthDirectSelectorCode contextTruth arguments
  | 1 => rawCoqRestrictedPATruthDirectSelectorCode conclusionTruth arguments
  | S (S _) => rawFormulaBotCode M
  end.

Arguments rawCoqRestrictedPADerivationSoundnessOpaqueCode
  {M parameters} _ _ _ _.

Lemma rawCoqRestrictedPADerivationSoundnessOpaqueCode_context : forall
    M parameters
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    first second third fourth fifth,
  rawCoqRestrictedPADerivationSoundnessOpaqueCode
    contextTruth conclusionTruth
    coqRestrictedPAContextTruthPredicateName
    [first; second; third; fourth; fifth] =
  rawCoqRestrictedPATruthDirectOutput contextTruth
    first second third fourth fifth.
Proof. reflexivity. Qed.

Lemma rawCoqRestrictedPADerivationSoundnessOpaqueCode_conclusion : forall
    M parameters
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    first second third fourth fifth,
  rawCoqRestrictedPADerivationSoundnessOpaqueCode
    contextTruth conclusionTruth
    coqRestrictedPAConclusionTruthPredicateName
    [first; second; third; fourth; fifth] =
  rawCoqRestrictedPATruthDirectOutput conclusionTruth
    first second third fourth fifth.
Proof. reflexivity. Qed.

Lemma rawCoqRestrictedPADerivationSoundnessOpaqueCode_other_predicate : forall
    M parameters
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    predicate arguments,
  rawCoqRestrictedPADerivationSoundnessOpaqueCode
    contextTruth conclusionTruth (S (S predicate)) arguments =
  rawFormulaBotCode M.
Proof. reflexivity. Qed.

(** One-node represented operation trees discharge every unused opaque name.
    Keeping these facts local makes the abstract nature of the two selected
    truth families explicit. *)
Lemma raw_coqRestrictedPADerivationSoundness_bottom_shift : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff amount,
  RawCodedFormulaShift M cutoff amount
    (rawFormulaBotCode M) (rawFormulaBotCode M).
Proof.
  intros M hPA cutoff amount.
  exact (raw_codedFormulaShift_of_valid_tree M hPA amount
    (RFSTBot M cutoff) I).
Qed.

Lemma raw_coqRestrictedPADerivationSoundness_bottom_opening : forall
    (M : RawPAModel), RawPASatisfies M -> forall replacement depth,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement depth (rawFormulaBotCode M) (rawFormulaBotCode M).
Proof.
  intros M hPA replacement depth.
  exact (raw_codedFormulaOperation_of_valid_tree M hPA
    (RawCodedFormulaSubstitutionAtom M) replacement
    (RFSTBot M depth) I).
Qed.

(** ------------------------------------------------------------------
    The complete direct structural package. *)

Definition rawCoqRestrictedPADerivationSoundnessTemplateSymbols
    (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    : RawCodedTemplateStructuralSymbols M :=
  rawNumeralTemplateSymbols M parameters
    (rawCoqRestrictedPADerivationSoundnessOpaqueCode
      contextTruth conclusionTruth).

Arguments rawCoqRestrictedPADerivationSoundnessTemplateSymbols
  M _ _ _ : clear implicits.

(** Term translation depends only on the parameter-code projection of the
    symbols record.  This structural lemma avoids unfolding the proof fields
    of the later direct-input record merely to expose that fact. *)
Lemma rawCoqRestrictedPADerivationSoundnessTemplateTerm_symbols : forall
    M parameters
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters) input,
  rawStructuralTemplateTermWith M
    (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
      M parameters contextTruth conclusionTruth) input =
  rawCoqRestrictedPADerivationSoundnessTemplateTermView
    M parameters input.
Proof.
  intros M parameters contextTruth conclusionTruth input.
  induction input as
      [index | name | | child IHchild
      | lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs];
    cbn [rawCoqRestrictedPADerivationSoundnessTemplateSymbols
      rawCoqRestrictedPADerivationSoundnessTemplateTermView
      rawCoqRestrictedPADerivationSoundnessTermViewSymbols
      rawStructuralTemplateTermWith rawNumeralTemplateSymbols];
    try rewrite IHchild; try rewrite IHlhs, IHrhs; reflexivity.
Qed.

Lemma rawCoqRestrictedPADerivationSoundnessTemplateTerms_symbols : forall
    M parameters
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters) inputs,
  rawStructuralTemplateTermsWith M
    (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
      M parameters contextTruth conclusionTruth) inputs =
  rawCoqRestrictedPADerivationSoundnessTemplateTermsView
    M parameters inputs.
Proof.
  intros M parameters contextTruth conclusionTruth inputs.
  unfold rawStructuralTemplateTermsWith,
    rawCoqRestrictedPADerivationSoundnessTemplateTermsView.
  apply map_ext. intro input.
  apply rawCoqRestrictedPADerivationSoundnessTemplateTerm_symbols.
Qed.

(** On the selector-independent term view, exact-arity dispatch reduces to a
    seven-way list-shape split: one selected branch and six bottom branches. *)
Lemma rawCoqRestrictedPATruthDirectSelectorCode_view_shiftAt : forall
    (M : RawPAModel), RawPASatisfies M -> forall parameters
    (selector : RawCoqRestrictedPATruthDirectSelector M parameters)
    depth arguments,
  RawCodedFormulaShift M
    (rawNumeralValue M depth) (rawNumeralValue M 1)
    (rawCoqRestrictedPATruthDirectSelectorCode selector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermsView
        M parameters arguments))
    (rawCoqRestrictedPATruthDirectSelectorCode selector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermsView M parameters
        (templateTermsRename
          (templateShiftRenamingAt depth) arguments))).
Proof.
  intros M hPA parameters selector depth arguments.
  destruct arguments as
    [|first [|second [|third [|fourth [|fifth [|sixth rest]]]]]];
    cbn [rawCoqRestrictedPADerivationSoundnessTemplateTermsView
      rawCoqRestrictedPATruthDirectSelectorCode templateTermsRename].
  all: try
    (apply raw_coqRestrictedPADerivationSoundness_bottom_shift; exact hPA).
  apply rawCoqRestrictedPATruthDirectShiftAt.
Qed.

Lemma rawCoqRestrictedPATruthDirectSelectorCode_view_openingAt : forall
    (M : RawPAModel), RawPASatisfies M -> forall parameters
    (selector : RawCoqRestrictedPATruthDirectSelector M parameters)
    depth replacement arguments,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters replacement)
    (rawNumeralValue M depth)
    (rawCoqRestrictedPATruthDirectSelectorCode selector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermsView
        M parameters arguments))
    (rawCoqRestrictedPATruthDirectSelectorCode selector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermsView M parameters
        (templateTermsSubst
          (templateOpeningSubstAt depth replacement) arguments))).
Proof.
  intros M hPA parameters selector depth replacement arguments.
  destruct arguments as
    [|first [|second [|third [|fourth [|fifth [|sixth rest]]]]]];
    cbn [rawCoqRestrictedPADerivationSoundnessTemplateTermsView
      rawCoqRestrictedPATruthDirectSelectorCode templateTermsSubst].
  all: try
    (apply raw_coqRestrictedPADerivationSoundness_bottom_opening; exact hPA).
  apply rawCoqRestrictedPATruthDirectOpeningAt.
Qed.

(** Transport the selector-view result to the structural symbols used by the
    complete soundness package. *)
Lemma rawCoqRestrictedPATruthDirectSelectorCode_shiftAt : forall
    (M : RawPAModel), RawPASatisfies M -> forall parameters
    (contextTruth conclusionTruth selector :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    depth arguments,
  RawCodedFormulaShift M
    (rawNumeralValue M depth) (rawNumeralValue M 1)
    (rawCoqRestrictedPATruthDirectSelectorCode selector
      (rawStructuralTemplateTermsWith M
        (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
          M parameters contextTruth conclusionTruth) arguments))
    (rawCoqRestrictedPATruthDirectSelectorCode selector
      (rawStructuralTemplateTermsWith M
        (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
          M parameters contextTruth conclusionTruth)
        (templateTermsRename
          (templateShiftRenamingAt depth) arguments))).
Proof.
  intros M hPA parameters contextTruth conclusionTruth selector
    depth arguments.
  rewrite
    !rawCoqRestrictedPADerivationSoundnessTemplateTerms_symbols.
  apply rawCoqRestrictedPATruthDirectSelectorCode_view_shiftAt.
  exact hPA.
Qed.

(** The analogous transport for opening also aligns the replacement term. *)
Lemma rawCoqRestrictedPATruthDirectSelectorCode_openingAt : forall
    (M : RawPAModel), RawPASatisfies M -> forall parameters
    (contextTruth conclusionTruth selector :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    depth replacement arguments,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    (rawStructuralTemplateTermWith M
      (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
        M parameters contextTruth conclusionTruth) replacement)
    (rawNumeralValue M depth)
    (rawCoqRestrictedPATruthDirectSelectorCode selector
      (rawStructuralTemplateTermsWith M
        (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
          M parameters contextTruth conclusionTruth) arguments))
    (rawCoqRestrictedPATruthDirectSelectorCode selector
      (rawStructuralTemplateTermsWith M
        (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
          M parameters contextTruth conclusionTruth)
        (templateTermsSubst
          (templateOpeningSubstAt depth replacement) arguments))).
Proof.
  intros M hPA parameters contextTruth conclusionTruth selector
    depth replacement arguments.
  rewrite rawCoqRestrictedPADerivationSoundnessTemplateTerm_symbols.
  rewrite
    !rawCoqRestrictedPADerivationSoundnessTemplateTerms_symbols.
  apply rawCoqRestrictedPATruthDirectSelectorCode_view_openingAt.
  exact hPA.
Qed.

(** The constructor combines existing numeral-term support with exactly the
    four selector traces.  No decoded formula tree is requested at either
    selected opaque leaf. *)
Definition rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters)
    : RawCodedTemplateDirectStructuralInputs M.
Proof.
  refine
    {| rawDirectTemplateSymbols :=
         rawCoqRestrictedPADerivationSoundnessTemplateSymbols
           M parameters contextTruth conclusionTruth;
       rawDirectTemplateTermShiftAt := _;
       rawDirectTemplateTermOpeningAt := _;
       rawDirectTemplateOpaqueShiftAt := _;
       rawDirectTemplateOpaqueOpeningAt := _ |}.
  - apply raw_numeralTemplateTerm_shift. exact hPA.
  - apply raw_numeralTemplateTerm_substitutionAtom. exact hPA.
  - intros depth [|[|predicate]] arguments.
    + cbn [
        rawCoqRestrictedPADerivationSoundnessOpaqueCode
        rawStructuralTemplateFormulaWith
        templateFormulaRename].
      apply rawCoqRestrictedPATruthDirectSelectorCode_shiftAt. exact hPA.
    + cbn [
        rawCoqRestrictedPADerivationSoundnessOpaqueCode
        rawStructuralTemplateFormulaWith
        templateFormulaRename].
      apply rawCoqRestrictedPATruthDirectSelectorCode_shiftAt. exact hPA.
    + cbn [rawCoqRestrictedPADerivationSoundnessTemplateSymbols
        rawCoqRestrictedPADerivationSoundnessOpaqueCode
        rawStructuralTemplateFormulaWith
        rawStructuralTemplateTermsWith
        rawNumeralTemplateSymbols
        templateFormulaRename].
      apply raw_coqRestrictedPADerivationSoundness_bottom_shift.
      exact hPA.
  - intros depth replacement [|[|predicate]] arguments.
    + cbn [
        rawCoqRestrictedPADerivationSoundnessOpaqueCode
        rawStructuralTemplateFormulaWith
        templateFormulaSubst].
      apply rawCoqRestrictedPATruthDirectSelectorCode_openingAt. exact hPA.
    + cbn [
        rawCoqRestrictedPADerivationSoundnessOpaqueCode
        rawStructuralTemplateFormulaWith
        templateFormulaSubst].
      apply rawCoqRestrictedPATruthDirectSelectorCode_openingAt. exact hPA.
    + cbn [rawCoqRestrictedPADerivationSoundnessTemplateSymbols
        rawCoqRestrictedPADerivationSoundnessOpaqueCode
        rawStructuralTemplateFormulaWith
        rawStructuralTemplateTermsWith
        rawNumeralTemplateSymbols
        templateFormulaSubst].
      apply raw_coqRestrictedPADerivationSoundness_bottom_opening.
      exact hPA.
Defined.

Arguments
  rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
  M _ _ _ _ : clear implicits.

(** ------------------------------------------------------------------
    Exact direct term and formula views. *)

Section Views.

Context (M : RawPAModel) (hPA : RawPASatisfies M).
Context (parameters : RawCodedTemplateNumeralParameters M).
Context (contextTruth conclusionTruth :
  RawCoqRestrictedPATruthDirectSelector M parameters).

Let inputs : RawCodedTemplateDirectStructuralInputs M :=
  rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
    M hPA parameters contextTruth conclusionTruth.

(** This is the promised selector-independence equation for every finite
    template term, not merely for the arguments occurring in the soundness
    predicate. *)
Lemma rawCoqRestrictedPADerivationSoundnessDirectTerm_view : forall input,
  rawDirectTemplateTerm inputs input =
  rawCoqRestrictedPADerivationSoundnessTemplateTermView
    M parameters input.
Proof.
  intro input.
  change (rawStructuralTemplateTermWith M
    (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
      M parameters contextTruth conclusionTruth) input =
    rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters input).
  apply rawCoqRestrictedPADerivationSoundnessTemplateTerm_symbols.
Qed.

Lemma rawCoqRestrictedPADerivationSoundnessDirectTerms_view : forall inputs0,
  map (rawDirectTemplateTerm inputs) inputs0 =
  rawCoqRestrictedPADerivationSoundnessTemplateTermsView
    M parameters inputs0.
Proof.
  intro inputs0.
  apply map_ext. intro input.
  apply rawCoqRestrictedPADerivationSoundnessDirectTerm_view.
Qed.

(** The general formula view records the exact structural interpretation
    selected by the package.  The following leaf equations then expose the
    only two nontransparent cases without normalizing a larger template. *)
Lemma rawCoqRestrictedPADerivationSoundnessDirectFormula_view : forall formula,
  rawDirectTemplateFormula inputs formula =
  rawStructuralTemplateFormulaWith M
    (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
      M parameters contextTruth conclusionTruth) formula.
Proof. reflexivity. Qed.

Lemma rawCoqRestrictedPADerivationSoundnessContextTruthLeaf_view : forall
    first second third fourth fifth,
  rawDirectTemplateFormula inputs
    (tfOpaque coqRestrictedPAContextTruthPredicateName
      [first; second; third; fourth; fifth]) =
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
  rewrite rawCoqRestrictedPADerivationSoundnessDirectFormula_view.
  change
    (rawCoqRestrictedPATruthDirectOutput contextTruth
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
          M parameters contextTruth conclusionTruth) first)
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
          M parameters contextTruth conclusionTruth) second)
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
          M parameters contextTruth conclusionTruth) third)
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
          M parameters contextTruth conclusionTruth) fourth)
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
          M parameters contextTruth conclusionTruth) fifth) =
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
    rawCoqRestrictedPADerivationSoundnessTemplateTerm_symbols.
  reflexivity.
Qed.

Lemma rawCoqRestrictedPADerivationSoundnessConclusionTruthLeaf_view : forall
    first second third fourth fifth,
  rawDirectTemplateFormula inputs
    (tfOpaque coqRestrictedPAConclusionTruthPredicateName
      [first; second; third; fourth; fifth]) =
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
  rewrite rawCoqRestrictedPADerivationSoundnessDirectFormula_view.
  change
    (rawCoqRestrictedPATruthDirectOutput conclusionTruth
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
          M parameters contextTruth conclusionTruth) first)
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
          M parameters contextTruth conclusionTruth) second)
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
          M parameters contextTruth conclusionTruth) third)
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
          M parameters contextTruth conclusionTruth) fourth)
      (rawStructuralTemplateTermWith M
        (rawCoqRestrictedPADerivationSoundnessTemplateSymbols
          M parameters contextTruth conclusionTruth) fifth) =
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
    rawCoqRestrictedPADerivationSoundnessTemplateTerm_symbols.
  reflexivity.
Qed.

(** Exact named-template views used by the carrier induction compiler. *)
Lemma rawCoqRestrictedPADerivationSoundnessContextTruthTemplate_view :
  rawDirectTemplateFormula inputs
    coqRestrictedPADerivationSoundnessContextTruthTemplate =
  rawCoqRestrictedPATruthDirectOutput contextTruth
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
      coqRestrictedPASoundnessLowerLevelTerm)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
      coqRestrictedPASoundnessUpperLevelTerm)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
      (ttVar 3))
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
      (ttVar 1))
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
      (ttVar 0)).
Proof.
  apply rawCoqRestrictedPADerivationSoundnessContextTruthLeaf_view.
Qed.

Lemma rawCoqRestrictedPADerivationSoundnessConclusionTruthTemplate_view :
  rawDirectTemplateFormula inputs
    coqRestrictedPADerivationSoundnessConclusionTruthTemplate =
  rawCoqRestrictedPATruthDirectOutput conclusionTruth
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
      coqRestrictedPASoundnessLowerLevelTerm)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
      coqRestrictedPASoundnessUpperLevelTerm)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
      (ttVar 2))
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
      (ttVar 1))
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView M parameters
      (ttVar 0)).
Proof.
  apply rawCoqRestrictedPADerivationSoundnessConclusionTruthLeaf_view.
Qed.

End Views.

(** The existential form is intentionally conditional on both abstract
    selectors.  It asserts only availability of a structural input record,
    not existence or semantic adequacy of either truth selector. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs_exists
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters),
  exists inputs : RawCodedTemplateDirectStructuralInputs M, True.
Proof.
  intros M hPA parameters contextTruth conclusionTruth.
  exists
    (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth).
  exact I.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
