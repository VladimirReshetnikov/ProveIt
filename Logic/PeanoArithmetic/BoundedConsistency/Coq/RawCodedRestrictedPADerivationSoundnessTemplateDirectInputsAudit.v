(** Kernel-facing audit for the abstract derivation-soundness direct inputs. *)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputsAudit.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.

Check rawCoqRestrictedPADerivationSoundnessTermViewSymbols.
Check rawCoqRestrictedPADerivationSoundnessTemplateTermView.
Check rawCoqRestrictedPADerivationSoundnessTemplateTermsView.
Check rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
Check rawCoqRestrictedPADerivationSoundnessTemplateTermView_shift.
Check rawCoqRestrictedPADerivationSoundnessTemplateTermView_opening.

Check RawCoqRestrictedPATruthDirectSelector.
Check rawCoqRestrictedPATruthDirectOutput.
Check rawCoqRestrictedPATruthDirectShiftAt.
Check rawCoqRestrictedPATruthDirectOpeningAt.
Check rawCoqRestrictedPATruthDirectSelectorCode.

Check rawCoqRestrictedPADerivationSoundnessOpaqueCode.
Check rawCoqRestrictedPADerivationSoundnessOpaqueCode_context.
Check rawCoqRestrictedPADerivationSoundnessOpaqueCode_conclusion.
Check rawCoqRestrictedPADerivationSoundnessOpaqueCode_other_predicate.
Check raw_coqRestrictedPADerivationSoundness_bottom_shift.
Check raw_coqRestrictedPADerivationSoundness_bottom_opening.

Check rawCoqRestrictedPADerivationSoundnessTemplateSymbols.
Check rawCoqRestrictedPADerivationSoundnessTemplateTerm_symbols.
Check rawCoqRestrictedPADerivationSoundnessTemplateTerms_symbols.
Check rawCoqRestrictedPATruthDirectSelectorCode_shiftAt.
Check rawCoqRestrictedPATruthDirectSelectorCode_openingAt.
Check
  rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs.
Check rawCoqRestrictedPADerivationSoundnessDirectTerm_view.
Check rawCoqRestrictedPADerivationSoundnessDirectTerms_view.
Check rawCoqRestrictedPADerivationSoundnessDirectFormula_view.
Check rawCoqRestrictedPADerivationSoundnessContextTruthLeaf_view.
Check rawCoqRestrictedPADerivationSoundnessConclusionTruthLeaf_view.
Check rawCoqRestrictedPADerivationSoundnessContextTruthTemplate_view.
Check rawCoqRestrictedPADerivationSoundnessConclusionTruthTemplate_view.
Check
  raw_coqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs_exists.

Print Assumptions
  rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessTemplateTermView_shift.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessTemplateTermView_opening.

Section ExactBoundary.

Variable M : RawPAModel.
Variable hPA : RawPASatisfies M.
Variable parameters : RawCodedTemplateNumeralParameters M.
Variable contextTruth conclusionTruth :
  RawCoqRestrictedPATruthDirectSelector M parameters.

Let inputs : RawCodedTemplateDirectStructuralInputs M :=
  rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
    M hPA parameters contextTruth conclusionTruth.

(** The abstract selectors suffice for the complete generic direct-translation
    record.  No semantic or native dynamic-truth field appears in this type. *)
Check inputs : RawCodedTemplateDirectStructuralInputs M.

Check (rawDirectTemplateTermShiftAt inputs)
  : forall depth input,
      RawCodedTermShift M
        (rawNumeralValue M depth) (rawNumeralValue M 1)
        (rawDirectTemplateTerm inputs input)
        (rawDirectTemplateTerm inputs
          (templateTermRename (templateShiftRenamingAt depth) input)).

Check (rawDirectTemplateTermOpeningAt inputs)
  : forall depth replacement input,
      RawCodedFormulaSubstitutionAtom M
        (rawDirectTemplateTerm inputs replacement)
        (rawNumeralValue M depth)
        (rawDirectTemplateTerm inputs input)
        (rawDirectTemplateTerm inputs
          (templateTermSubst
            (templateOpeningSubstAt depth replacement) input)).

(** Exact selector-independent term view. *)
Check (rawCoqRestrictedPADerivationSoundnessDirectTerm_view
  M hPA parameters contextTruth conclusionTruth)
  : forall input,
      rawDirectTemplateTerm inputs input =
      rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters input.

(** Exact context-truth and conclusion-truth formula leaves. *)
Check (rawCoqRestrictedPADerivationSoundnessContextTruthLeaf_view
  M hPA parameters contextTruth conclusionTruth)
  : forall first second third fourth fifth,
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

Check (rawCoqRestrictedPADerivationSoundnessConclusionTruthLeaf_view
  M hPA parameters contextTruth conclusionTruth)
  : forall first second third fourth fifth,
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

(** The concrete soundness-template leaves reduce to those same two selected
    output families, with their five arguments preserved in order. *)
Check (rawCoqRestrictedPADerivationSoundnessContextTruthTemplate_view
  M hPA parameters contextTruth conclusionTruth)
  : rawDirectTemplateFormula inputs
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

Check (rawCoqRestrictedPADerivationSoundnessConclusionTruthTemplate_view
  M hPA parameters contextTruth conclusionTruth)
  : rawDirectTemplateFormula inputs
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

(** Both designated names reject malformed arities definitionally. *)
Goal forall first second third fourth,
  rawCoqRestrictedPADerivationSoundnessOpaqueCode
    contextTruth conclusionTruth coqRestrictedPAContextTruthPredicateName
    [first; second; third; fourth] =
  RawCodedSyntaxConstructors.PABoundedRawCodedSyntaxConstructors.rawFormulaBotCode
    M.
Proof. reflexivity. Qed.

Goal forall first second third fourth fifth sixth,
  rawCoqRestrictedPADerivationSoundnessOpaqueCode
    contextTruth conclusionTruth coqRestrictedPAConclusionTruthPredicateName
    [first; second; third; fourth; fifth; sixth] =
  RawCodedSyntaxConstructors.PABoundedRawCodedSyntaxConstructors.rawFormulaBotCode
    M.
Proof. reflexivity. Qed.

End ExactBoundary.

Print Assumptions
  rawCoqRestrictedPADerivationSoundnessOpaqueCode_context.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessOpaqueCode_conclusion.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessOpaqueCode_other_predicate.
Print Assumptions raw_coqRestrictedPADerivationSoundness_bottom_shift.
Print Assumptions raw_coqRestrictedPADerivationSoundness_bottom_opening.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessTemplateTerm_symbols.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessTemplateTerms_symbols.
Print Assumptions rawCoqRestrictedPATruthDirectSelectorCode_shiftAt.
Print Assumptions rawCoqRestrictedPATruthDirectSelectorCode_openingAt.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessDirectTerm_view.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessDirectFormula_view.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessContextTruthLeaf_view.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessConclusionTruthLeaf_view.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessContextTruthTemplate_view.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessConclusionTruthTemplate_view.
Print Assumptions
  raw_coqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs_exists.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputsAudit.
