(** Kernel-facing audit for the concrete dynamic-truth direct inputs. *)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthTemplateNumeralParameters
  RawCodedDynamicTruthTemplateDirectInputs.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthTemplateDirectInputsAudit.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthTemplateNumeralParameters.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.

Check rawCoqDynamicTruthTemplateOpaqueCode.
Check rawCoqDynamicTruthTemplateOpaqueCode_designated.
Check rawCoqDynamicTruthTemplateOpaqueCode_wrong_predicate.
Check raw_codedFormulaShift_bottom.
Check raw_codedFormulaSubstitution_bottom.
Check RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax.
Check raw_coqDynamicTruthTemplateTernaryCommutingOnSyntax_of_deepClosed.
Check raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed.
Check rawCoqDynamicTruthTemplateTernary_shift_commuting_on_syntax.
Check rawCoqDynamicTruthTemplateTernary_opening_commuting_on_syntax.
Check raw_dynamicTruthCoqLowerApplication_functional.
Check raw_dynamicTruthSigmaRowDomainTemplate_quoted_code.
Check rawCoqDynamicTruthTemplateOpaqueShiftAt.
Check rawCoqDynamicTruthTemplateOpaqueOpeningAt.
Check rawCoqDynamicTruthTemplateDirectStructuralInputs.
Check rawCoqDynamicTruthSigmaDomainLeaf_opening_trace.
Check rawCoqDynamicTruthSigmaDomainLeaf_identifies_native_domain.
Check rawCoqDynamicTruthLowerPiAtomTemplate_code.
Check rawCoqDynamicTruthLowerPiAtomDirect_code.
Check rawCoqDynamicTruthTemplateTerm_syntax.
Check rawCoqDynamicTruthTemplateTerm_renamed_syntax.
Check rawCoqDynamicTruthTemplateTerm_opened_syntax.
Check rawCoqDynamicTruthLowerPiAtom_selector_trace.
Check RawCoqDynamicTruthLowerApplicationCompatibility.
Check rawCoqDynamicTruthLowerApplicationCompatibility_holds.
Check rawCoqDynamicTruthLowerApplication_selector_unique.
Check rawCoqDynamicTruthLowerPiAtom_identifies_native_application.
Check rawCoqDynamicTruthLowerPiAtom_native_application.
Check raw_coqDynamicTruthTemplateDirectStructuralInputs_exists.

Section ExactFieldAudit.

Variable M : RawPAModel.
Variable hPA : RawPASatisfies M.
Variable lowerLevel upperLevel lowerPiCode : M.
Variable selector : RawCodedTernaryApplicationSelector M lowerPiCode.
Variable commutingOnSyntax :
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    M lowerPiCode selector.
Variable package : RawCodedDynamicTruthTemplateNumeralTermPackage
  M lowerLevel upperLevel
  (rawCoqDynamicTruthTemplateOpaqueCode selector).

Let inputs : RawCodedTemplateDirectStructuralInputs M :=
  rawCoqDynamicTruthTemplateDirectStructuralInputs
    M hPA lowerLevel upperLevel lowerPiCode selector
    commutingOnSyntax package.

(** The record is directly accepted by the generic finite structural
    translator; no formula code is decoded at this boundary. *)
Check inputs : RawCodedTemplateDirectStructuralInputs M.

Check (rawCoqDynamicTruthTemplateOpaqueShiftAt
  M hPA lowerLevel upperLevel lowerPiCode selector
  commutingOnSyntax package)
  : forall depth predicate arguments,
      RawCodedFormulaShift M
        (rawNumeralValue M depth) (rawNumeralValue M 1)
        (rawStructuralTemplateFormulaWith M
          (rawCoqDynamicTruthTemplateNumeralSymbols package)
          (tfOpaque predicate arguments))
        (rawStructuralTemplateFormulaWith M
          (rawCoqDynamicTruthTemplateNumeralSymbols package)
          (templateFormulaRename (templateShiftRenamingAt depth)
            (tfOpaque predicate arguments))).

Check (rawCoqDynamicTruthTemplateOpaqueOpeningAt
  M hPA lowerLevel upperLevel lowerPiCode selector
  commutingOnSyntax package)
  : forall depth replacement predicate arguments,
      RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
        (rawStructuralTemplateTermWith M
          (rawCoqDynamicTruthTemplateNumeralSymbols package) replacement)
        (rawNumeralValue M depth)
        (rawStructuralTemplateFormulaWith M
          (rawCoqDynamicTruthTemplateNumeralSymbols package)
          (tfOpaque predicate arguments))
        (rawStructuralTemplateFormulaWith M
          (rawCoqDynamicTruthTemplateNumeralSymbols package)
          (templateFormulaSubst
            (templateOpeningSubstAt depth replacement)
            (tfOpaque predicate arguments))).

(** Exact source-code equation for the only opaque atom in the concrete
    dynamic-truth row. *)
Check (rawCoqDynamicTruthLowerPiAtomDirect_code
  M hPA lowerLevel upperLevel lowerPiCode selector
  commutingOnSyntax package)
  : rawDirectTemplateFormula inputs coqDynamicTruthLowerPiAtomTemplate =
      rawTernaryApplicationOutput selector
        (RawCodedSyntaxConstructors.PABoundedRawCodedSyntaxConstructors.rawTermVarCode
          M (rawNumeralValue M 9))
        (RawCodedSyntaxConstructors.PABoundedRawCodedSyntaxConstructors.rawTermVarCode
          M (rawNumeralValue M 1))
        (RawCodedSyntaxConstructors.PABoundedRawCodedSyntaxConstructors.rawTermVarCode
          M (rawNumeralValue M 0)).

(** The independent native row graph receives exactly that selected output. *)
Check (rawCoqDynamicTruthLowerPiAtom_native_application
  M hPA lowerLevel upperLevel lowerPiCode selector
  commutingOnSyntax package)
  : RawDynamicTruthCoqLowerApplication M lowerPiCode
      (rawDirectTemplateFormula inputs coqDynamicTruthLowerPiAtomTemplate).

Check (rawCoqDynamicTruthSigmaDomainLeaf_opening_trace
  M hPA lowerLevel upperLevel lowerPiCode selector
  commutingOnSyntax package)
  : RawCodedFormulaSingleSubstitution M
      (rawCoqDynamicTruthUpperNumeralCode package)
      (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode)
      (rawDirectTemplateFormula inputs
        coqDynamicTruthSigmaDomainLeafTemplate).

Check (rawCoqDynamicTruthSigmaDomainLeaf_identifies_native_domain
  M hPA lowerLevel upperLevel lowerPiCode selector
  commutingOnSyntax package)
  : forall domain,
      RawCodedFormulaSingleSubstitution M
        (rawCoqDynamicTruthUpperNumeralCode package)
        (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode)
        domain ->
      rawDirectTemplateFormula inputs
        coqDynamicTruthSigmaDomainLeafTemplate = domain.

End ExactFieldAudit.

Print Assumptions rawCoqDynamicTruthTemplateOpaqueCode_designated.
Print Assumptions raw_codedFormulaShift_bottom.
Print Assumptions raw_codedFormulaSubstitution_bottom.
Print Assumptions raw_dynamicTruthCoqLowerApplication_functional.
Print Assumptions raw_dynamicTruthSigmaRowDomainTemplate_quoted_code.
Print Assumptions rawCoqDynamicTruthTemplateOpaqueShiftAt.
Print Assumptions rawCoqDynamicTruthTemplateOpaqueOpeningAt.
Print Assumptions rawCoqDynamicTruthTemplateDirectStructuralInputs.
Print Assumptions rawCoqDynamicTruthSigmaDomainLeaf_opening_trace.
Print Assumptions rawCoqDynamicTruthSigmaDomainLeaf_identifies_native_domain.
Print Assumptions rawCoqDynamicTruthLowerPiAtomDirect_code.
Print Assumptions rawCoqDynamicTruthTemplateTerm_syntax.
Print Assumptions rawCoqDynamicTruthTemplateTerm_renamed_syntax.
Print Assumptions rawCoqDynamicTruthTemplateTerm_opened_syntax.
Print Assumptions rawCoqDynamicTruthLowerPiAtom_selector_trace.
Print Assumptions rawCoqDynamicTruthLowerApplicationCompatibility_holds.
Print Assumptions rawCoqDynamicTruthLowerApplication_selector_unique.
Print Assumptions rawCoqDynamicTruthLowerPiAtom_identifies_native_application.
Print Assumptions rawCoqDynamicTruthLowerPiAtom_native_application.
Print Assumptions raw_coqDynamicTruthTemplateDirectStructuralInputs_exists.
Print Assumptions
  raw_coqDynamicTruthTemplateTernaryCommutingOnSyntax_of_deepClosed.
Print Assumptions
  raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed.

End PABoundedRawCodedDynamicTruthTemplateDirectInputsAudit.
