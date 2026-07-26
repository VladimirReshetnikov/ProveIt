(** Kernel-facing audit for the two dynamic-truth numeral parameters. *)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation RawCodedTemplateNumeralParameters
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthTemplateNumeralParameters.

Module PABoundedRawCodedDynamicTruthTemplateNumeralParametersAudit.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthTemplateNumeralParameters.

Check coqDynamicTruthParameterSelect.
Check coqDynamicTruthParameterSelect_lower.
Check coqDynamicTruthParameterSelect_upper.
Check rawCoqDynamicTruthTemplateNumeralParameters.
Check rawCoqDynamicTruthTemplateNumeralParameters_lower_bound.
Check rawCoqDynamicTruthTemplateNumeralParameters_upper_bound.
Check rawCoqDynamicTruthTemplateNumeralParameters_lower_code.
Check rawCoqDynamicTruthTemplateNumeralParameters_upper_code.
Check raw_coqDynamicTruthTemplateNumeralParameters_exists.

Check RawCodedDynamicTruthTemplateNumeralTermPackage.
Check rawCoqDynamicTruthTermPackage_parameters.
Check rawCoqDynamicTruthTermPackage_lower_bound.
Check rawCoqDynamicTruthTermPackage_upper_bound.
Check rawCoqDynamicTruthTermPackage_traces.
Check rawCoqDynamicTruthTemplateNumeralTermPackage.
Check raw_coqDynamicTruthTemplateNumeralTermPackage_exists.
Check rawCoqDynamicTruthTemplateNumeralSymbols.
Check rawCoqDynamicTruthLowerNumeralCode.
Check rawCoqDynamicTruthUpperNumeralCode.
Check rawCoqDynamicTruthLowerNumeralCode_valid.
Check rawCoqDynamicTruthUpperNumeralCode_valid.
Check rawCoqDynamicTruthTemplateTermShiftAt.
Check rawCoqDynamicTruthTemplateTermOpeningAt.

Section DirectTermFieldAudit.

Variable M : RawPAModel.
Variable lowerLevel upperLevel : M.
Variable opaqueCode : TemplatePredicateName -> list M -> M.
Variable package : RawCodedDynamicTruthTemplateNumeralTermPackage
  M lowerLevel upperLevel opaqueCode.

(** The selected parameter codes really represent the two arbitrary carrier
    levels named by the concrete template. *)
Check (rawCoqDynamicTruthLowerNumeralCode_valid
  M lowerLevel upperLevel opaqueCode package)
  : RawCodedNumeralTermCode.PABoundedRawCodedNumeralTermCode.RawNumeralTermCodeAt
      M lowerLevel (rawCoqDynamicTruthLowerNumeralCode package).

Check (rawCoqDynamicTruthUpperNumeralCode_valid
  M lowerLevel upperLevel opaqueCode package)
  : RawCodedNumeralTermCode.PABoundedRawCodedNumeralTermCode.RawNumeralTermCodeAt
      M upperLevel (rawCoqDynamicTruthUpperNumeralCode package).

(** These are definitionally the two term fields required by the direct
    structural input record. *)
Check (rawCoqDynamicTruthTemplateTermShiftAt
  M lowerLevel upperLevel opaqueCode package)
  : forall depth input,
      RawCodedTermShift M
        (rawNumeralValue M depth) (rawNumeralValue M 1)
        (rawStructuralTemplateTermWith M
          (rawCoqDynamicTruthTemplateNumeralSymbols package) input)
        (rawStructuralTemplateTermWith M
          (rawCoqDynamicTruthTemplateNumeralSymbols package)
          (templateTermRename (templateShiftRenamingAt depth) input)).

Check (rawCoqDynamicTruthTemplateTermOpeningAt
  M lowerLevel upperLevel opaqueCode package)
  : forall depth replacement input,
      RawCodedFormulaSubstitutionAtom M
        (rawStructuralTemplateTermWith M
          (rawCoqDynamicTruthTemplateNumeralSymbols package) replacement)
        (rawNumeralValue M depth)
        (rawStructuralTemplateTermWith M
          (rawCoqDynamicTruthTemplateNumeralSymbols package) input)
        (rawStructuralTemplateTermWith M
          (rawCoqDynamicTruthTemplateNumeralSymbols package)
          (templateTermSubst
            (templateOpeningSubstAt depth replacement) input)).

End DirectTermFieldAudit.

Print Assumptions coqDynamicTruthParameterSelect_lower.
Print Assumptions coqDynamicTruthParameterSelect_upper.
Print Assumptions rawCoqDynamicTruthTemplateNumeralParameters.
Print Assumptions raw_coqDynamicTruthTemplateNumeralParameters_exists.
Print Assumptions rawCoqDynamicTruthTemplateNumeralTermPackage.
Print Assumptions raw_coqDynamicTruthTemplateNumeralTermPackage_exists.
Print Assumptions rawCoqDynamicTruthLowerNumeralCode_valid.
Print Assumptions rawCoqDynamicTruthUpperNumeralCode_valid.
Print Assumptions rawCoqDynamicTruthTemplateTermShiftAt.
Print Assumptions rawCoqDynamicTruthTemplateTermOpeningAt.

End PABoundedRawCodedDynamicTruthTemplateNumeralParametersAudit.
