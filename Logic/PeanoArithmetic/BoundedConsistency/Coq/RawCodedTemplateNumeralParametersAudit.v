(** Kernel-facing audit for numeral-parameter template term traces. *)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax RawCodedTemplateStructuralTranslation
  RawCodedTemplateNumeralParameters.

Module PABoundedRawCodedTemplateNumeralParametersAudit.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.

Check RawCodedTemplateNumeralParameters.
Check rawNumeralTemplateParameterBound.
Check rawNumeralTemplateParameterCode.
Check rawNumeralTemplateParameter_valid.
Check rawNumeralTemplateSymbols.

Check templateShiftRenamingBy.
Check templateShiftRenamingBy_zero_amount.
Check templateShiftRenamingBy_one.
Check templateOpeningSubstAt_below.
Check templateOpeningSubstAt_at.
Check templateOpeningSubstAt_above.

Check raw_numeralTemplateTerm_shift_by.
Check raw_numeralTemplateTerm_shift.
Check raw_numeralTemplateTerm_opening_variable.
Check raw_numeralTemplateTerm_opening.
Check raw_numeralTemplateTerm_substitutionAtom.

Check RawCodedTemplateTermTraceInputs.
Check rawTemplateTermTrace_shiftAt.
Check rawTemplateTermTrace_openAt.
Check rawNumeralTemplateTermTraceInputs.

Section ExactStructuralFieldAudit.

Variable M : RawPAModel.
Variable hPA : RawPASatisfies M.
Variable parameters : RawCodedTemplateNumeralParameters M.
Variable opaqueCode : TemplatePredicateName -> list M -> M.

Let symbols := rawNumeralTemplateSymbols M parameters opaqueCode.
Let traces := rawNumeralTemplateTermTraceInputs
  M hPA parameters opaqueCode.

(** These two checks deliberately repeat the types of the corresponding
    fields in [RawCodedTemplateStructuralInputs]. *)
Check (rawTemplateTermTrace_shiftAt traces)
  : forall depth input,
      RawCodedFormulaOperations.PABoundedRawCodedFormulaOperations.RawCodedTermShift
        M (rawNumeralValue M depth) (rawNumeralValue M 1)
        (rawStructuralTemplateTermWith M symbols input)
        (rawStructuralTemplateTermWith M symbols
          (templateTermRename (templateShiftRenamingAt depth) input)).

Check (rawTemplateTermTrace_openAt traces)
  : forall depth replacement input,
      RawCodedFormulaOperations.PABoundedRawCodedFormulaOperations.RawCodedFormulaSubstitutionAtom
        M (rawStructuralTemplateTermWith M symbols replacement)
        (rawNumeralValue M depth)
        (rawStructuralTemplateTermWith M symbols input)
        (rawStructuralTemplateTermWith M symbols
          (templateTermSubst
            (templateOpeningSubstAt depth replacement) input)).

End ExactStructuralFieldAudit.

Print Assumptions templateShiftRenamingBy_zero_amount.
Print Assumptions templateShiftRenamingBy_one.
Print Assumptions templateOpeningSubstAt_below.
Print Assumptions templateOpeningSubstAt_at.
Print Assumptions templateOpeningSubstAt_above.
Print Assumptions raw_numeralTemplateTerm_shift_by.
Print Assumptions raw_numeralTemplateTerm_shift.
Print Assumptions raw_numeralTemplateTerm_opening_variable.
Print Assumptions raw_numeralTemplateTerm_opening.
Print Assumptions raw_numeralTemplateTerm_substitutionAtom.
Print Assumptions rawNumeralTemplateTermTraceInputs.

End PABoundedRawCodedTemplateNumeralParametersAudit.
