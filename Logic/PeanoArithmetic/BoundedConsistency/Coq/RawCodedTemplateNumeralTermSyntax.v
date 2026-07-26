(**
  Honest syntax for structurally interpreted numeral-parameter terms.

  [RawCodedTemplateNumeralParameters] constructs exact represented shifts
  and openings for every finite template term, including terms containing a
  numeral parameter whose code may be nonstandard.  The ternary-application
  selector is intentionally specified only on honest represented term
  syntax.  This module connects those interfaces without decoding a numeral
  code: shift a term by zero, observe that the structural target is unchanged,
  and use the target-syntax theorem carried by the represented trace.

  The result applies equally to renamed and opened template terms because
  those are still ordinary values of the finite [TemplateTerm] datatype.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication.

Module PABoundedRawCodedTemplateNumeralTermSyntax.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.

(** Every interpreted template term belongs to the selector's honest syntax
    domain.  The zero-shift trace is used only as an internal syntax
    certificate; no extensional formula operation is inferred from it. *)
Theorem raw_numeralTemplateTerm_syntax : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (parameters : RawCodedTemplateNumeralParameters M)
      opaqueCode input,
  RawCodedTermSyntax M
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode) input).
Proof.
  intros M hPA parameters opaqueCode input.
  pose proof (raw_numeralTemplateTerm_shift_by M hPA
    parameters opaqueCode 0 0 input) as hzeroShift.
  assert (hrenamed :
      templateTermRename (templateShiftRenamingBy 0 0) input = input).
  {
    rewrite <- (templateTermRename_id input) at 2.
    apply templateTermRename_ext. intro index.
    apply templateShiftRenamingBy_zero_amount.
  }
  rewrite hrenamed in hzeroShift.
  exact (raw_codedTermShift_target_syntax M hPA
    (rawNumeralValue M 0) (rawNumeralValue M 0)
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode) input)
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode) input)
    hzeroShift).
Qed.

(** Named forms used when filling the source and target syntax premises of
    a shift-commuting opaque application. *)
Corollary raw_numeralTemplateTerm_renamed_syntax : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (parameters : RawCodedTemplateNumeralParameters M)
      opaqueCode renaming input,
  RawCodedTermSyntax M
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode)
      (templateTermRename renaming input)).
Proof.
  intros. apply raw_numeralTemplateTerm_syntax. assumption.
Qed.

Corollary raw_numeralTemplateTerm_opened_syntax : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (parameters : RawCodedTemplateNumeralParameters M)
      opaqueCode substitution input,
  RawCodedTermSyntax M
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode)
      (templateTermSubst substitution input)).
Proof.
  intros. apply raw_numeralTemplateTerm_syntax. assumption.
Qed.

End PABoundedRawCodedTemplateNumeralTermSyntax.
