(** Atomic adequacy supplied by every coded template translation. *)

From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaShiftSourceAtomicAdequacy
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler.

Module PABoundedRawCodedTemplateFormulaAtomicAdequacy.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaShiftSourceAtomicAdequacy.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.

(** The unit-shift trace in the translation contract witnesses adequacy of
    its source.  No structural interpretation or PA-quotation agreement is
    needed, so the result also applies to genuinely nonstandard templates. *)
Theorem raw_codedTemplateFormula_atomically_adequate_core : forall
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

End PABoundedRawCodedTemplateFormulaAtomicAdequacy.
