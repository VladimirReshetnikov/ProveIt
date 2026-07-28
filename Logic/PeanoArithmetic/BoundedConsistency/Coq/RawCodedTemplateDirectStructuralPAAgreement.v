(**
  Ordinary-PA agreement for the direct structural template translation.

  Direct structural inputs differ from finite structural inputs only at
  opaque template leaves: they provide represented shift and opening traces
  instead of metatheoretic operation trees.  Embedded ordinary PA syntax has
  no parameter or opaque constructors, so the same transparent recursion
  theorem proves agreement with the established raw PA quotation.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplatePAEmbedding
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateDirectStructuralTranslation.

Module PABoundedRawCodedTemplateDirectStructuralPAAgreement.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.

(** Package the constructor-by-constructor equations in the interface used
    by the finite proof-tree compiler.  The proof deliberately unfolds only
    the direct wrappers; the generic [With] lemmas then make the argument
    independent of the client-selected parameter and opaque symbols. *)
Theorem rawDirectStructuralTemplatePAAgreement : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedTemplatePAAgreement M
    (rawDirectStructuralTemplateTranslation M hPA inputs).
Proof.
  intros M hPA inputs.
  constructor.
  - intro input.
    unfold rawDirectStructuralTemplateTranslation, rawDirectTemplateTerm.
    apply rawStructuralTemplateTermWith_embedPA.
  - intro input.
    unfold rawDirectStructuralTemplateTranslation, rawDirectTemplateFormula.
    apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

End PABoundedRawCodedTemplateDirectStructuralPAAgreement.
