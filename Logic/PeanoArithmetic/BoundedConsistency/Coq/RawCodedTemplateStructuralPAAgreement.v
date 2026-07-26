(**
  Ordinary-PA agreement for the structural template translation.

  The structural translator has two client-selected cases: named parameters
  and opaque predicate applications.  Neither case occurs in the image of
  ordinary PA syntax.  Consequently its transparent recursion agrees
  definitionally, constructor by constructor, with the established raw
  quotation of PA terms and formulas.  This small bridge discharges the
  agreement premise used when a template proof contains ordinary PA axioms.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedTemplateSyntax
  RawCodedTemplatePAEmbedding RawCodedTemplateStructuralTranslation.

Module PABoundedRawCodedTemplateStructuralPAAgreement.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateStructuralTranslation.

(** Parameter and opaque-symbol choices are irrelevant on embedded PA
    terms.  Stating the lemma for the transparent [With] function keeps it
    independent of all represented shift/opening witnesses. *)
Lemma rawStructuralTemplateTermWith_embedPA : forall
    (M : RawPAModel) (symbols : RawCodedTemplateStructuralSymbols M)
    input,
  rawStructuralTemplateTermWith M symbols (embedPATerm input) =
  rawQuotedTermCode M input.
Proof.
  intros M symbols input.
  induction input; cbn
    [embedPATerm rawStructuralTemplateTermWith rawQuotedTermCode].
  - reflexivity.
  - reflexivity.
  - now rewrite IHinput.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
Qed.

(** The corresponding formula theorem follows by the same transparent
    structural recursion. *)
Lemma rawStructuralTemplateFormulaWith_embedPA : forall
    (M : RawPAModel) (symbols : RawCodedTemplateStructuralSymbols M)
    input,
  rawStructuralTemplateFormulaWith M symbols (embedPAFormula input) =
  rawQuotedFormulaCode M input.
Proof.
  intros M symbols input.
  induction input; cbn
    [embedPAFormula rawStructuralTemplateFormulaWith rawQuotedFormulaCode].
  - now rewrite !rawStructuralTemplateTermWith_embedPA.
  - reflexivity.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput.
  - now rewrite IHinput.
Qed.

Corollary rawStructuralTemplateTerm_embedPA : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) input,
  rawStructuralTemplateTerm inputs (embedPATerm input) =
  rawQuotedTermCode M input.
Proof.
  intros M inputs input.
  unfold rawStructuralTemplateTerm.
  apply rawStructuralTemplateTermWith_embedPA.
Qed.

Corollary rawStructuralTemplateFormula_embedPA : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) input,
  rawStructuralTemplateFormula inputs (embedPAFormula input) =
  rawQuotedFormulaCode M input.
Proof.
  intros M inputs input.
  unfold rawStructuralTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

(** Package the two equations in precisely the interface consumed by
    [RawCodedTemplatePAEmbedding]. *)
Theorem rawStructuralTemplatePAAgreement : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateStructuralInputs M),
  RawCodedTemplatePAAgreement M
    (rawStructuralTemplateTranslation M hPA inputs).
Proof.
  intros M hPA inputs.
  constructor.
  - apply rawStructuralTemplateTerm_embedPA.
  - apply rawStructuralTemplateFormula_embedPA.
Qed.

End PABoundedRawCodedTemplateStructuralPAAgreement.
