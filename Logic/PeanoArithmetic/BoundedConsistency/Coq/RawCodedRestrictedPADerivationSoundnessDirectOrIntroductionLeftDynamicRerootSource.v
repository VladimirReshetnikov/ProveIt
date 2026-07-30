(**
  A fixed PA source for carrier-parametric Or-I-left restriction rerooting.

  The direct recursive-child law contains one named hierarchy-level
  parameter.  Abstracting that parameter produces an ordinary PA formula
  with a fresh variable zero.  The other free variables are shifted past the
  new variable, so universally quantifying the body binds exactly the level
  and leaves the displayed proof data free.

  This module deliberately separates syntax from arithmetic validity.  It
  proves that the abstraction lies in ordinary PA syntax and that represented
  All-E at the direct carrier term opens it to the exact recursive-child law.
  The remaining substantive obligation is now one honest theorem of PA:

      PA |- forall level, dynamicRestrictedReroot(level).

  No standardness premise and no already-coded proof root occur here.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateParameterAbstraction
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootSource.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.

Definition
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyTemplate
    : TemplateFormula :=
  templateFormulaAbstractParameter
    coqRestrictedPASoundnessLowerLevelParameterName
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootLawTemplate.

(** The fallback is intentionally absurd.  The following computation theorem
    proves that it is unreachable for this source and exposes the exact PA
    formula selected by reification without carrying an existential witness
    through every downstream definition. *)
Definition
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyFormula
    : formula :=
  match templateFormulaAsPAFormula
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyTemplate
  with
  | Some output => output
  | None => pBot
  end.

Definition
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceFormula
    : formula :=
  pAll
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyFormula.

Lemma
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSource_reifies :
  templateFormulaAsPAFormula
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyTemplate =
  Some
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyFormula.
Proof.
  vm_compute. reflexivity.
Qed.

Theorem
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSource_embed :
  embedPAFormula
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyFormula =
  coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyTemplate.
Proof.
  apply templateFormulaAsPAFormula_sound.
  exact
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSource_reifies.
Qed.

(** This is the key exact syntax equation.  It is stronger than agreement of
    denotations: represented substitution literally targets the direct law
    already consumed by the recursive-child compiler. *)
Theorem
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSource_open :
  templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
    (embedPAFormula
      coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyFormula) =
  coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootLawTemplate.
Proof.
  rewrite
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSource_embed.
  apply templateFormulaAbstractParameter_open.
Qed.

Lemma
    rawDirect_dynamicRestrictedRerootSourceBody_agreement : forall
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
    (embedPAFormula
      coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyFormula) =
  rawQuotedFormulaCode M
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyFormula.
Proof.
  intros M inputs.
  unfold rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

(** An arbitrary direct level term, including one denoting a nonstandard
    model element, supplies a represented single-substitution trace from the
    fixed PA source body to the exact direct reroot law. *)
Theorem
    rawDirect_dynamicRestrictedRerootSource_substitution : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedFormulaSingleSubstitution M
    (rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm)
    (rawQuotedFormulaCode M
      coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyFormula)
    (rawDirectTemplateFormula inputs
      coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootLawTemplate).
Proof.
  intros M hPA inputs.
  pose proof (rawDirectTemplateFormula_open M hPA inputs
    (embedPAFormula
      coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSourceBodyFormula)
    coqRestrictedPASoundnessLowerLevelTerm) as hopen.
  rewrite rawDirect_dynamicRestrictedRerootSourceBody_agreement in hopen.
  rewrite
    coqRestrictedPADirectOrIntroductionLeftDynamicRestrictedRerootSource_open
    in hopen.
  exact hopen.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootSource.
