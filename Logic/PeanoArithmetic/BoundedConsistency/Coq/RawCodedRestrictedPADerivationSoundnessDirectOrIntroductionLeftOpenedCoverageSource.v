(**
  A fixed PA source for the complete opened Or-I-left child interface.

  The opened structural law contains only ordinary arithmetic template
  syntax and the named lower-hierarchy parameter.  Abstracting that parameter
  therefore yields one reifiable PA formula.  Its universal closure can be
  proved once and instantiated, by represented All-E, at an arbitrary element
  of a possibly nonstandard PA model.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateParameterAbstraction
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageSource.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftRecursiveChildCompilation.

Definition
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceBodyTemplate
    : TemplateFormula :=
  templateFormulaAbstractParameter
    coqRestrictedPASoundnessLowerLevelParameterName
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawTemplate.

Definition
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceBodyFormula
    : formula :=
  match templateFormulaAsPAFormula
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceBodyTemplate
  with
  | Some output => output
  | None => pBot
  end.

Definition
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceFormula
    : formula :=
  pAll coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceBodyFormula.

Lemma
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSource_reifies :
  templateFormulaAsPAFormula
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceBodyTemplate =
  Some
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceBodyFormula.
Proof. vm_compute. reflexivity. Qed.

Theorem
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSource_embed :
  embedPAFormula
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceBodyFormula =
  coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceBodyTemplate.
Proof.
  apply templateFormulaAsPAFormula_sound.
  exact
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSource_reifies.
Qed.

Theorem
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSource_open :
  templateFormulaOpen coqRestrictedPASoundnessLowerLevelTerm
    (embedPAFormula
      coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceBodyFormula) =
  coqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawTemplate.
Proof.
  rewrite
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSource_embed.
  apply templateFormulaAbstractParameter_open.
Qed.

Lemma rawDirect_openedCoverageSourceBody_agreement : forall
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawDirectTemplateFormula inputs
    (embedPAFormula
      coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceBodyFormula) =
  rawQuotedFormulaCode M
    coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceBodyFormula.
Proof.
  intros M inputs.
  unfold rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

Theorem rawDirect_openedCoverageSource_substitution : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedFormulaSingleSubstitution M
    (rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm)
    (rawQuotedFormulaCode M
      coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceBodyFormula)
    (rawDirectTemplateFormula inputs
      coqRestrictedPADirectOrIntroductionLeftOpenedCoverageCompilerLawTemplate).
Proof.
  intros M hPA inputs.
  pose proof (rawDirectTemplateFormula_open M hPA inputs
    (embedPAFormula
      coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSourceBodyFormula)
    coqRestrictedPASoundnessLowerLevelTerm) as hopen.
  rewrite rawDirect_openedCoverageSourceBody_agreement in hopen.
  rewrite coqRestrictedPADirectOrIntroductionLeftOpenedCoverageSource_open
    in hopen.
  exact hopen.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftOpenedCoverageSource.
