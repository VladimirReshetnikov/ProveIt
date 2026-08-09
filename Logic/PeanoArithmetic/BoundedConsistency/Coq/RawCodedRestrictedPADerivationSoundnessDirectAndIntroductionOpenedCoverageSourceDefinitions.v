(** Fixed PA source definitions for the opened And-I coverage law. *)

From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateParameterAbstraction
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceDefinitions.

Import PA.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.

Definition
    coqRestrictedPADirectAndIntroductionOpenedCoverageSourceBodyTemplate
    : TemplateFormula :=
  templateFormulaAbstractParameter
    coqRestrictedPASoundnessLowerLevelParameterName
    coqRestrictedPADirectAndIntroductionOpenedCoverageCompilerLawTemplate.

Definition
    coqRestrictedPADirectAndIntroductionOpenedCoverageSourceBodyFormula
    : formula :=
  match templateFormulaAsPAFormula
    coqRestrictedPADirectAndIntroductionOpenedCoverageSourceBodyTemplate with
  | Some output => output
  | None => pBot
  end.

Definition coqRestrictedPADirectAndIntroductionOpenedCoverageSourceFormula
    : formula :=
  pAll coqRestrictedPADirectAndIntroductionOpenedCoverageSourceBodyFormula.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageSourceDefinitions.
