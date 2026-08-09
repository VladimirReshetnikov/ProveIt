(** Specialized, computation-free support for the opened And-I source. *)

From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateParameterAbstraction
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationMachinery.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.

(** Certificates importing this compatibility support receive both the generic
    checker operations and the nine component constants owned by validity. *)
Export
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationMachinery.
Export
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageValidity.
Export PABoundedRawCodedTemplateParameterAbstraction.
Export PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.

Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.

Definition
    coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker
    (input : TemplateFormula) : bool :=
  templateFormulaHasPAReificationAfterAbstracting
    coqRestrictedPASoundnessLowerLevelParameterName input.

Lemma
    coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker_sound
    : forall depth input,
  coqRestrictedPADirectAndIntroductionOpenedCoverageReificationChecker input =
    true ->
  exists output,
    templateFormulaAsPAFormula
      (templateFormulaAbstractParameterAt
        coqRestrictedPASoundnessLowerLevelParameterName depth input) =
    Some output.
Proof.
  intros depth input hsuccess.
  apply templateFormulaHasPAReificationAfterAbstracting_sound.
  exact hsuccess.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationSupport.
