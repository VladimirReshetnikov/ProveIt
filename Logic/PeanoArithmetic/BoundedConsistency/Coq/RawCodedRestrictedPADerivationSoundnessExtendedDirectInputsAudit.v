(** Kernel-facing audit for the extensible mixed-arity direct inputs. *)

From Stdlib Require Import List.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputsAudit.

Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.

Check RawCoqRestrictedPAOpaqueTailDirectSelector.
Check rawCoqRestrictedPAOpaqueTailOutput.
Check rawCoqRestrictedPAOpaqueTailShiftAt.
Check rawCoqRestrictedPAOpaqueTailOpeningAt.
Check rawCoqRestrictedPATernaryDirectSelectorCode.
Check rawCoqRestrictedPATernaryDirectSelectorCode_shiftAt.
Check rawCoqRestrictedPATernaryDirectSelectorCode_openingAt.
Check rawCoqRestrictedPATernaryPairTailCode.
Check rawCoqRestrictedPATernaryPairTailDirectSelector.
Check rawCoqRestrictedPADerivationSoundnessExtendedOpaqueCode.
Check rawCoqRestrictedPADerivationSoundnessExtendedTemplateSymbols.
Check rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerm_symbols.
Check rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerms_symbols.
Check
  rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs.
Check rawCoqRestrictedPADerivationSoundnessExtendedDirectTerm_view.
Check rawCoqRestrictedPADerivationSoundnessExtendedDirectFormula_view.
Check rawCoqRestrictedPADerivationSoundnessExtendedContextTruthLeaf_view.
Check
  rawCoqRestrictedPADerivationSoundnessExtendedConclusionTruthLeaf_view.
Check rawCoqRestrictedPADerivationSoundnessExtendedTailLeaf_view.
Check coqRestrictedPALowerPiTruthPredicateName.
Check coqRestrictedPALowerSigmaTruthPredicateName.

Section ExactSlots.

Variable M : RawPAModel.
Variable hPA : RawPASatisfies M.
Variable parameters : RawCodedTemplateNumeralParameters M.
Variable contextTruth conclusionTruth :
  RawCoqRestrictedPATruthDirectSelector M parameters.
Variable lowerPiCode lowerSigmaCode : M.
Variable lowerPiSelector :
  RawCodedTernaryApplicationSelector M lowerPiCode.
Variable lowerSigmaSelector :
  RawCodedTernaryApplicationSelector M lowerSigmaCode.
Variable lowerPiCommuting :
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    M lowerPiCode lowerPiSelector.
Variable lowerSigmaCommuting :
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
    M lowerSigmaCode lowerSigmaSelector.

Let tail :=
  rawCoqRestrictedPATernaryPairTailDirectSelector
    M hPA parameters lowerPiCode lowerSigmaCode
    lowerPiSelector lowerSigmaSelector
    lowerPiCommuting lowerSigmaCommuting.

Let inputs :=
  rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
    M hPA parameters contextTruth conclusionTruth tail.

Check inputs : RawCodedTemplateDirectStructuralInputs M.

(** The two original five-argument slots retain their exact outputs. *)
Goal forall first second third fourth fifth,
  rawDirectTemplateFormula inputs
    (tfOpaque 0 [first; second; third; fourth; fifth]) =
  rawCoqRestrictedPATruthDirectOutput contextTruth
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters first)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters second)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters third)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters fourth)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters fifth).
Proof.
  apply
    rawCoqRestrictedPADerivationSoundnessExtendedContextTruthLeaf_view.
Qed.

Goal forall first second third fourth fifth,
  rawDirectTemplateFormula inputs
    (tfOpaque 1 [first; second; third; fourth; fifth]) =
  rawCoqRestrictedPATruthDirectOutput conclusionTruth
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters first)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters second)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters third)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters fourth)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters fifth).
Proof.
  apply
    rawCoqRestrictedPADerivationSoundnessExtendedConclusionTruthLeaf_view.
Qed.

(** Global slots two and three are independent ternary applications. *)
Goal forall first second third,
  rawDirectTemplateFormula inputs
    (tfOpaque coqRestrictedPALowerPiTruthPredicateName
      [first; second; third]) =
  rawTernaryApplicationOutput lowerPiSelector
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters first)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters second)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters third).
Proof.
  intros first second third.
  etransitivity.
  - apply
      rawCoqRestrictedPADerivationSoundnessExtendedTailLeaf_view.
  - reflexivity.
Qed.

Goal forall first second third,
  rawDirectTemplateFormula inputs
    (tfOpaque coqRestrictedPALowerSigmaTruthPredicateName
      [first; second; third]) =
  rawTernaryApplicationOutput lowerSigmaSelector
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters first)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters second)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters third).
Proof.
  intros first second third.
  etransitivity.
  - apply
      rawCoqRestrictedPADerivationSoundnessExtendedTailLeaf_view.
  - reflexivity.
Qed.

End ExactSlots.

Print Assumptions rawCoqRestrictedPATernaryDirectSelectorCode_shiftAt.
Print Assumptions rawCoqRestrictedPATernaryDirectSelectorCode_openingAt.
Print Assumptions rawCoqRestrictedPATernaryPairTailDirectSelector.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessExtendedTemplateTerm_symbols.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessExtendedContextTruthLeaf_view.
Print Assumptions
  rawCoqRestrictedPADerivationSoundnessExtendedTailLeaf_view.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputsAudit.
