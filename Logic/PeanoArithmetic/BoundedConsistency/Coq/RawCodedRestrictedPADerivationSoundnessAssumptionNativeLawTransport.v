(**
  Carrier-code transport from the native Assumption law to its public leaf.

  The transparent context predicate uses the documented reversed ternary
  argument order, and its innermost conclusion leaf fixes both hierarchy
  arguments to zero.  Native truth selectors ignore those two displayed
  hierarchy arguments.  The already-audited context and conclusion leaf
  equations therefore identify the complete transparent law with the public
  Assumption semantic residual, literally at carrier formula-code level.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateTernaryApplication
  RawCodedDynamicContextTruthSelector
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessAssumptionContextTruthExpansion
  RawCodedRestrictedPADerivationSoundnessAssumptionWitnessShapes
  RawCodedRestrictedPADerivationSoundnessAssumptionTenWitnessComposition.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionNativeLawTransport.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionContextTruthExpansion.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionWitnessShapes.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionTenWitnessComposition.

Theorem raw_coqRestrictedPADirectAssumptionNativeLaw_code : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode)
    (contextSelector : RawCodedTernaryApplicationSelector M
      (rawDynamicContextAllSigmaCode sigmaSelector)),
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput sigmaSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAContextTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput contextSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)) ->
  rawDirectTemplateFormula inputs
    coqRestrictedPADirectAssumptionMembershipTruthLawTemplate =
  rawDirectTemplateFormula inputs
    coqRestrictedPADirectAssumptionNativeMembershipTruthLawTemplate.
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs
    sigmaCode sigmaSelector contextSelector hconclusion hcontext.
  unfold coqRestrictedPADirectAssumptionMembershipTruthLawTemplate,
    coqRestrictedPADirectAssumptionNativeMembershipTruthLawTemplate.
  cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith].
  f_equal.
  - exact (raw_coqRestrictedPAContextTruthLeaf_expansion
      M hPA parameters contextTruth conclusionTruth
      sigmaCode sigmaSelector contextSelector hconclusion hcontext
      coqRestrictedPASoundnessLowerLevelTerm
      coqRestrictedPASoundnessUpperLevelTerm
      coqRestrictedPADirectAssumptionWitnessContextTerm
      (ttVar 9) (ttVar 8)).
  - f_equal.
    unfold coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate,
      coqRestrictedPADirectAssumptionNativeWitnessFormulaTruthTemplate.
    rewrite (hconclusion
      coqRestrictedPASoundnessLowerLevelTerm
      coqRestrictedPASoundnessUpperLevelTerm
      coqRestrictedPADirectAssumptionWitnessFormulaTerm
      (ttVar 9) (ttVar 8)).
    rewrite (hconclusion ttZero ttZero
      coqRestrictedPADirectAssumptionWitnessFormulaTerm
      (ttVar 9) (ttVar 8)).
    reflexivity.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessAssumptionNativeLawTransport.
