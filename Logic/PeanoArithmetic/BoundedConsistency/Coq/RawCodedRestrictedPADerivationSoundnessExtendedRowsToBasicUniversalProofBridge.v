(**
  Compile rule cases with extended rows and return the basic soundness code.

  Rule-case compilation deliberately uses two extra opaque selectors for the
  predecessor dynamic-truth rows.  The synchronized carried-consistency
  package, on the other hand, retains the original two-selector structural
  inputs.  The opaque-tail invariance module proves both equalities needed to
  cross that boundary: equality of the final universal soundness code and
  equality of the carrier-body code on which the closure remainder depends.

  This module packages those equalities around the ordinary V2 dispatcher.
  Its output is therefore already indexed by the basic carried-input code;
  downstream consistency bridges never need to mention or identify the two
  structurally different input records.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessExtendedDirectInputs
  RawCodedRestrictedPADerivationSoundnessExtendedRowIdentification
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareDispatcherIntegration
  RawCodedRestrictedPADerivationSoundnessUniversalDirectCodeTailInvariance.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedRowsToBasicUniversalProofBridge.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedRowIdentification.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectBottomAdmissibilityAwareDispatcherIntegration.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessUniversalDirectCodeTailInvariance.

(** The generic tail form is the reusable theorem.  It assumes no semantic
    property of the additional opaque selectors: all semantic work remains
    honestly concentrated in the V2 rule-case compiler. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_basic_of_extended_remaining_v2
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      (tail : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters),
  RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler M hPA
      (rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth tail) ->
  forall replacement axiom closureCount,
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder M
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      replacement axiom closureCount ->
  exists soundnessCertificate : M,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
        (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth))
      soundnessCertificate.
Proof.
  intros M hPA parameters contextTruth conclusionTruth tail
    hremaining replacement axiom closureCount hremainder.
  pose proof (proj2
    (raw_coqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder_extended_iff_basic
      M hPA parameters contextTruth conclusionTruth tail
      replacement axiom closureCount) hremainder) as hextendedRemainder.
  destruct
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_remaining_v2_after_orIntroductionLeft
      M hPA
      (rawCoqRestrictedPADerivationSoundnessExtendedDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth tail)
      hremaining replacement axiom closureCount hextendedRemainder)
    as [soundnessCertificate hcertificate].
  exists soundnessCertificate.
  exact
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_basic_of_extended
      M hPA parameters contextTruth conclusionTruth tail
      soundnessCertificate hcertificate).
Qed.

(** Concrete specialization to the predecessor Pi/Sigma rows installed by
    the aligned native constructor.  Bounds and row-identification equations
    are intentionally absent: they belong to construction of the V2
    compiler, not to this code-and-closure transport step. *)
Corollary
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_basic_of_extended_rows_remaining_v2
    : forall (M : RawPAModel) (hPA : RawPASatisfies M)
      (parameters : RawCodedTemplateNumeralParameters M)
      (contextTruth conclusionTruth :
        RawCoqRestrictedPATruthDirectSelector M parameters)
      lowerPiCode lowerSigmaCode
      (lowerPiSelector :
        RawCodedTernaryApplicationSelector M lowerPiCode)
      (lowerSigmaSelector :
        RawCodedTernaryApplicationSelector M lowerSigmaCode)
      (lowerPiCommuting :
        RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
          M lowerPiCode lowerPiSelector)
      (lowerSigmaCommuting :
        RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
          M lowerSigmaCode lowerSigmaSelector),
  RawCoqRestrictedPADirectRemainingRuleCasesV2StandardTailCompiler M hPA
      (rawCoqRestrictedPAExtendedRowsInputs
        M hPA parameters contextTruth conclusionTruth
        lowerPiCode lowerSigmaCode lowerPiSelector lowerSigmaSelector
        lowerPiCommuting lowerSigmaCommuting) ->
  forall replacement axiom closureCount,
  RawCoqRestrictedPADerivationSoundnessStrongPrefixDirectClosureRemainder M
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      replacement axiom closureCount ->
  exists soundnessCertificate : M,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
        (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth))
      soundnessCertificate.
Proof.
  intros M hPA parameters contextTruth conclusionTruth
    lowerPiCode lowerSigmaCode lowerPiSelector lowerSigmaSelector
    lowerPiCommuting lowerSigmaCommuting hremaining
    replacement axiom closureCount hremainder.
  unfold rawCoqRestrictedPAExtendedRowsInputs in hremaining.
  exact
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_basic_of_extended_remaining_v2
      M hPA parameters contextTruth conclusionTruth
      (rawCoqRestrictedPAExtendedRowsTail
        M hPA parameters lowerPiCode lowerSigmaCode
        lowerPiSelector lowerSigmaSelector
        lowerPiCommuting lowerSigmaCommuting)
      hremaining replacement axiom closureCount hremainder).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedRowsToBasicUniversalProofBridge.
