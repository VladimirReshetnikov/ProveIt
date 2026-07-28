(**
  Discharge the final bridge fields-head adequacy premise.

  The growable universal-soundness bridge keeps atomic adequacy of the
  projected restricted-proof fields explicit.  That premise is useful at
  the general transport seam, but the final staged graph already carries the
  numeral witness from which adequacy of this exact fields head was proved
  unconditionally.  This file applies that syntax theorem and changes
  nothing else about the growable endpoint.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateStructuralTranslation
  RawCodedPAProvability
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridge
  RawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy.

Module
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeAdequacy.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridge.
Import
  PABoundedRawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy.

(** Exact corollary of the growable endpoint.  The only omitted input is
    [RawCodedFormulaAtomicallyAdequate] for the projected-fields head; the
    unconditional compiler obtains it from the same graph trace and staged
    prerequisites supplied below. *)
Theorem
    raw_dynamicTruthNativeFinalGrowingUniversalSoundnessBridge_of_ordinary_complete_fields
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M)
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      soundnessCertificate,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness ->
  RawCodedPAProofOf M
    (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
    soundnessCertificate ->
  rawStructuralTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
  RawDynamicTruthNativeFinalConsistencyFromUniversalSoundnessCompiler
    M inputs ->
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeAt
    M inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode.
Proof.
  intros M hPA inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    soundnessCertificate htrace hprerequisites hsoundnessCertificate
    hlevel hconsistencyCompiler.
  pose proof
    (raw_dynamicTruthNativeFinalBridgeFieldsHeadAdequacyCompiler M hPA
      tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      htrace hprerequisites)
    as hfieldsAdequate.
  exact
    (raw_dynamicTruthNativeFinalGrowingUniversalSoundnessBridge_of_ordinary
      M hPA inputs tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      soundnessCertificate htrace hprerequisites hsoundnessCertificate
      hfieldsAdequate hlevel hconsistencyCompiler).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeAdequacy.
