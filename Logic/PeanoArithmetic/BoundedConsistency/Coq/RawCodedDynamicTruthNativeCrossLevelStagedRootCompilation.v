(**
  Carried certificate packaging for the staged native cross-level field.

  [RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation] already exposes
  the right dependency boundary: the preceding six-field master and the new
  local field share one witnessed PA context, and one trace-linked implication
  sends their conjunction to the complete coherence body.  That module uses
  the body to recover the historical two-guard interface.  The dependency-
  ordered successor needs one additional, purely structural endpoint: retain
  the witnessed context, close the same body under its three universal
  binders, and package an ordinary proof of the transform-selected field.

  This file performs exactly that packaging.  It neither strengthens nor
  discharges the remaining cross-level kernel implication.  In particular,
  no local proof is moved to the empty context and no semantic coherence fact
  is converted into represented proof syntax.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedProofEndpoints
  RawCodedProofBinaryConstructors
  RawCodedProofAndIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofAndIntroduction
  RawCodedPAProvability
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedTruthCertificateFinalProjection
  RawCodedTruthCertificateMasterIntroduction
  RawCodedPAAxiomContextSelfShift
  RawCodedPAProofAllNCarriedCertificates
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeCrossLevelPositiveGraph
  RawCodedDynamicTruthNativeCrossLevelProofCompilation
  RawCodedDynamicTruthNativeCrossLevelLeafRootCompilation
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthNativeCrossLevelStagedRootCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedTruthCertificateFinalProjection.
Import PABoundedRawCodedTruthCertificateMasterIntroduction.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedPAProofAllNCarriedCertificates.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelLeafRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.

(** Assemble the literal staged antecedent and apply the one existing kernel
    implication.  The returned root remains in the supplied witnessed base;
    the construction does not detour through either empty-base guard API. *)
Theorem raw_dynamicTruthNativeCrossLevelStagedBodyRoot_of_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot,
    RawDynamicTruthNativeCrossLevelLinkedRowsAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    RawDynamicTruthNativeCrossLevelStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot ->
    RawDynamicTruthNativeCrossLevelBodyRootOn M baseContext
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot hlinked hstaged.
  destruct hstaged as
    [hwitnessed hcurrentLocal hcurrentCross hcurrentShift
      hcurrentSubstitution hcurrentAxiom hcurrentFinal hnextLocal].
  pose proof (raw_codedPALocalProofOf_sixFieldMaster_intro M hPA
    baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    hcurrentLocal hcurrentCross hcurrentShift hcurrentSubstitution
    hcurrentAxiom hcurrentFinal) as hcurrentMaster.
  pose proof (raw_codedPALocalProofOf_andI M hPA baseContext
    (rawSixFieldMasterCode M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal)
    nextLocal
    (rawSixFieldMasterIntroductionRoot M baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot)
    nextLocalRoot hcurrentMaster hnextLocal) as hantecedent.
  assert (hstagedAgain :
      RawDynamicTruthNativeCrossLevelStagedPrerequisitesAt M
        witnessList baseContext
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal nextLocal
        currentLocalRoot currentCrossLevelRoot currentShiftRoot
        currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
        nextLocalRoot).
  { constructor; assumption. }
  destruct (hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot hlinked hstagedAgain) as
    [implicationRoot himplication].
  set (antecedent :=
    rawDynamicTruthNativeCrossLevelStagedAntecedentCode M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal).
  set (body := rawDynamicTruthNativeCrossLevelCoherenceBodyCode M
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi).
  exists (rawProofImpERoot M baseContext antecedent body
    implicationRoot
    (rawProofAndIRoot M baseContext
      (rawSixFieldMasterCode M
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal)
      nextLocal
      (rawSixFieldMasterIntroductionRoot M baseContext
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal
        currentLocalRoot currentCrossLevelRoot currentShiftRoot
        currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot)
      nextLocalRoot)).
  exact (raw_codedPALocalProofOf_impE M hPA baseContext
    antecedent body implicationRoot
    (rawProofAndIRoot M baseContext
      (rawSixFieldMasterCode M
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal)
      nextLocal
      (rawSixFieldMasterIntroductionRoot M baseContext
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal
        currentLocalRoot currentCrossLevelRoot currentShiftRoot
        currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot)
      nextLocalRoot)
    himplication hantecedent).
Qed.

(** ------------------------------------------------------------------
    Carried triple closure and exact ordinary-certificate packaging. *)

Definition rawDynamicTruthNativeCrossLevelStagedProofCertificate
    (M : RawPAModel) (witnessList baseContext body child : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0) witnessList
    (rawProofCloseNCarriedRoot M baseContext 3 body child).

Arguments rawDynamicTruthNativeCrossLevelStagedProofCertificate
  M witnessList baseContext body child : clear implicits.

Theorem
    raw_codedPAProofOf_dynamicTruthNativeCrossLevelField_of_body_root_on :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawDynamicTruthNativeCrossLevelBodyRootOn M baseContext
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthNativeCrossLevelCoherenceFieldCode M
        sigmaDomain piDomain currentSigma currentPi nextSigma nextPi)
      certificate.
Proof.
  intros M hPA witnessList baseContext
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
    hwitness [child [hcoverage hendpoint]].
  set (body := rawDynamicTruthNativeCrossLevelCoherenceBodyCode M
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi).
  pose proof (raw_codedPAAxiomWitnessContext_selfShift M hPA
    witnessList baseContext hwitness) as hself.
  exists (rawDynamicTruthNativeCrossLevelStagedProofCertificate M
    witnessList baseContext body child).
  exists witnessList,
    (rawProofCloseNCarriedRoot M baseContext 3 body child), baseContext.
  split.
  - unfold rawDynamicTruthNativeCrossLevelStagedProofCertificate.
    reflexivity.
  - repeat split.
    + exact hwitness.
    + exact (raw_proofCloseNCarriedRoot_ruleCoverage M hPA
        baseContext hself 3 body child hcoverage hendpoint).
    + change (RawProofEndpoint M
        (rawProofCloseNCarriedRoot M baseContext 3 body child)
        baseContext (rawRestrictedTargetCloseNFormulaCode M 3 body)).
      exact (raw_proofCloseNCarriedRoot_endpoint M hPA
        baseContext hself 3 body child hcoverage hendpoint).
Qed.

(** Close the body produced by the one staged implication. *)
Theorem
    raw_dynamicTruthNativeCrossLevelStagedFieldProof_of_body_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot,
    RawDynamicTruthNativeCrossLevelLinkedRowsAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    RawDynamicTruthNativeCrossLevelStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot ->
    exists certificate : M,
      RawCodedPAProofOf M
        (rawDynamicTruthNativeCrossLevelCoherenceFieldCode M
          sigmaDomain piDomain currentSigma currentPi nextSigma nextPi)
        certificate.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot hlinked hstaged.
  pose proof hstaged as hstagedForBody.
  destruct hstaged as [hwitnessed _ _ _ _ _ _ _].
  apply
    (raw_codedPAProofOf_dynamicTruthNativeCrossLevelField_of_body_root_on
      M hPA witnessList baseContext
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      hwitnessed).
  exact (raw_dynamicTruthNativeCrossLevelStagedBodyRoot_of_implication
    M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot hlinked hstagedForBody).
Qed.

(** Graph-facing endpoint.  Both the six dynamic formula parameters and the
    final field code are obtained from one transform trace; the linked rows
    are then exposed from that same trace before invoking the kernel. *)
Theorem
    raw_dynamicTruthNativeCrossLevelStagedTransformProof_of_body_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi fieldCode
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi ->
    RawDynamicTruthNativeCrossLevelFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode ->
    RawDynamicTruthNativeCrossLevelStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot ->
    exists certificate : M,
      RawCodedPAProofOf M fieldCode certificate.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi fieldCode
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot horbit htransform hstaged.
  destruct (raw_dynamicTruthNativeCrossLevelProofTraceAt_of_transform M tail
    predecessorLevel currentGlobalSigma currentGlobalPi fieldCode
    horbit htransform) as
    (sigmaDomain & piDomain & currentSigma & currentPi & nextSigma & nextPi &
      hfield & htrace).
  destruct
    (raw_dynamicTruthNativeCrossLevelProofTraceAt_exposes_linked_rows
      M tail predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      htrace) as
    (sigmaRowDomain & piRowDomain & lowerPi & lowerSigma & hlinked).
  rewrite hfield.
  exact
    (raw_dynamicTruthNativeCrossLevelStagedFieldProof_of_body_implication
      M hPA hcompiler tail predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain currentSigma currentPi nextSigma nextPi
      sigmaRowDomain piRowDomain lowerPi lowerSigma
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot hlinked hstaged).
Qed.

End PABoundedRawCodedDynamicTruthNativeCrossLevelStagedRootCompilation.
