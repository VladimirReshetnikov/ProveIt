(**
  Dependency-aware compilation of the native PA-axiom-soundness stage.

  The axiom field is the fifth positive field in the native master orbit.
  Its proof is therefore allowed to use the preceding six-field master and
  the four successor fields already compiled at the current stage.  This
  file records that dependency prefix literally as

      ((((current-master /\ next-local) /\ next-cross)
          /\ next-shift) /\ next-substitution).

  All ten component roots live in one witnessed PA-axiom context.  The only
  arithmetic residual below is one trace-linked implication from that
  cumulative antecedent to the already isolated curried witness kernel

      shifted-antecedent -> witness-body -> shifted-next-Sigma.

  Everything after that implication is proof-code plumbing.  We apply the
  cumulative antecedent, use the existing witness-body compiler to construct
  both domain leaves, and retain the exact formula/context shifts through
  Ex-E and Or-E.  Finally Imp-I and All-I close the selected axiom field over
  the *same* witnessed context, and that carried local root is packaged as an
  ordinary represented PA proof.  No semantic truth is converted to proof
  syntax and no nonempty context is erased.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFormulaShiftAtomicAdequacy
  RawCodedRestrictedProofStandardAdequacy
  RawCodedRestrictedPAProof
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedPAProofImpICertificates
  RawCodedPAAxiomContextSelfShift
  RawCodedProofBinaryConstructors
  RawCodedProofAndIConstructor
  RawCodedProofImpIConstructor
  RawCodedProofAllIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofAndIntroduction
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedTruthCertificateFinalProjection
  RawCodedTruthCertificateMasterIntroduction
  RawCodedPAProvability
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph
  RawCodedDynamicTruthNativeAxiomSoundnessProofCompilation
  RawCodedDynamicTruthNativeAxiomSoundnessLeafRootCompilation
  RawCodedDynamicTruthNativeAxiomWitnessBodyRootCompilation
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.

Module PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaShiftAtomicAdequacy.
Import PABoundedRawCodedRestrictedProofStandardAdequacy.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedPAProofImpICertificates.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedTruthCertificateFinalProjection.
Import PABoundedRawCodedTruthCertificateMasterIntroduction.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessProofCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAxiomSoundnessLeafRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAxiomWitnessBodyRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.

(** ------------------------------------------------------------------
    The literal dependency prefix and its represented proof root. *)

(** Reuse the committed cross-level prefix for the first seven fields, then
    extend it in the exact production order.  This makes the dependency on
    the preceding stage syntactically visible without importing any later
    staged wrapper. *)
Definition rawDynamicTruthNativeAxiomStagedAntecedentCode
    (M : RawPAModel)
    (currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution : M) : M :=
  rawFormulaAndCode M
    (rawFormulaAndCode M
      (rawFormulaAndCode M
        (rawDynamicTruthNativeCrossLevelStagedAntecedentCode M
          currentLocal currentCrossLevel currentShift currentSubstitution
          currentAxiomSoundness currentFinal nextLocal)
        nextCrossLevel)
      nextShift)
    nextSubstitution.

Arguments rawDynamicTruthNativeAxiomStagedAntecedentCode
  M currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution : clear implicits.

(** The prerequisite record keeps every target paired with the actual root
    proving it in one common base.  The witnessed relation is not cosmetic:
    it supplies both context realizability for Ex-E and the self-shift needed
    by the final All-I binder. *)
Record RawDynamicTruthNativeAxiomStagedPrerequisitesAt
    (M : RawPAModel)
    (witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot
      nextSubstitutionRoot : M) : Prop := {
  rawDynamicTruthNativeAxiom_staged_witnessed :
    RawCodedPAAxiomWitnessContext M witnessList baseContext;
  rawDynamicTruthNativeAxiom_staged_currentLocal :
    RawCodedPALocalProofOf M baseContext currentLocal currentLocalRoot;
  rawDynamicTruthNativeAxiom_staged_currentCrossLevel :
    RawCodedPALocalProofOf M baseContext
      currentCrossLevel currentCrossLevelRoot;
  rawDynamicTruthNativeAxiom_staged_currentShift :
    RawCodedPALocalProofOf M baseContext currentShift currentShiftRoot;
  rawDynamicTruthNativeAxiom_staged_currentSubstitution :
    RawCodedPALocalProofOf M baseContext
      currentSubstitution currentSubstitutionRoot;
  rawDynamicTruthNativeAxiom_staged_currentAxiomSoundness :
    RawCodedPALocalProofOf M baseContext
      currentAxiomSoundness currentAxiomSoundnessRoot;
  rawDynamicTruthNativeAxiom_staged_currentFinal :
    RawCodedPALocalProofOf M baseContext currentFinal currentFinalRoot;
  rawDynamicTruthNativeAxiom_staged_nextLocal :
    RawCodedPALocalProofOf M baseContext nextLocal nextLocalRoot;
  rawDynamicTruthNativeAxiom_staged_nextCrossLevel :
    RawCodedPALocalProofOf M baseContext
      nextCrossLevel nextCrossLevelRoot;
  rawDynamicTruthNativeAxiom_staged_nextShift :
    RawCodedPALocalProofOf M baseContext nextShift nextShiftRoot;
  rawDynamicTruthNativeAxiom_staged_nextSubstitution :
    RawCodedPALocalProofOf M baseContext
      nextSubstitution nextSubstitutionRoot
}.

Arguments RawDynamicTruthNativeAxiomStagedPrerequisitesAt
  M witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
  : clear implicits.

(** A concrete conjunction-introduction tree for the cumulative antecedent.
    Its nesting is kept in lockstep with the definition above. *)
Definition rawDynamicTruthNativeAxiomStagedAntecedentRoot
    (M : RawPAModel) (baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot
      nextSubstitutionRoot : M) : M :=
  rawProofAndIRoot M baseContext
    (rawFormulaAndCode M
      (rawFormulaAndCode M
        (rawDynamicTruthNativeCrossLevelStagedAntecedentCode M
          currentLocal currentCrossLevel currentShift currentSubstitution
          currentAxiomSoundness currentFinal nextLocal)
        nextCrossLevel)
      nextShift)
    nextSubstitution
    (rawProofAndIRoot M baseContext
      (rawFormulaAndCode M
        (rawDynamicTruthNativeCrossLevelStagedAntecedentCode M
          currentLocal currentCrossLevel currentShift currentSubstitution
          currentAxiomSoundness currentFinal nextLocal)
        nextCrossLevel)
      nextShift
      (rawProofAndIRoot M baseContext
        (rawDynamicTruthNativeCrossLevelStagedAntecedentCode M
          currentLocal currentCrossLevel currentShift currentSubstitution
          currentAxiomSoundness currentFinal nextLocal)
        nextCrossLevel
        (rawProofAndIRoot M baseContext
          (rawSixFieldMasterCode M
            currentLocal currentCrossLevel currentShift currentSubstitution
            currentAxiomSoundness currentFinal)
          nextLocal
          (rawSixFieldMasterIntroductionRoot M baseContext
            currentLocal currentCrossLevel currentShift currentSubstitution
            currentAxiomSoundness currentFinal
            currentLocalRoot currentCrossLevelRoot currentShiftRoot
            currentSubstitutionRoot currentAxiomSoundnessRoot
            currentFinalRoot)
          nextLocalRoot)
        nextCrossLevelRoot)
      nextShiftRoot)
    nextSubstitutionRoot.

Arguments rawDynamicTruthNativeAxiomStagedAntecedentRoot
  M baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
  : clear implicits.

Theorem raw_dynamicTruthNativeAxiomStagedAntecedentRoot_of_prerequisites :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot,
  RawDynamicTruthNativeAxiomStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawDynamicTruthNativeAxiomStagedAntecedentCode M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution)
    (rawDynamicTruthNativeAxiomStagedAntecedentRoot M baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot).
Proof.
  intros M hPA witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
    hstaged.
  destruct hstaged as
    [hwitnessed hcurrentLocal hcurrentCross hcurrentShift
      hcurrentSubstitution hcurrentAxiom hcurrentFinal
      hnextLocal hnextCross hnextShift hnextSubstitution].
  pose proof (raw_codedPALocalProofOf_sixFieldMaster_intro M hPA
    baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    hcurrentLocal hcurrentCross hcurrentShift hcurrentSubstitution
    hcurrentAxiom hcurrentFinal) as hmaster.
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
    nextLocalRoot hmaster hnextLocal) as hlocalPrefix.
  pose proof (raw_codedPALocalProofOf_andI M hPA baseContext
    (rawDynamicTruthNativeCrossLevelStagedAntecedentCode M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal)
    nextCrossLevel
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
    nextCrossLevelRoot hlocalPrefix hnextCross) as hcrossPrefix.
  pose proof (raw_codedPALocalProofOf_andI M hPA baseContext
    (rawFormulaAndCode M
      (rawDynamicTruthNativeCrossLevelStagedAntecedentCode M
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal nextLocal)
      nextCrossLevel)
    nextShift
    (rawProofAndIRoot M baseContext
      (rawDynamicTruthNativeCrossLevelStagedAntecedentCode M
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal nextLocal)
      nextCrossLevel
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
      nextCrossLevelRoot)
    nextShiftRoot hcrossPrefix hnextShift) as hshiftPrefix.
  unfold rawDynamicTruthNativeAxiomStagedAntecedentCode,
    rawDynamicTruthNativeAxiomStagedAntecedentRoot.
  exact (raw_codedPALocalProofOf_andI M hPA baseContext
    (rawFormulaAndCode M
      (rawFormulaAndCode M
        (rawDynamicTruthNativeCrossLevelStagedAntecedentCode M
          currentLocal currentCrossLevel currentShift currentSubstitution
          currentAxiomSoundness currentFinal nextLocal)
        nextCrossLevel)
      nextShift)
    nextSubstitution
    (rawProofAndIRoot M baseContext
      (rawFormulaAndCode M
        (rawDynamicTruthNativeCrossLevelStagedAntecedentCode M
          currentLocal currentCrossLevel currentShift currentSubstitution
          currentAxiomSoundness currentFinal nextLocal)
        nextCrossLevel)
      nextShift
      (rawProofAndIRoot M baseContext
        (rawDynamicTruthNativeCrossLevelStagedAntecedentCode M
          currentLocal currentCrossLevel currentShift currentSubstitution
          currentAxiomSoundness currentFinal nextLocal)
        nextCrossLevel
        (rawProofAndIRoot M baseContext
          (rawSixFieldMasterCode M
            currentLocal currentCrossLevel currentShift currentSubstitution
            currentAxiomSoundness currentFinal)
          nextLocal
          (rawSixFieldMasterIntroductionRoot M baseContext
            currentLocal currentCrossLevel currentShift currentSubstitution
            currentAxiomSoundness currentFinal
            currentLocalRoot currentCrossLevelRoot currentShiftRoot
            currentSubstitutionRoot currentAxiomSoundnessRoot
            currentFinalRoot)
          nextLocalRoot)
        nextCrossLevelRoot)
      nextShiftRoot)
    nextSubstitutionRoot hshiftPrefix hnextSubstitution).
Qed.

(** ------------------------------------------------------------------
    One staged implication supplies the existing curried kernel. *)

Definition RawDynamicTruthNativeAxiomStagedKernelImplicationRootOn
    (M : RawPAModel) (baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      shiftedAntecedent shiftedNextSigma : M) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M baseContext
      (rawFormulaImpCode M
        (rawDynamicTruthNativeAxiomStagedAntecedentCode M
          currentLocal currentCrossLevel currentShift currentSubstitution
          currentAxiomSoundness currentFinal
          nextLocal nextCrossLevel nextShift nextSubstitution)
        (rawDynamicTruthNativeAxiomWitnessBodyKernelCode M
          shiftedAntecedent shiftedNextSigma))
      root.

Arguments RawDynamicTruthNativeAxiomStagedKernelImplicationRootOn
  M baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    shiftedAntecedent shiftedNextSigma : clear implicits.

(** This is the sole arithmetic residual.  Although the implication mentions
    only the shifted antecedent and shifted next-Sigma in its consequent, all
    four formula shifts and the context self-shift are retained here.  They
    ensure that the implication remains attached to exactly the Sigma/Pi
    leaves and Ex-E closure selected from the linked successor rows. *)
Definition
    RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
      shiftedAntecedent shiftedSigmaDomain shiftedPiDomain
      shiftedNextSigma,
    RawDynamicTruthNativeAxiomSoundnessLinkedRowsAt M tail
      predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    RawDynamicTruthNativeAxiomStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot ->
    RawContextShift M baseContext baseContext ->
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
        sigmaDomain piDomain)
      shiftedAntecedent ->
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      sigmaDomain shiftedSigmaDomain ->
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      piDomain shiftedPiDomain ->
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      nextSigmaEvidence shiftedNextSigma ->
    RawDynamicTruthNativeAxiomStagedKernelImplicationRootOn M
      baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      shiftedAntecedent shiftedNextSigma.

Arguments
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M
  : clear implicits.

(** Apply the only staged implication.  The result is literally the
    [RawDynamicTruthNativeAxiomWitnessBodyKernelRootOn] fiber consumed by the
    existing linked witness-body compiler. *)
Theorem raw_dynamicTruthNativeAxiomWitnessBodyKernelRoot_of_staged_implication :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
      shiftedAntecedent shiftedNextSigma,
  RawDynamicTruthNativeAxiomStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot ->
  RawDynamicTruthNativeAxiomStagedKernelImplicationRootOn M
      baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      shiftedAntecedent shiftedNextSigma ->
  RawDynamicTruthNativeAxiomWitnessBodyKernelRootOn M
    baseContext shiftedAntecedent shiftedNextSigma.
Proof.
  intros M hPA witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
    shiftedAntecedent shiftedNextSigma hstaged
    (implicationRoot & himplication).
  pose proof
    (raw_dynamicTruthNativeAxiomStagedAntecedentRoot_of_prerequisites
      M hPA witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
      hstaged) as hantecedent.
  exists (rawProofImpERoot M baseContext
    (rawDynamicTruthNativeAxiomStagedAntecedentCode M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution)
    (rawDynamicTruthNativeAxiomWitnessBodyKernelCode M
      shiftedAntecedent shiftedNextSigma)
    implicationRoot
    (rawDynamicTruthNativeAxiomStagedAntecedentRoot M baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot)).
  exact (raw_codedPALocalProofOf_impE M hPA baseContext
    (rawDynamicTruthNativeAxiomStagedAntecedentCode M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution)
    (rawDynamicTruthNativeAxiomWitnessBodyKernelCode M
      shiftedAntecedent shiftedNextSigma)
    implicationRoot
    (rawDynamicTruthNativeAxiomStagedAntecedentRoot M baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot)
    himplication hantecedent).
Qed.

(** ------------------------------------------------------------------
    Route the staged kernel through the existing leaf/Ex-E/Or-E shell. *)

Theorem raw_dynamicTruthNativeAxiomLocalRootOn_of_staged_kernel_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot,
    RawDynamicTruthNativeAxiomSoundnessLinkedRowsAt M tail
      predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      sigmaRowDomain piRowDomain
      lowerPiApplication lowerSigmaApplication ->
    RawDynamicTruthNativeAxiomStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot ->
    RawDynamicTruthNativeAxiomLocalRootOn M baseContext
      sigmaDomain piDomain nextSigmaEvidence.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
    hlinked hstaged.
  pose proof (raw_dynamicTruthNativeAxiomSoundnessLinkedRowsAt_adequacy
    M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma hlinked) as hadequacy.
  destruct (raw_codedFormulaUnitShift_exists M hPA
    (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
      sigmaDomain piDomain)
    (rawDynamicTruthNativeAxiomSoundness_antecedent_adequate
      M sigmaDomain piDomain nextSigmaEvidence hadequacy)) as
    [shiftedAntecedent hantecedentShift].
  destruct (raw_codedFormulaUnitShift_exists M hPA sigmaDomain
    (rawDynamicTruthNativeAxiomSoundness_sigmaDomain_adequate
      M sigmaDomain piDomain nextSigmaEvidence hadequacy)) as
    [shiftedSigmaDomain hsigmaShift].
  destruct (raw_codedFormulaUnitShift_exists M hPA piDomain
    (rawDynamicTruthNativeAxiomSoundness_piDomain_adequate
      M sigmaDomain piDomain nextSigmaEvidence hadequacy)) as
    [shiftedPiDomain hpiShift].
  destruct (raw_codedFormulaUnitShift_exists M hPA nextSigmaEvidence
    (rawDynamicTruthNativeAxiomSoundness_nextSigma_adequate
      M sigmaDomain piDomain nextSigmaEvidence hadequacy)) as
    [shiftedNextSigma hnextShift].
  destruct hstaged as
    [hwitnessed hcurrentLocal hcurrentCross hcurrentShift
      hcurrentSubstitution hcurrentAxiom hcurrentFinal
      hnextLocal hnextCross hnextShiftProof hnextSubstitution].
  assert (hstagedAgain :
      RawDynamicTruthNativeAxiomStagedPrerequisitesAt M
        witnessList baseContext
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal
        nextLocal nextCrossLevel nextShift nextSubstitution
        currentLocalRoot currentCrossLevelRoot currentShiftRoot
        currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
        nextLocalRoot nextCrossLevelRoot nextShiftRoot
        nextSubstitutionRoot).
  {
    constructor; assumption.
  }
  pose proof (raw_codedPAAxiomWitnessContext_selfShift
    M hPA witnessList baseContext hwitnessed) as hbaseShift.
  pose proof (hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
    shiftedAntecedent shiftedSigmaDomain shiftedPiDomain shiftedNextSigma
    hlinked hstagedAgain hbaseShift hantecedentShift
    hsigmaShift hpiShift hnextShift) as himplication.
  pose proof
    (raw_dynamicTruthNativeAxiomWitnessBodyKernelRoot_of_staged_implication
      M hPA witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
      shiftedAntecedent shiftedNextSigma hstagedAgain himplication) as
    hkernel.
  destruct hkernel as [kernelRoot hkernelRoot].
  destruct (raw_dynamicTruthNativeAxiomWitnessBodyLeaf_of_kernel_root
    M hPA baseContext baseContext
    (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
      sigmaDomain piDomain)
    shiftedAntecedent sigmaDomain shiftedSigmaDomain
    shiftedNextSigma kernelRoot hbaseShift hantecedentShift
    hsigmaShift hkernelRoot) as [sigmaLeaf hsigmaLeaf].
  destruct (raw_dynamicTruthNativeAxiomWitnessBodyLeaf_of_kernel_root
    M hPA baseContext baseContext
    (rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
      sigmaDomain piDomain)
    shiftedAntecedent piDomain shiftedPiDomain
    shiftedNextSigma kernelRoot hbaseShift hantecedentShift
    hpiShift hkernelRoot) as [piLeaf hpiLeaf].
  apply (raw_dynamicTruthNativeAxiomLocalRootOn_of_witness_domain_leaves
    M hPA baseContext baseContext sigmaDomain piDomain
    nextSigmaEvidence).
  - exact (raw_codedPAAxiomWitnessContext_context_realizable
      M witnessList baseContext hwitnessed).
  - exact hbaseShift.
  - exact (rawDynamicTruthNativeAxiomSoundness_sigmaDomain_adequate
      M sigmaDomain piDomain nextSigmaEvidence hadequacy).
  - exact (rawDynamicTruthNativeAxiomSoundness_piDomain_adequate
      M sigmaDomain piDomain nextSigmaEvidence hadequacy).
  - exists shiftedAntecedent, shiftedSigmaDomain, shiftedPiDomain,
      shiftedNextSigma, sigmaLeaf, piLeaf.
    split; [exact hantecedentShift |].
    split; [exact hsigmaShift |].
    split; [exact hpiShift |].
    split; [exact hnextShift |].
    split; [exact hsigmaLeaf | exact hpiLeaf].
Qed.

(** ------------------------------------------------------------------
    Carried All/Imp closure and ordinary-proof packaging. *)

Definition RawDynamicTruthNativeAxiomFieldLocalRootOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain nextSigmaEvidence : M) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthNativeAxiomSoundnessFieldCode M
        sigmaDomain piDomain nextSigmaEvidence)
      root.

Arguments RawDynamicTruthNativeAxiomFieldLocalRootOn
  M baseContext sigmaDomain piDomain nextSigmaEvidence : clear implicits.

(** Imp-I first discharges the transparent carrier antecedent.  All-I then
    uses the witnessed base's self-shift: under the eigenvariable binder the
    context is not replaced by zero and no PA axiom is lost. *)
Theorem raw_dynamicTruthNativeAxiomFieldLocalRootOn_of_local_root :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext sigmaDomain piDomain nextSigmaEvidence,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawDynamicTruthNativeAxiomLocalRootOn M baseContext
      sigmaDomain piDomain nextSigmaEvidence ->
  RawDynamicTruthNativeAxiomFieldLocalRootOn M baseContext
      sigmaDomain piDomain nextSigmaEvidence.
Proof.
  intros M hPA witnessList baseContext
    sigmaDomain piDomain nextSigmaEvidence hwitnessed
    (child & hchild).
  set (antecedent :=
    rawDynamicTruthNativeAxiomSoundnessAntecedentCode M
      sigmaDomain piDomain).
  set (body := rawFormulaImpCode M antecedent nextSigmaEvidence).
  set (impRoot := rawProofImpIRoot M baseContext
    antecedent nextSigmaEvidence child).
  pose proof (raw_codedPALocalProofOf_impI M hPA baseContext
    antecedent nextSigmaEvidence child hchild) as himp.
  destruct himp as [himpCoverage himpEndpoint].
  exists (rawProofAllIRoot M baseContext body impRoot).
  rewrite rawDynamicTruthNativeAxiomSoundnessFieldCode_as_all_imp.
  change (RawCodedPALocalProofOf M baseContext
    (rawFormulaAllCode M body)
    (rawProofAllIRoot M baseContext body impRoot)).
  split.
  - exact (raw_proofAllI_ruleCoverage M hPA
      baseContext baseContext body impRoot
      (raw_codedPAAxiomWitnessContext_selfShift
        M hPA witnessList baseContext hwitnessed)
      himpCoverage himpEndpoint).
  - exact (raw_proofAllI_endpoint M baseContext body impRoot).
Qed.

(** Package a carried local field root using the same witness list and
    context.  Only the outer certificate list is new. *)
Theorem raw_codedPAProofOf_dynamicTruthNativeAxiomField_of_carried_root :
    forall (M : RawPAModel) witnessList baseContext
      sigmaDomain piDomain nextSigmaEvidence,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawDynamicTruthNativeAxiomFieldLocalRootOn M baseContext
      sigmaDomain piDomain nextSigmaEvidence ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthNativeAxiomSoundnessFieldCode M
        sigmaDomain piDomain nextSigmaEvidence)
      certificate.
Proof.
  intros M witnessList baseContext sigmaDomain piDomain nextSigmaEvidence
    hwitnessed (root & [hcoverage hendpoint]).
  exists (rawCodeList3 M (rawNumeralValue M 0) witnessList root).
  exists witnessList, root, baseContext.
  split; [reflexivity |].
  repeat split; assumption.
Qed.

(** Exact transform-selected endpoint.  The graph transform supplies the
    literal Sigma/Pi domains and next-Sigma evidence.  Its trace is opened
    into linked rows before invoking the sole staged residual, so the final
    ordinary proof cannot drift to another transform output. *)
Theorem
    raw_dynamicTruthNativeAxiomTransformSelectedProof_of_staged_kernel_implication
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi fieldCode,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi ->
    RawDynamicTruthNativeAxiomSoundnessFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode ->
  forall witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot,
    RawDynamicTruthNativeAxiomStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot ->
  exists certificate : M, RawCodedPAProofOf M fieldCode certificate.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi fieldCode horbit htransform
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
    hstaged.
  destruct (raw_dynamicTruthNativeAxiomSoundnessProofTraceAt_of_transform
    M tail predecessorLevel currentGlobalSigma currentGlobalPi fieldCode
    horbit htransform) as
    (sigmaDomain & piDomain & nextSigmaEvidence & hfield & htrace).
  destruct
    (raw_dynamicTruthNativeAxiomSoundnessProofTraceAt_exposes_linked_rows
      M tail predecessorLevel currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence htrace) as
    (sigmaRowDomain & piRowDomain & lowerPi & lowerSigma & hlinked).
  pose proof
    (raw_dynamicTruthNativeAxiomLocalRootOn_of_staged_kernel_implication
      M hPA hcompiler tail predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain nextSigmaEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
      hlinked hstaged) as hlocal.
  pose proof hstaged as hstagedCopy.
  destruct hstagedCopy as [hwitnessed].
  rewrite hfield.
  exact (raw_codedPAProofOf_dynamicTruthNativeAxiomField_of_carried_root
    M witnessList baseContext sigmaDomain piDomain nextSigmaEvidence
    hwitnessed
    (raw_dynamicTruthNativeAxiomFieldLocalRootOn_of_local_root
      M hPA witnessList baseContext sigmaDomain piDomain nextSigmaEvidence
      hwitnessed hlocal)).
Qed.

(** Pair the exact ordinary proof with the corresponding positive-graph
    witness.  This is the pointwise shape expected by the dependency-ordered
    axiom callback; graph selection and proof selection share [fieldCode]. *)
Corollary
    raw_dynamicTruthNativeAxiomPositiveProofAt_of_staged_kernel_implication
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi fieldCode,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi ->
    RawDynamicTruthNativeAxiomSoundnessFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode ->
  forall witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot,
    RawDynamicTruthNativeAxiomStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot ->
  exists certificate : M,
    raw_formula_sat M
      (scons M fieldCode (scons M predecessorLevel tail))
      dynamicTruthNativeAxiomSoundnessPositiveGraph /\
    RawCodedPAProofOf M fieldCode certificate.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi fieldCode horbit htransform
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
    hstaged.
  destruct
    (raw_dynamicTruthNativeAxiomTransformSelectedProof_of_staged_kernel_implication
      M hPA hcompiler tail predecessorLevel
      currentGlobalSigma currentGlobalPi fieldCode horbit htransform
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot nextSubstitutionRoot
      hstaged) as [certificate hcertificate].
  exists certificate. split.
  - apply (proj2
      (raw_sat_dynamicTruthNativeAxiomSoundnessPositiveGraph_iff
        M tail predecessorLevel fieldCode)).
    exists currentGlobalSigma, currentGlobalPi. split.
    + apply (proj1
        (raw_dynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt_iff M
          tail (raw_succ M predecessorLevel)
          currentGlobalSigma currentGlobalPi)).
      exact horbit.
    + exact htransform.
  - exact hcertificate.
Qed.

(** The residual compiler above is intentionally not proved here.  It is the
    one staged arithmetic kernel still required for axiom soundness; all
    context shifts, witness-body leaves, eliminations, binder closures, and
    exact-target packaging following it are discharged by this module. *)

End PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
