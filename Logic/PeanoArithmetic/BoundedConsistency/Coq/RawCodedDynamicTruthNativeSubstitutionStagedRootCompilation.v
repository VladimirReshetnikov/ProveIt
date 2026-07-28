(**
  Dependency-aware root compilation for native substitution invariance.

  Lean's staged successor proves substitution invariance only after the
  current six-field certificate and the new local, cross-level, and shift
  fields are available.  Thus the exact cumulative antecedent is

      (((current six-field master /\ next local) /\ next cross-level)
        /\ next shift).

  This file records that dependency boundary literally.  All nine input
  roots share one witnessed PA context, and the sole mathematical residual
  is one trace-linked implication from the cumulative antecedent to the
  complete open substitution body.  The implication synchronizes all four
  directional substitution laws; four independent context-free compilers
  would be strictly stronger than the production construction.

  Everything surrounding that implication is structural.  We assemble the
  cumulative antecedent, apply the implication in the same visible context,
  recover the four directional leaves and implication roots by checked
  context insertion and propositional elimination, and replay the seven
  universal introductions while retaining the original witnessed PA tail.
  No semantic truth-to-proof conversion, proof irrelevance, or context
  erasure is used.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthOperationTransport
  RawCodedRestrictedProofStandardAdequacy
  RawCodedRestrictedPAProof
  RawCodedProofEndpoints
  RawCodedProofRuleCoverage
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedProofAssumptionLeaf
  RawCodedProofBinaryConstructors
  RawCodedProofAndIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofAndIntroduction
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPAProvability
  RawCodedPAProofImpICertificates
  RawCodedTruthCertificateFinalProjection
  RawCodedTruthCertificateMasterIntroduction
  RawCodedPAAxiomContextSelfShift
  RawCodedPAProofAllNCarriedCertificates
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation
  RawCodedDynamicTruthNativeSubstitutionCarrier
  RawCodedDynamicTruthNativeSubstitutionPositiveGraph
  RawCodedDynamicTruthNativeSubstitutionProofCompilation
  RawCodedDynamicTruthNativeSubstitutionLeafRootCompilation.

Import ListNotations.

Module
  PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthOperationTransport.
Import PABoundedRawCodedRestrictedProofStandardAdequacy.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAProofImpICertificates.
Import PABoundedRawCodedTruthCertificateFinalProjection.
Import PABoundedRawCodedTruthCertificateMasterIntroduction.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedPAProofAllNCarriedCertificates.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionCarrier.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionLeafRootCompilation.

(** ------------------------------------------------------------------
    The exact cumulative context available to the substitution kernel. *)

Definition rawDynamicTruthNativeSubstitutionStagedAntecedentCode
    (M : RawPAModel)
    (currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift : M) : M :=
  rawFormulaAndCode M
    (rawFormulaAndCode M
      (rawDynamicTruthNativeCrossLevelStagedAntecedentCode M
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal nextLocal)
      nextCrossLevel)
    nextShift.

Arguments rawDynamicTruthNativeSubstitutionStagedAntecedentCode
  M currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel nextShift
  : clear implicits.

(** Every prerequisite is a local root in one literal witnessed context.
    In particular, the three successor fields cannot be imported from three
    unrelated ordinary certificates and silently treated as a conjunction. *)
Record RawDynamicTruthNativeSubstitutionStagedPrerequisitesAt
    (M : RawPAModel)
    (witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot : M) : Prop := {
  rawDynamicTruthNativeSubstitution_staged_witnessed :
    RawCodedPAAxiomWitnessContext M witnessList baseContext;
  rawDynamicTruthNativeSubstitution_staged_currentLocal :
    RawCodedPALocalProofOf M baseContext currentLocal currentLocalRoot;
  rawDynamicTruthNativeSubstitution_staged_currentCrossLevel :
    RawCodedPALocalProofOf M baseContext
      currentCrossLevel currentCrossLevelRoot;
  rawDynamicTruthNativeSubstitution_staged_currentShift :
    RawCodedPALocalProofOf M baseContext currentShift currentShiftRoot;
  rawDynamicTruthNativeSubstitution_staged_currentSubstitution :
    RawCodedPALocalProofOf M baseContext
      currentSubstitution currentSubstitutionRoot;
  rawDynamicTruthNativeSubstitution_staged_currentAxiomSoundness :
    RawCodedPALocalProofOf M baseContext
      currentAxiomSoundness currentAxiomSoundnessRoot;
  rawDynamicTruthNativeSubstitution_staged_currentFinal :
    RawCodedPALocalProofOf M baseContext currentFinal currentFinalRoot;
  rawDynamicTruthNativeSubstitution_staged_nextLocal :
    RawCodedPALocalProofOf M baseContext nextLocal nextLocalRoot;
  rawDynamicTruthNativeSubstitution_staged_nextCrossLevel :
    RawCodedPALocalProofOf M baseContext
      nextCrossLevel nextCrossLevelRoot;
  rawDynamicTruthNativeSubstitution_staged_nextShift :
    RawCodedPALocalProofOf M baseContext nextShift nextShiftRoot
}.

Arguments RawDynamicTruthNativeSubstitutionStagedPrerequisitesAt
  M witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel nextShift
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot : clear implicits.

(** A single implication is the smallest synchronized arithmetic seam.  Its
    consequent is the complete open body, rather than four freely chosen
    directional targets, and its context is exactly the context of all nine
    prerequisites. *)
Definition
    RawDynamicTruthNativeSubstitutionStagedBodyImplicationRootOn
    (M : RawPAModel)
    (baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : M)
    : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M baseContext
      (rawFormulaImpCode M
        (rawDynamicTruthNativeSubstitutionStagedAntecedentCode M
          currentLocal currentCrossLevel currentShift currentSubstitution
          currentAxiomSoundness currentFinal
          nextLocal nextCrossLevel nextShift)
        (rawDynamicTruthNativeSubstitutionBodyCode M
          sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi))
      root.

Arguments
  RawDynamicTruthNativeSubstitutionStagedBodyImplicationRootOn
  M baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel nextShift
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
  : clear implicits.

(** The residual remains linked to the one represented orbit/transform trace
    which selected all six formulas in the body. *)
Definition
    RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot,
    RawDynamicTruthNativeSubstitutionProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi ->
    RawDynamicTruthNativeSubstitutionStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot ->
    RawDynamicTruthNativeSubstitutionStagedBodyImplicationRootOn M
      baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi.

Arguments
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler
  M : clear implicits.

(** Assemble the exact [shiftContext] analogue and apply the one residual
    implication.  The witness component is retained in [hstagedAgain] and is
    not used to erase the base context. *)
Theorem raw_dynamicTruthNativeSubstitutionStagedBodyRoot_of_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler
    M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot,
    RawDynamicTruthNativeSubstitutionProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi ->
    RawDynamicTruthNativeSubstitutionStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot ->
    RawDynamicTruthNativeSubstitutionBodyLocalRootOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot htrace hstaged.
  destruct hstaged as
    [hwitnessed hcurrentLocal hcurrentCross hcurrentShift
      hcurrentSubstitution hcurrentAxiom hcurrentFinal
      hnextLocal hnextCross hnextShift].
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
    nextLocalRoot hcurrentMaster hnextLocal) as hlocalContext.
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
    nextCrossLevelRoot hlocalContext hnextCross) as hcrossContext.
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
    nextShiftRoot hcrossContext hnextShift) as hantecedent.
  assert (hstagedAgain :
      RawDynamicTruthNativeSubstitutionStagedPrerequisitesAt M
        witnessList baseContext
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal
        nextLocal nextCrossLevel nextShift
        currentLocalRoot currentCrossLevelRoot currentShiftRoot
        currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
        nextLocalRoot nextCrossLevelRoot nextShiftRoot).
  {
    constructor; assumption.
  }
  destruct (hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot
    htrace hstagedAgain) as [implicationRoot himplication].
  set (antecedent :=
    rawDynamicTruthNativeSubstitutionStagedAntecedentCode M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift).
  set (body := rawDynamicTruthNativeSubstitutionBodyCode M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
  exists (rawProofImpERoot M baseContext antecedent body
    implicationRoot
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
      nextShiftRoot)).
  exact (raw_codedPALocalProofOf_impE M hPA baseContext
    antecedent body implicationRoot
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
    himplication hantecedent).
Qed.

(** ------------------------------------------------------------------
    Structural decomposition of the synchronized body. *)

(** The only non-fixed constituents of the five-fold side condition are the
    two trace-selected domain codes.  This adequacy fact licenses insertion
    of the side-condition assumption above an arbitrary witnessed tail. *)
Lemma raw_dynamicTruthNativeSubstitutionAntecedent_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall sigmaDomain piDomain,
  RawCodedFormulaAtomicallyAdequate M sigmaDomain ->
  RawCodedFormulaAtomicallyAdequate M piDomain ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthNativeSubstitutionAntecedentCode M
      sigmaDomain piDomain).
Proof.
  intros M hPA sigmaDomain piDomain hsigmaDomain hpiDomain.
  unfold rawDynamicTruthNativeSubstitutionAntecedentCode,
    rawDynamicTruthNativeSubstitutionFormulaAnd5Code,
    rawDynamicTruthNativeSubstitutionSourceAdmissibleCode.
  apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
  - exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      (codedFormulaSingleSubstitutionTermAt
        (tVar 0) (tVar 1) (tVar 2))).
  - apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
    + exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
        (codedFormulaSubstitutionAssignmentRelationTermAt
          (tVar 0) (tVar 1) (tVar 3) (tVar 4) (tVar 5) (tVar 6))).
    + apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
      * apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
        -- exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
             (codedFormulaAtomicallyAdequateTermAt (tVar 1))).
        -- apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
           ++ exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
                (codedAssignmentDefinedThroughTermAt
                  (tVar 3) (tVar 4) (tVar 1))).
           ++ apply raw_formulaOrCode_atomically_adequate;
                [exact hPA | exact hsigmaDomain | exact hpiDomain].
      * apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
        -- exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
             (codedFormulaTargetAdmissibilityDataTermAt
               (tVar 2) (tVar 5) (tVar 6))).
        -- exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
             (codedFormulaRankAgreementTermAt (tVar 1) (tVar 2))).
Qed.

(** Open the full body under its literal side-condition assumption and
    project its four implication roots.  The body itself first undergoes one
    checked insertion; no arbitrary-context weakening is assumed. *)
Theorem raw_dynamicTruthNativeSubstitutionLocalRootsOn_of_body_root :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi,
  RawContextListRealizable M baseContext ->
  RawCodedFormulaAtomicallyAdequate M sigmaDomain ->
  RawCodedFormulaAtomicallyAdequate M piDomain ->
  RawDynamicTruthNativeSubstitutionBodyLocalRootOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi ->
  RawDynamicTruthNativeSubstitutionSigmaLocalRootsOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma /\
    RawDynamicTruthNativeSubstitutionPiLocalRootsOn M baseContext
      sigmaDomain piDomain sourcePi targetPi.
Proof.
  intros M hPA baseContext sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi
    hbase hsigmaDomain hpiDomain [bodyRoot hbody].
  set (antecedent := rawDynamicTruthNativeSubstitutionAntecedentCode M
    sigmaDomain piDomain).
  set (common := rawDynamicTruthNativeSubstitutionCommonContextOn M
    baseContext sigmaDomain piDomain).
  set (sigmaForward := rawFormulaImpCode M sourceSigma targetSigma).
  set (sigmaBackward := rawFormulaImpCode M targetSigma sourceSigma).
  set (piForward := rawFormulaImpCode M sourcePi targetPi).
  set (piBackward := rawFormulaImpCode M targetPi sourcePi).
  set (sigmaIff := rawDynamicTruthNativeSubstitutionFormulaIffCode M
    sourceSigma targetSigma).
  set (piIff := rawDynamicTruthNativeSubstitutionFormulaIffCode M
    sourcePi targetPi).
  set (transport := rawFormulaAndCode M sigmaIff piIff).
  assert (hantecedentAdequate :
      RawCodedFormulaAtomicallyAdequate M antecedent).
  {
    unfold antecedent.
    exact (raw_dynamicTruthNativeSubstitutionAntecedent_atomically_adequate
      M hPA sigmaDomain piDomain hsigmaDomain hpiDomain).
  }
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    baseContext antecedent
    (rawDynamicTruthNativeSubstitutionBodyCode M
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
    bodyRoot hantecedentAdequate hbase hbody) as
    [bodyAtCommon hbodyAtCommon].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    baseContext antecedent hbase) as hantecedent.
  change (RawCodedPALocalProofOf M common
    (rawFormulaImpCode M antecedent transport) bodyAtCommon)
    in hbodyAtCommon.
  change (RawCodedPALocalProofOf M common antecedent
    (rawProofAssumptionRoot M common antecedent)) in hantecedent.
  pose proof (raw_codedPALocalProofOf_impE M hPA common
    antecedent transport bodyAtCommon
    (rawProofAssumptionRoot M common antecedent)
    hbodyAtCommon hantecedent) as htransport.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA common
    sigmaIff piIff _ htransport) as hsigmaIff.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA common
    sigmaIff piIff _ htransport) as hpiIff.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA common
    sigmaForward sigmaBackward _ hsigmaIff) as hsigmaForward.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA common
    sigmaForward sigmaBackward _ hsigmaIff) as hsigmaBackward.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA common
    piForward piBackward _ hpiIff) as hpiForward.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA common
    piForward piBackward _ hpiIff) as hpiBackward.
  split.
  - do 2 eexists. split; [exact hsigmaForward | exact hsigmaBackward].
  - do 2 eexists. split; [exact hpiForward | exact hpiBackward].
Qed.

(** Turn one implication root in the common side-condition context into its
    directional target leaf by inserting the source assumption and applying
    modus ponens.  Source adequacy is explicit because it is exactly the
    guard required by checked insertion. *)
Lemma raw_dynamicTruthNativeSubstitutionDirectionalLeaf_of_local_root :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain source target implicationRoot,
  RawContextListRealizable M baseContext ->
  RawCodedFormulaAtomicallyAdequate M source ->
  RawCodedPALocalProofOf M
    (rawDynamicTruthNativeSubstitutionCommonContextOn M baseContext
      sigmaDomain piDomain)
    (rawFormulaImpCode M source target) implicationRoot ->
  exists leaf : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeSubstitutionDirectionalContextOn M baseContext
        sigmaDomain piDomain source)
      target leaf.
Proof.
  intros M hPA baseContext sigmaDomain piDomain source target
    implicationRoot hbase hsource himplication.
  set (common := rawDynamicTruthNativeSubstitutionCommonContextOn M
    baseContext sigmaDomain piDomain).
  set (directional :=
    rawDynamicTruthNativeSubstitutionDirectionalContextOn M baseContext
      sigmaDomain piDomain source).
  assert (hcommon : RawContextListRealizable M common).
  {
    unfold common.
    exact (raw_dynamicTruthNativeSubstitutionCommonContextOn_realizable
      M hPA baseContext sigmaDomain piDomain hbase).
  }
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    common source (rawFormulaImpCode M source target) implicationRoot
    hsource hcommon himplication) as [transplanted htransplanted].
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    common source hcommon) as hassumption.
  change (RawCodedPALocalProofOf M directional
    (rawFormulaImpCode M source target) transplanted) in htransplanted.
  change (RawCodedPALocalProofOf M directional source
    (rawProofAssumptionRoot M directional source)) in hassumption.
  exists (rawProofImpERoot M directional source target
    transplanted (rawProofAssumptionRoot M directional source)).
  exact (raw_codedPALocalProofOf_impE M hPA directional source target
    transplanted (rawProofAssumptionRoot M directional source)
    htransplanted hassumption).
Qed.

(** The trace adequacy record supplies all four insertion guards, so the
    projected implication roots recover exactly the existing directional
    leaf packages, with no target re-selection. *)
Theorem
    raw_dynamicTruthNativeSubstitutionDirectionalLeavesOn_of_local_roots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi,
  RawContextListRealizable M baseContext ->
  RawDynamicTruthNativeSubstitutionProofTraceAdequacyAt M
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi ->
  RawDynamicTruthNativeSubstitutionSigmaLocalRootsOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma ->
  RawDynamicTruthNativeSubstitutionPiLocalRootsOn M baseContext
      sigmaDomain piDomain sourcePi targetPi ->
  RawDynamicTruthNativeSubstitutionSigmaDirectionalLeavesOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma /\
    RawDynamicTruthNativeSubstitutionPiDirectionalLeavesOn M baseContext
      sigmaDomain piDomain sourcePi targetPi.
Proof.
  intros M hPA baseContext
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi hbase hadequacy
    (sigmaForward & sigmaBackward & hsigmaForward & hsigmaBackward)
    (piForward & piBackward & hpiForward & hpiBackward).
  destruct hadequacy as
    [hcurrentSigma hcurrentPi hsigmaDomain hpiDomain
      hsourceSigma htargetSigma hsourcePi htargetPi].
  destruct
    (raw_dynamicTruthNativeSubstitutionDirectionalLeaf_of_local_root
      M hPA baseContext sigmaDomain piDomain
      sourceSigma targetSigma sigmaForward
      hbase hsourceSigma hsigmaForward) as
    [sigmaForwardLeaf hsigmaForwardLeaf].
  destruct
    (raw_dynamicTruthNativeSubstitutionDirectionalLeaf_of_local_root
      M hPA baseContext sigmaDomain piDomain
      targetSigma sourceSigma sigmaBackward
      hbase htargetSigma hsigmaBackward) as
    [sigmaBackwardLeaf hsigmaBackwardLeaf].
  destruct
    (raw_dynamicTruthNativeSubstitutionDirectionalLeaf_of_local_root
      M hPA baseContext sigmaDomain piDomain
      sourcePi targetPi piForward
      hbase hsourcePi hpiForward) as
    [piForwardLeaf hpiForwardLeaf].
  destruct
    (raw_dynamicTruthNativeSubstitutionDirectionalLeaf_of_local_root
      M hPA baseContext sigmaDomain piDomain
      targetPi sourcePi piBackward
      hbase htargetPi hpiBackward) as
    [piBackwardLeaf hpiBackwardLeaf].
  split.
  - exists sigmaForwardLeaf, sigmaBackwardLeaf. split; assumption.
  - exists piForwardLeaf, piBackwardLeaf. split; assumption.
Qed.

(** ------------------------------------------------------------------
    Trace-linked staged resources and carried ordinary certificates. *)

(** One invocation of the staged residual exposes every resource used by the
    older leaf shell.  Adequacy and side-condition roots are re-derived from
    the same trace and context, rather than accepted for unrelated codes. *)
Theorem
    raw_dynamicTruthNativeSubstitutionStagedResources_of_body_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler
    M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot,
    RawDynamicTruthNativeSubstitutionProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi ->
    RawDynamicTruthNativeSubstitutionStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot ->
    RawDynamicTruthNativeSubstitutionProofTraceAdequacyAt M
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi /\
    RawDynamicTruthNativeSubstitutionSideConditionRootsOn M baseContext
      sigmaDomain piDomain /\
    RawDynamicTruthNativeSubstitutionSigmaDirectionalLeavesOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma /\
    RawDynamicTruthNativeSubstitutionPiDirectionalLeavesOn M baseContext
      sigmaDomain piDomain sourcePi targetPi /\
    RawDynamicTruthNativeSubstitutionBodyLocalRootOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot htrace hstaged.
  pose proof hstaged as hstagedForWitness.
  destruct hstagedForWitness as
    [hwitnessed _ _ _ _ _ _ _ _ _].
  assert (hbase : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitnessed).
  }
  pose proof (raw_dynamicTruthNativeSubstitutionProofTraceAt_adequacy
    M hPA tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    htrace) as hadequacy.
  pose proof (raw_dynamicTruthNativeSubstitutionStagedBodyRoot_of_implication
    M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot
    htrace hstaged) as hbody.
  destruct hadequacy as
    [hcurrentSigma hcurrentPi hsigmaDomain hpiDomain
      hsourceSigma htargetSigma hsourcePi htargetPi].
  assert (hadequacyAgain :
      RawDynamicTruthNativeSubstitutionProofTraceAdequacyAt M
        currentGlobalSigma currentGlobalPi sigmaDomain piDomain
        sourceSigma targetSigma sourcePi targetPi).
  {
    constructor; assumption.
  }
  destruct (raw_dynamicTruthNativeSubstitutionLocalRootsOn_of_body_root
    M hPA baseContext sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi
    hbase hsigmaDomain hpiDomain hbody) as [hsigmaRoots hpiRoots].
  destruct
    (raw_dynamicTruthNativeSubstitutionDirectionalLeavesOn_of_local_roots
      M hPA baseContext
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi
      hbase hadequacyAgain hsigmaRoots hpiRoots) as
    [hsigmaLeaves hpiLeaves].
  split; [exact hadequacyAgain |].
  split.
  - exact (raw_dynamicTruthNativeSubstitutionSideConditionRootsOn
      M hPA baseContext sigmaDomain piDomain hbase).
  - split; [exact hsigmaLeaves |].
    split; [exact hpiLeaves | exact hbody].
Qed.

(** Deliberately route the staged body through the public directional-leaf
    interface and its implication-introduction constructors.  This confirms
    that the single synchronized implication discharges the historical
    four-leaf seam without changing the trace or the visible base context. *)
Theorem
    raw_dynamicTruthNativeSubstitutionStagedLocalRoots_via_directional_leaves :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler
    M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot,
    RawDynamicTruthNativeSubstitutionProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi ->
    RawDynamicTruthNativeSubstitutionStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot ->
    RawDynamicTruthNativeSubstitutionSigmaLocalRootsOn M baseContext
        sigmaDomain piDomain sourceSigma targetSigma /\
      RawDynamicTruthNativeSubstitutionPiLocalRootsOn M baseContext
        sigmaDomain piDomain sourcePi targetPi.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot htrace hstaged.
  destruct
    (raw_dynamicTruthNativeSubstitutionStagedResources_of_body_implication
      M hPA hcompiler tail predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot htrace hstaged) as
    (_hadequacy & _hsideConditions & hsigmaLeaves & hpiLeaves & _hbody).
  split.
  - exact
      (raw_dynamicTruthNativeSubstitutionSigmaLocalRootsOn_of_directional_leaves
        M hPA baseContext sigmaDomain piDomain sourceSigma targetSigma
        hsigmaLeaves).
  - exact
      (raw_dynamicTruthNativeSubstitutionPiLocalRootsOn_of_directional_leaves
        M hPA baseContext sigmaDomain piDomain sourcePi targetPi
        hpiLeaves).
Qed.

(** Package a body root over a witnessed PA context by replaying seven All-I
    nodes over that same context.  This is the nonempty-context counterpart
    of the older empty-context substitution proof certificate. *)
Definition rawDynamicTruthNativeSubstitutionCarriedProofCertificate
    (M : RawPAModel) (witnessList baseContext body child : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0) witnessList
    (rawProofCloseNCarriedRoot M baseContext 7 body child).

Arguments rawDynamicTruthNativeSubstitutionCarriedProofCertificate
  M witnessList baseContext body child : clear implicits.

Theorem
    raw_codedPAProofOf_dynamicTruthNativeSubstitutionField_of_body_root_on :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawDynamicTruthNativeSubstitutionBodyLocalRootOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthNativeSubstitutionFieldCode M
        sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
      certificate.
Proof.
  intros M hPA witnessList baseContext
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    hwitness [child hbody].
  set (body := rawDynamicTruthNativeSubstitutionBodyCode M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
  pose proof (raw_codedPAAxiomWitnessContext_selfShift M hPA
    witnessList baseContext hwitness) as hself.
  destruct hbody as [hcoverage hendpoint].
  pose proof (raw_proofCloseNCarriedRoot_ruleCoverage M hPA
    baseContext hself 7 body child hcoverage hendpoint) as hclosedCoverage.
  pose proof (raw_proofCloseNCarriedRoot_endpoint M hPA
    baseContext hself 7 body child hcoverage hendpoint) as hclosedEndpoint.
  exists (rawDynamicTruthNativeSubstitutionCarriedProofCertificate M
    witnessList baseContext body child).
  exists witnessList,
    (rawProofCloseNCarriedRoot M baseContext 7 body child),
    baseContext.
  split.
  - reflexivity.
  - repeat split.
    + exact hwitness.
    + exact hclosedCoverage.
    + rewrite rawDynamicTruthNativeSubstitutionFieldCode_as_all7_body.
      change (RawProofEndpoint M
        (rawProofCloseNCarriedRoot M baseContext 7 body child)
        baseContext
        (rawRestrictedTargetCloseNFormulaCode M 7 body)).
      exact hclosedEndpoint.
Qed.

(** Trace-facing ordinary-proof endpoint.  It is useful to a staged graph
    assembler which has already opened the transform and wants to retain the
    six selected carrier codes explicitly. *)
Theorem
    raw_dynamicTruthNativeSubstitutionStagedTraceFieldProof_of_body_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler
    M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot,
    RawDynamicTruthNativeSubstitutionProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi ->
    RawDynamicTruthNativeSubstitutionStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot ->
    exists certificate : M,
      RawCodedPAProofOf M
        (rawDynamicTruthNativeSubstitutionFieldCode M
          sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
        certificate.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot htrace hstaged.
  pose proof hstaged as hstagedForBody.
  pose proof hstaged as hstagedForWitness.
  destruct hstagedForWitness as
    [hwitnessed _ _ _ _ _ _ _ _ _].
  apply
    (raw_codedPAProofOf_dynamicTruthNativeSubstitutionField_of_body_root_on
      M hPA witnessList baseContext
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      hwitnessed).
  exact (raw_dynamicTruthNativeSubstitutionStagedBodyRoot_of_implication
    M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot
    htrace hstagedForBody).
Qed.

(** Exact graph-facing endpoint.  The transform is decomposed once, yielding
    one synchronized trace and the definitional equality of its field code;
    the staged kernel is then applied without changing either identity. *)
Theorem
    raw_dynamicTruthNativeSubstitutionStagedFieldProof_of_body_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler
    M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi fieldCode
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi ->
    RawDynamicTruthNativeSubstitutionFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode ->
    RawDynamicTruthNativeSubstitutionStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot nextShiftRoot ->
    exists certificate : M,
      RawCodedPAProofOf M fieldCode certificate.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi fieldCode
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot
    horbit htransform hstaged.
  destruct (raw_dynamicTruthNativeSubstitutionProofTraceAt_of_transform
    M tail predecessorLevel currentGlobalSigma currentGlobalPi fieldCode
    horbit htransform) as
    (sigmaDomain & piDomain & sourceSigma & targetSigma & sourcePi &
      targetPi & hfield & htrace).
  pose proof (raw_dynamicTruthNativeSubstitutionStagedBodyRoot_of_implication
    M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot nextShiftRoot
    htrace hstaged) as hbody.
  pose proof hstaged as hstagedForWitness.
  destruct hstagedForWitness as
    [hwitnessed _ _ _ _ _ _ _ _ _].
  destruct
    (raw_codedPAProofOf_dynamicTruthNativeSubstitutionField_of_body_root_on
      M hPA witnessList baseContext
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      hwitnessed
      hbody) as [certificate hcertificate].
  exists certificate.
  rewrite hfield.
  exact hcertificate.
Qed.

(** The residual above is intentionally not promoted to the old context-free
    proof-total compiler.  It is the Lean-aligned substitution callback: it
    requires the current six roots and the three earlier successor roots in
    one witnessed context, and it constructs only the next substitution
    field. *)

End
  PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.
