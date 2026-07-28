(**
  Dependency-aware root compilation for native formula-shift invariance.

  Lean's staged successor does not prove the shift field in isolation.  Its
  shift kernel is compiled only after the preceding six-field certificate,
  the new local field, and the new cross-level field have all been proved.
  The exact available formula is therefore

      ((previous six-field master /\ next local) /\ next cross-level).

  This file records that dependency boundary literally in the raw coded
  calculus.  All eight prerequisite roots share one witnessed PA context.
  The only mathematical residual is one trace-linked represented implication
  from that cumulative antecedent to the synchronized shift body.  The
  implication is applied in the same visible context; no witnessed tail is
  erased and no semantic truth is converted into a proof.

  The remainder is structural.  The cumulative antecedent is assembled by
  conjunction introduction, the one kernel implication is eliminated, and
  the resulting body is routed through the already checked shift proof
  shapes.  A carried eight-fold universal closure finally packages the exact
  graph-selected shift field as an ordinary PA certificate while retaining
  the original witness list and context.
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
  RawCodedPAProvability
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedProofAssumptionLeaf
  RawCodedProofBinaryConstructors
  RawCodedProofAndIConstructor
  RawCodedProofAndEConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofAndIntroduction
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTruthCertificateFinalProjection
  RawCodedTruthCertificateMasterIntroduction
  RawCodedPAAxiomContextSelfShift
  RawCodedPAProofAllNCarriedCertificates
  RawCodedDynamicTruthPairedSuccessorAdequacy
  RawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation
  RawCodedDynamicTruthNativeShiftPositiveGraph
  RawCodedDynamicTruthNativeShiftProofCompilation
  RawCodedDynamicTruthNativeShiftLeafRootCompilation.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.

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
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofAndIntroduction.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTruthCertificateFinalProjection.
Import PABoundedRawCodedTruthCertificateMasterIntroduction.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedPAProofAllNCarriedCertificates.
Import PABoundedRawCodedDynamicTruthPairedSuccessorAdequacy.
Import PABoundedRawCodedDynamicTruthPairedGlobalFormulaCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeShiftProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftLeafRootCompilation.

(** ------------------------------------------------------------------
    The exact cumulative context available to the shift kernel. *)

Definition rawDynamicTruthNativeShiftStagedAntecedentCode
    (M : RawPAModel)
    (currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel : M) : M :=
  rawFormulaAndCode M
    (rawDynamicTruthNativeCrossLevelStagedAntecedentCode M
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal)
    nextCrossLevel.

Arguments rawDynamicTruthNativeShiftStagedAntecedentCode
  M currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel
  : clear implicits.

(** Every prerequisite root is indexed by the same literal base context.
    This is the raw-code analogue of Lean's [crossContext]; in particular,
    [nextCrossLevel] cannot be imported from an unrelated proof package. *)
Record RawDynamicTruthNativeShiftStagedPrerequisitesAt
    (M : RawPAModel)
    (witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot : M) : Prop := {
  rawDynamicTruthNativeShift_staged_witnessed :
    RawCodedPAAxiomWitnessContext M witnessList baseContext;
  rawDynamicTruthNativeShift_staged_currentLocal :
    RawCodedPALocalProofOf M baseContext currentLocal currentLocalRoot;
  rawDynamicTruthNativeShift_staged_currentCrossLevel :
    RawCodedPALocalProofOf M baseContext
      currentCrossLevel currentCrossLevelRoot;
  rawDynamicTruthNativeShift_staged_currentShift :
    RawCodedPALocalProofOf M baseContext currentShift currentShiftRoot;
  rawDynamicTruthNativeShift_staged_currentSubstitution :
    RawCodedPALocalProofOf M baseContext
      currentSubstitution currentSubstitutionRoot;
  rawDynamicTruthNativeShift_staged_currentAxiomSoundness :
    RawCodedPALocalProofOf M baseContext
      currentAxiomSoundness currentAxiomSoundnessRoot;
  rawDynamicTruthNativeShift_staged_currentFinal :
    RawCodedPALocalProofOf M baseContext currentFinal currentFinalRoot;
  rawDynamicTruthNativeShift_staged_nextLocal :
    RawCodedPALocalProofOf M baseContext nextLocal nextLocalRoot;
  rawDynamicTruthNativeShift_staged_nextCrossLevel :
    RawCodedPALocalProofOf M baseContext
      nextCrossLevel nextCrossLevelRoot
}.

Arguments RawDynamicTruthNativeShiftStagedPrerequisitesAt
  M witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot : clear implicits.

(** A body root retains the caller's witnessed tail.  It is intentionally
    distinct from [RawDynamicTruthNativeShiftBodyLocalRootAt], whose context
    is definitionally empty. *)
Definition RawDynamicTruthNativeShiftBodyRootOn
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi : M) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthNativeShiftBodyCode M
        sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
      root.

Arguments RawDynamicTruthNativeShiftBodyRootOn
  M baseContext sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi : clear implicits.

(** One implication is the exact proof-producing boundary of the staged
    shift induction kernel.  It synchronizes all four directional laws by
    targeting their common shift body, rather than accepting four unrelated
    leaf compilers. *)
Definition RawDynamicTruthNativeShiftStagedBodyImplicationRootOn
    (M : RawPAModel)
    (baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi : M)
    : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M baseContext
      (rawFormulaImpCode M
        (rawDynamicTruthNativeShiftStagedAntecedentCode M
          currentLocal currentCrossLevel currentShift currentSubstitution
          currentAxiomSoundness currentFinal nextLocal nextCrossLevel)
        (rawDynamicTruthNativeShiftBodyCode M
          sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi))
      root.

Arguments RawDynamicTruthNativeShiftStagedBodyImplicationRootOn
  M baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
  : clear implicits.

(** The residual stays linked to the exact orbit/application trace which
    selected the six carrier formulas appearing in the shift body. *)
Definition RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot,
    RawDynamicTruthNativeShiftProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi ->
    RawDynamicTruthNativeShiftStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot ->
    RawDynamicTruthNativeShiftStagedBodyImplicationRootOn M baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi.

Arguments RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler
  M : clear implicits.

(** Assemble the exact [crossContext] antecedent in the shared context and
    apply the single residual implication. *)
Theorem raw_dynamicTruthNativeShiftStagedBodyRoot_of_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot,
    RawDynamicTruthNativeShiftProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi ->
    RawDynamicTruthNativeShiftStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot ->
    RawDynamicTruthNativeShiftBodyRootOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot htrace hstaged.
  destruct hstaged as
    [hwitnessed hcurrentLocal hcurrentCross hcurrentShift
      hcurrentSubstitution hcurrentAxiom hcurrentFinal hnextLocal
      hnextCross].
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
    nextCrossLevelRoot hlocalContext hnextCross) as hantecedent.
  assert (hstagedAgain :
      RawDynamicTruthNativeShiftStagedPrerequisitesAt M
        witnessList baseContext
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal nextLocal nextCrossLevel
        currentLocalRoot currentCrossLevelRoot currentShiftRoot
        currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
        nextLocalRoot nextCrossLevelRoot).
  {
    constructor; assumption.
  }
  destruct (hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot htrace hstagedAgain) as
    [implicationRoot himplication].
  set (antecedent := rawDynamicTruthNativeShiftStagedAntecedentCode M
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel).
  set (body := rawDynamicTruthNativeShiftBodyCode M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
  exists (rawProofImpERoot M baseContext antecedent body
    implicationRoot
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
      nextCrossLevelRoot)).
  exact (raw_codedPALocalProofOf_impE M hPA baseContext
    antecedent body implicationRoot
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
    himplication hantecedent).
Qed.

(** ------------------------------------------------------------------
    Structural decomposition of the synchronized body. *)

(** Only the two trace-selected domain codes are non-fixed constituents of
    the five-fold shift antecedent.  This focused adequacy lemma is what
    licenses insertion of that antecedent above an arbitrary witnessed tail. *)
Lemma raw_dynamicTruthNativeShiftAntecedent_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall sigmaDomain piDomain,
  RawCodedFormulaAtomicallyAdequate M sigmaDomain ->
  RawCodedFormulaAtomicallyAdequate M piDomain ->
  RawCodedFormulaAtomicallyAdequate M
    (rawDynamicTruthNativeShiftAntecedentCode M sigmaDomain piDomain).
Proof.
  intros M hPA sigmaDomain piDomain hsigmaDomain hpiDomain.
  unfold rawDynamicTruthNativeShiftAntecedentCode,
    rawDynamicTruthNativeShiftFormulaAnd5Code,
    rawDynamicTruthNativeShiftSourceAdmissibleCode.
  apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
  - exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
      (codedFormulaShiftTermAt (tVar 0) (tVar 1) (tVar 2) (tVar 3))).
  - apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
    + exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
        (codedFormulaShiftAssignmentRelationTermAt
          (tVar 0) (tVar 1) (tVar 2)
          (tVar 4) (tVar 5) (tVar 6) (tVar 7))).
    + apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
      * apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
        -- exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
             (codedFormulaAtomicallyAdequateTermAt (tVar 2))).
        -- apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
           ++ exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
                (codedAssignmentDefinedThroughTermAt
                  (tVar 4) (tVar 5) (tVar 2))).
           ++ apply raw_formulaOrCode_atomically_adequate;
                [exact hPA | exact hsigmaDomain | exact hpiDomain].
      * apply raw_formulaAndCode_atomically_adequate; [exact hPA | |].
        -- exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
             (codedFormulaTargetAdmissibilityDataTermAt
               (tVar 3) (tVar 6) (tVar 7))).
        -- exact (raw_fixedFormulaNumeral_atomically_adequate M hPA
             (codedFormulaRankAgreementTermAt (tVar 2) (tVar 3))).
Qed.

(** Apply the synchronized body under its literal shift-data assumption and
    project the four implication roots.  The body is first transplanted by
    checked insertion; this is the point where retaining the trace-derived
    domain adequacy is essential. *)
Theorem raw_dynamicTruthNativeShiftLocalRootsOn_of_body_root : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi,
  RawContextListRealizable M baseContext ->
  RawCodedFormulaAtomicallyAdequate M sigmaDomain ->
  RawCodedFormulaAtomicallyAdequate M piDomain ->
  RawDynamicTruthNativeShiftBodyRootOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi ->
  RawDynamicTruthNativeShiftSigmaLocalRootsOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma /\
    RawDynamicTruthNativeShiftPiLocalRootsOn M baseContext
      sigmaDomain piDomain sourcePi targetPi.
Proof.
  intros M hPA baseContext sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi
    hbase hsigmaDomain hpiDomain [bodyRoot hbody].
  set (antecedent := rawDynamicTruthNativeShiftAntecedentCode M
    sigmaDomain piDomain).
  set (common := rawDynamicTruthNativeShiftCommonContextOn M baseContext
    sigmaDomain piDomain).
  set (sigmaForward := rawFormulaImpCode M sourceSigma targetSigma).
  set (sigmaBackward := rawFormulaImpCode M targetSigma sourceSigma).
  set (piForward := rawFormulaImpCode M sourcePi targetPi).
  set (piBackward := rawFormulaImpCode M targetPi sourcePi).
  set (sigmaIff := rawDynamicTruthNativeShiftFormulaIffCode M
    sourceSigma targetSigma).
  set (piIff := rawDynamicTruthNativeShiftFormulaIffCode M
    sourcePi targetPi).
  set (transport := rawFormulaAndCode M sigmaIff piIff).
  assert (hantecedentAdequate :
      RawCodedFormulaAtomicallyAdequate M antecedent).
  {
    unfold antecedent.
    exact (raw_dynamicTruthNativeShiftAntecedent_atomically_adequate
      M hPA sigmaDomain piDomain hsigmaDomain hpiDomain).
  }
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    baseContext antecedent
    (rawDynamicTruthNativeShiftBodyCode M
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

(** The staged compiler therefore supplies all four implication roots over
    the original witnessed tail.  The adequacy premises are recovered from
    the same transform trace rather than restated independently. *)
Theorem raw_dynamicTruthNativeShiftStagedLocalRoots_of_body_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot,
    RawDynamicTruthNativeShiftProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi ->
    RawDynamicTruthNativeShiftStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot ->
    RawDynamicTruthNativeShiftSigmaLocalRootsOn M baseContext
        sigmaDomain piDomain sourceSigma targetSigma /\
      RawDynamicTruthNativeShiftPiLocalRootsOn M baseContext
        sigmaDomain piDomain sourcePi targetPi.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot htrace hstaged.
  pose proof hstaged as hstagedForBody.
  destruct hstaged as
    [hwitnessed _ _ _ _ _ _ _ _].
  destruct (raw_dynamicTruthNativeShiftProofTraceAt_adequacy M hPA
    tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    htrace) as
    (_hglobalSigma & _hglobalPi & hsigmaDomain & hpiDomain &
      _hsourceSigma & _htargetSigma & _hsourcePi & _htargetPi).
  apply (raw_dynamicTruthNativeShiftLocalRootsOn_of_body_root M hPA
    baseContext sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi).
  - exact (raw_codedPAAxiomWitnessContext_context_realizable
      M witnessList baseContext hwitnessed).
  - exact hsigmaDomain.
  - exact hpiDomain.
  - exact (raw_dynamicTruthNativeShiftStagedBodyRoot_of_implication
      M hPA hcompiler tail predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot htrace hstagedForBody).
Qed.

(** ------------------------------------------------------------------
    Adapter through the directional-leaf boundary. *)

(** Turn one implication root in the shift-data context into its literal
    directional leaf.  Checked insertion retains the source formula as the
    new head, after which assumption and implication elimination are enough. *)
Lemma raw_dynamicTruthNativeShiftDirectionalLeaf_of_local_root : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain source target root,
  RawContextListRealizable M baseContext ->
  RawCodedFormulaAtomicallyAdequate M source ->
  RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftCommonContextOn M baseContext
        sigmaDomain piDomain)
      (rawFormulaImpCode M source target) root ->
  exists leaf : M,
    RawCodedPALocalProofOf M
      (rawDynamicTruthNativeShiftDirectionalContextOn M baseContext
        sigmaDomain piDomain source)
      target leaf.
Proof.
  intros M hPA baseContext sigmaDomain piDomain source target root
    hbase hsource hroot.
  set (common := rawDynamicTruthNativeShiftCommonContextOn M baseContext
    sigmaDomain piDomain).
  assert (hcommon : RawContextListRealizable M common).
  {
    unfold common.
    exact (raw_dynamicTruthNativeShiftCommonContextOn_realizable M hPA
      baseContext sigmaDomain piDomain hbase).
  }
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    common source (rawFormulaImpCode M source target) root
    hsource hcommon hroot) as [liftedRoot hlifted].
  pose proof (raw_codedPALocalProofOf_assumption M hPA common source
    hcommon) as hsourceRoot.
  exists (rawProofImpERoot M (rawListNode M source common)
    source target liftedRoot
    (rawProofAssumptionRoot M (rawListNode M source common) source)).
  exact (raw_codedPALocalProofOf_impE M hPA
    (rawListNode M source common) source target liftedRoot
    (rawProofAssumptionRoot M (rawListNode M source common) source)
    hlifted hsourceRoot).
Qed.

(** Four local roots sharing the shift-data context become exactly the two
    directional-leaf bundles consumed by the earlier leaf compiler. *)
Theorem raw_dynamicTruthNativeShiftDirectionalLeavesOn_of_local_roots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi,
  RawContextListRealizable M baseContext ->
  RawCodedFormulaAtomicallyAdequate M sourceSigma ->
  RawCodedFormulaAtomicallyAdequate M targetSigma ->
  RawCodedFormulaAtomicallyAdequate M sourcePi ->
  RawCodedFormulaAtomicallyAdequate M targetPi ->
  RawDynamicTruthNativeShiftSigmaLocalRootsOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma ->
  RawDynamicTruthNativeShiftPiLocalRootsOn M baseContext
      sigmaDomain piDomain sourcePi targetPi ->
  RawDynamicTruthNativeShiftSigmaDirectionalLeavesOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma /\
    RawDynamicTruthNativeShiftPiDirectionalLeavesOn M baseContext
      sigmaDomain piDomain sourcePi targetPi.
Proof.
  intros M hPA baseContext sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi hbase
    hsourceSigma htargetSigma hsourcePi htargetPi
    (sigmaForward & sigmaBackward & hsigmaForward & hsigmaBackward)
    (piForward & piBackward & hpiForward & hpiBackward).
  destruct (raw_dynamicTruthNativeShiftDirectionalLeaf_of_local_root
    M hPA baseContext sigmaDomain piDomain sourceSigma targetSigma
    sigmaForward hbase hsourceSigma hsigmaForward) as
    [sigmaForwardLeaf hsigmaForwardLeaf].
  destruct (raw_dynamicTruthNativeShiftDirectionalLeaf_of_local_root
    M hPA baseContext sigmaDomain piDomain targetSigma sourceSigma
    sigmaBackward hbase htargetSigma hsigmaBackward) as
    [sigmaBackwardLeaf hsigmaBackwardLeaf].
  destruct (raw_dynamicTruthNativeShiftDirectionalLeaf_of_local_root
    M hPA baseContext sigmaDomain piDomain sourcePi targetPi
    piForward hbase hsourcePi hpiForward) as
    [piForwardLeaf hpiForwardLeaf].
  destruct (raw_dynamicTruthNativeShiftDirectionalLeaf_of_local_root
    M hPA baseContext sigmaDomain piDomain targetPi sourcePi
    piBackward hbase htargetPi hpiBackward) as
    [piBackwardLeaf hpiBackwardLeaf].
  split.
  - exists sigmaForwardLeaf, sigmaBackwardLeaf.
    split; assumption.
  - exists piForwardLeaf, piBackwardLeaf.
    split; assumption.
Qed.

(** This theorem deliberately makes the detour through the public leaf
    interface and its checked implication-introduction shell.  It certifies
    that the one staged body implication really discharges the historical
    four-leaf boundary without changing any context or trace coordinate. *)
Theorem
    raw_dynamicTruthNativeShiftStagedLocalRoots_via_directional_leaves :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot,
    RawDynamicTruthNativeShiftProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi ->
    RawDynamicTruthNativeShiftStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot ->
    RawDynamicTruthNativeShiftSigmaLocalRootsOn M baseContext
        sigmaDomain piDomain sourceSigma targetSigma /\
      RawDynamicTruthNativeShiftPiLocalRootsOn M baseContext
        sigmaDomain piDomain sourcePi targetPi.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot htrace hstaged.
  pose proof hstaged as hstagedForRoots.
  destruct hstaged as
    [hwitnessed _ _ _ _ _ _ _ _].
  pose proof (raw_codedPAAxiomWitnessContext_context_realizable
    M witnessList baseContext hwitnessed) as hbase.
  destruct (raw_dynamicTruthNativeShiftProofTraceAt_adequacy M hPA
    tail predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    htrace) as
    (_hglobalSigma & _hglobalPi & _hsigmaDomain & _hpiDomain &
      hsourceSigma & htargetSigma & hsourcePi & htargetPi).
  destruct (raw_dynamicTruthNativeShiftStagedLocalRoots_of_body_implication
    M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot htrace hstagedForRoots) as
    [hsigmaRoots hpiRoots].
  destruct (raw_dynamicTruthNativeShiftDirectionalLeavesOn_of_local_roots
    M hPA baseContext sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi hbase
    hsourceSigma htargetSigma hsourcePi htargetPi
    hsigmaRoots hpiRoots) as [hsigmaLeaves hpiLeaves].
  split.
  - exact (raw_dynamicTruthNativeShiftSigmaLocalRootsOn_of_directional_leaves
      M hPA baseContext sigmaDomain piDomain sourceSigma targetSigma
      hsigmaLeaves).
  - exact (raw_dynamicTruthNativeShiftPiLocalRootsOn_of_directional_leaves
      M hPA baseContext sigmaDomain piDomain sourcePi targetPi hpiLeaves).
Qed.

(** ------------------------------------------------------------------
    Carried universal closure and ordinary-PA packaging. *)

Definition rawDynamicTruthNativeShiftStagedProofCertificate
    (M : RawPAModel) (witnessList baseContext body child : M) : M :=
  rawCodeList3 M (rawNumeralValue M 0) witnessList
    (rawProofCloseNCarriedRoot M baseContext 8 body child).

Arguments rawDynamicTruthNativeShiftStagedProofCertificate
  M witnessList baseContext body child : clear implicits.

(** A witnessed PA context is fixed by the eigenvariable shift, so the eight
    universal-introduction nodes can be replayed without replacing or
    discarding that context. *)
Theorem raw_codedPAProofOf_dynamicTruthNativeShiftField_of_body_root_on :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList baseContext sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawDynamicTruthNativeShiftBodyRootOn M baseContext
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawDynamicTruthNativeShiftFieldCode M
        sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
      certificate.
Proof.
  intros M hPA witnessList baseContext sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi hwitness
    [child [hcoverage hendpoint]].
  set (body := rawDynamicTruthNativeShiftBodyCode M
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi).
  pose proof (raw_codedPAAxiomWitnessContext_selfShift M hPA
    witnessList baseContext hwitness) as hself.
  exists (rawDynamicTruthNativeShiftStagedProofCertificate M
    witnessList baseContext body child).
  exists witnessList,
    (rawProofCloseNCarriedRoot M baseContext 8 body child), baseContext.
  split.
  - unfold rawDynamicTruthNativeShiftStagedProofCertificate. reflexivity.
  - repeat split.
    + exact hwitness.
    + exact (raw_proofCloseNCarriedRoot_ruleCoverage M hPA
        baseContext hself 8 body child hcoverage hendpoint).
    + change (RawProofEndpoint M
        (rawProofCloseNCarriedRoot M baseContext 8 body child)
        baseContext (rawRestrictedTargetCloseNFormulaCode M 8 body)).
      exact (raw_proofCloseNCarriedRoot_endpoint M hPA
        baseContext hself 8 body child hcoverage hendpoint).
Qed.

(** Final structural adapter for this stage.  The target is the literal field
    polynomial determined by the supplied shift trace; no target equality is
    postulated and no later successor field is available to the compiler. *)
Theorem
    raw_dynamicTruthNativeShiftStagedFieldProof_of_body_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi
      sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot,
    RawDynamicTruthNativeShiftProofTraceAt M tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      sourceSigma targetSigma sourcePi targetPi ->
    RawDynamicTruthNativeShiftStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot ->
    exists certificate : M,
      RawCodedPAProofOf M
        (rawDynamicTruthNativeShiftFieldCode M
          sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi)
        certificate.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot htrace hstaged.
  pose proof hstaged as hstagedForBody.
  destruct hstaged as
    [hwitnessed _ _ _ _ _ _ _ _].
  apply (raw_codedPAProofOf_dynamicTruthNativeShiftField_of_body_root_on
    M hPA witnessList baseContext sigmaDomain piDomain
    sourceSigma targetSigma sourcePi targetPi hwitnessed).
  exact (raw_dynamicTruthNativeShiftStagedBodyRoot_of_implication
    M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot htrace hstagedForBody).
Qed.

(** Graph-facing form.  The transform relation chooses the six formulas and
    the field target simultaneously.  Destructing its trace and rewriting by
    the returned target equation is the only identification performed here. *)
Theorem
    raw_dynamicTruthNativeShiftStagedTransformProof_of_body_implication :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M ->
  forall (tail : nat -> M) predecessorLevel
      currentGlobalSigma currentGlobalPi fieldCode
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot,
    RawDynamicTruthPairedGlobalFormulaCodeAdequateOrbitAt M
      tail (raw_succ M predecessorLevel)
      currentGlobalSigma currentGlobalPi ->
    RawDynamicTruthNativeShiftFieldTransformAt M
      currentGlobalSigma currentGlobalPi predecessorLevel fieldCode ->
    RawDynamicTruthNativeShiftStagedPrerequisitesAt M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal nextLocal nextCrossLevel
      currentLocalRoot currentCrossLevelRoot currentShiftRoot
      currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
      nextLocalRoot nextCrossLevelRoot ->
    exists certificate : M,
      RawCodedPAProofOf M fieldCode certificate.
Proof.
  intros M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi fieldCode
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot horbit htransform hstaged.
  destruct (raw_dynamicTruthNativeShiftProofTraceAt_of_transform M tail
    predecessorLevel currentGlobalSigma currentGlobalPi fieldCode
    horbit htransform) as
    (sigmaDomain & piDomain & sourceSigma & targetSigma & sourcePi &
      targetPi & hfield & htrace).
  rewrite hfield.
  exact (raw_dynamicTruthNativeShiftStagedFieldProof_of_body_implication
    M hPA hcompiler tail predecessorLevel
    currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain sourceSigma targetSigma sourcePi targetPi
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal nextLocal nextCrossLevel
    currentLocalRoot currentCrossLevelRoot currentShiftRoot
    currentSubstitutionRoot currentAxiomSoundnessRoot currentFinalRoot
    nextLocalRoot nextCrossLevelRoot htrace hstaged).
Qed.

End PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.
