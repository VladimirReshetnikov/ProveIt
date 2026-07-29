(**
  Grow the final staged context by the direct universal-soundness proof.

  The generic staged machinery already knows how to merge an ordinary PA
  certificate into the eleven-root final prerequisite context.  Its existing
  public specialization, however, fixes the older finite structural
  soundness code.  The soundness proof constructed from a genuinely
  nonstandard truth predicate has the direct code instead.

  This module factors the context-growth argument over an arbitrary fixed
  [soundnessCode], then specializes it to the exact direct code.  It also
  gives the direct analogues of the selected-axiom support compiler and the
  consistency bridge compiler, so the representation selected by direct
  strong induction is preserved through the final staged coordinate.

  The remaining open inputs are proof-producing: the selected truth support
  and the body of consistency-from-soundness.  No carrier formula is decoded,
  and the ordinary soundness certificate's hidden PA-axiom context is merged
  rather than silently identified with the staged base.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedProofAtomicAdequacy
  RawCodedProofAtomicAdequacyStandard
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPAProvability
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridge
  RawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy.

Module
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridge.
Import PABoundedRawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy.

(** ------------------------------------------------------------------
    Direct pointwise consistency compiler. *)

(** Carry the graph-selected axiom-soundness proof and the two direct truth
    coherence laws into the literal consistency-bridge context. *)
Definition
    RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectSupportCompiler
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext,
    RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode ->
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
    rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
    exists nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot : M,
      RawCoqRestrictedPASelectedAxiomContextTruthDirectSupport M inputs
        successorNumeralCode witnessList baseContext nextAxiomSoundness
        nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot.

Arguments
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectSupportCompiler
  M inputs : clear implicits.

(** The middle root needed by the final three-root composition, now fixed to
    the same direct universal-soundness code produced by strong induction. *)
Definition
    RawDynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext,
    RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode ->
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
    rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
    exists bridgeRoot : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPAConsistencyBridgeContextCode
          M successorNumeralCode baseContext)
        (rawFormulaImpCode M
          (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
          nextFinal)
        bridgeRoot.

Arguments
  RawDynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler
  M inputs : clear implicits.

Theorem
    raw_dynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler_of_open_and_axiom_support
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPAConsistencyFromUniversalSoundnessDirectOpenCompiler
    M inputs ->
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectSupportCompiler
    M inputs ->
  RawDynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler
    M inputs.
Proof.
  intros M hPA inputs hopen hsupportCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel.
  destruct (hsupportCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel) as
    (nextAxiomSoundnessRoot & coherenceRoot & bottomRefutationRoot &
      hsupport).
  pose proof htrace as htraceCopy.
  destruct htraceCopy as
    [_ _ _ _ _ _ _ hsource].
  destruct hsource as [_ _ hnextTarget _].
  destruct
    (raw_coqRestrictedPAConsistencyFromSoundnessBridgeDirect_of_open
      M hPA inputs hopen successorNumeralCode witnessList baseContext
      nextAxiomSoundness nextAxiomSoundnessRoot coherenceRoot
      bottomRefutationRoot hlevel hsupport)
    as [bridgeRoot hbridge].
  exists bridgeRoot.
  rewrite
    raw_coqRestrictedPAConsistencyFromSoundnessBridgeDirectCode_view,
    hlevel in hbridge.
  now rewrite hnextTarget.
Qed.

(** ------------------------------------------------------------------
    Representation-neutral grown-context bridge. *)

(** The context-growth proof needs only a fixed formula code and an ordinary
    PA certificate of it.  Factoring at this level avoids duplicating the
    eleven-root context merge for every soundness representation. *)
Definition RawDynamicTruthNativeFinalGrowingUniversalSoundnessCodeBridgeAt
    (M : RawPAModel) (soundnessCode : M)
    (tail : nat -> M) (level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode : M) : Prop :=
  exists mergedWitnessList mergedBaseContext
      soundnessRoot consistencyBridgeRoot : M,
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      mergedWitnessList mergedBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeContextCode M
        successorNumeralCode mergedBaseContext)
      soundnessCode soundnessRoot /\
    RawCodedPALocalProofOf M
      (rawCoqRestrictedPAConsistencyBridgeContextCode M
        successorNumeralCode mergedBaseContext)
      (rawFormulaImpCode M soundnessCode nextFinal)
      consistencyBridgeRoot.

Arguments RawDynamicTruthNativeFinalGrowingUniversalSoundnessCodeBridgeAt
  M soundnessCode tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode : clear implicits.

(** Generic context accumulation.  The last premise is pointwise in the
    newly merged base because context-sensitive consistency bridges must be
    reconstructed after the ordinary certificate's hidden axiom context is
    joined to the staged one. *)
Theorem
    raw_dynamicTruthNativeFinalGrowingUniversalSoundnessCodeBridge_of_ordinary
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      soundnessCode (tail : nat -> M) level
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
  RawCodedPAProofOf M soundnessCode soundnessCertificate ->
  RawCodedFormulaAtomicallyAdequate M
    (rawRestrictedPAProofFieldsCode M successorNumeralCode) ->
  (forall mergedWitnessList mergedBaseContext,
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      mergedWitnessList mergedBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
    exists bridgeRoot : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPAConsistencyBridgeContextCode M
          successorNumeralCode mergedBaseContext)
        (rawFormulaImpCode M soundnessCode nextFinal)
        bridgeRoot) ->
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessCodeBridgeAt
    M soundnessCode tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode.
Proof.
  intros M hPA soundnessCode tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    soundnessCertificate htrace hprerequisites hsoundnessCertificate
    hfieldsAdequate hbridgeCompiler.
  destruct
    (raw_dynamicTruthNativeFinalStagedPrerequisites_add_proof
      M hPA witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness soundnessCode soundnessCertificate
      hprerequisites hsoundnessCertificate)
    as (mergedWitnessList & mergedBaseContext & soundnessBaseRoot &
      hmergedPrerequisites & hsoundnessBase).
  pose proof hmergedPrerequisites as hmergedPrerequisitesCopy.
  destruct hmergedPrerequisitesCopy as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot & currentFinalRoot &
      nextLocalRoot & nextCrossLevelRoot & nextShiftRoot &
      nextSubstitutionRoot & nextAxiomSoundnessRoot &
      [hmergedPrefix _]).
  destruct hmergedPrefix as [hmergedWitnessed _ _ _ _ _ _ _ _ _ _].
  pose proof htrace as htraceCopy.
  destruct htraceCopy as [_ _ _ _ _ _ _ hsource].
  destruct hsource as [_ hnumeral _ _].
  destruct (raw_codedPALocalProof_to_restrictedPABridgeContext
    M hPA (raw_succ M level) successorNumeralCode
    mergedWitnessList mergedBaseContext soundnessCode soundnessBaseRoot
    hnumeral hmergedWitnessed hfieldsAdequate hsoundnessBase) as
    [soundnessRoot hsoundness].
  destruct
    (hbridgeCompiler mergedWitnessList mergedBaseContext
      hmergedPrerequisites) as
    [consistencyBridgeRoot hconsistencyBridge].
  exists mergedWitnessList, mergedBaseContext,
    soundnessRoot, consistencyBridgeRoot.
  split; [exact hmergedPrerequisites |].
  split; [exact hsoundness | exact hconsistencyBridge].
Qed.

(** ------------------------------------------------------------------
    Direct specialization. *)

Definition RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeAt
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M) (level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode : M) : Prop :=
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessCodeBridgeAt M
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode.

Arguments RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeAt
  M inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode : clear implicits.

Theorem
    raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_ordinary
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
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
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    soundnessCertificate ->
  RawCodedFormulaAtomicallyAdequate M
    (rawRestrictedPAProofFieldsCode M successorNumeralCode) ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
  RawDynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler
    M inputs ->
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeAt
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
    hfieldsAdequate hlevel hconsistencyCompiler.
  unfold RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeAt.
  apply
    (raw_dynamicTruthNativeFinalGrowingUniversalSoundnessCodeBridge_of_ordinary
      M hPA
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      soundnessCertificate htrace hprerequisites hsoundnessCertificate
      hfieldsAdequate).
  intros mergedWitnessList mergedBaseContext hmergedPrerequisites.
  exact (hconsistencyCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode mergedWitnessList mergedBaseContext
    htrace hmergedPrerequisites hlevel).
Qed.

(** The graph trace already proves atomic adequacy of the exact projected
    fields head, so the final consumer need not supply it separately. *)
Theorem
    raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_ordinary_complete_fields
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
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
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    soundnessCertificate ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
  RawDynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler
    M inputs ->
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeAt
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
    (raw_dynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridge_of_ordinary
      M hPA inputs tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      soundnessCertificate htrace hprerequisites hsoundnessCertificate
      hfieldsAdequate hlevel hconsistencyCompiler).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.
