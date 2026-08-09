(**
  Grow the final staged prerequisite package together with the open-shell
  arithmetic residual.

  The three arithmetic laws may add finite standard PA prefixes.  Their
  synchronized residual already returns the exact final witnessed context;
  the simultaneous prerequisite transport theorem moves all eleven staged
  roots to that same context.  This is the pointwise package needed before
  constructing native axiom-context coherence and bottom refutation.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedNumeralTermCode
  RawCodedRestrictedPAProof
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenIntegration
  RawCodedRestrictedPAOpenShellArithmeticCarriedResidual
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalStagedPrerequisitesWitnessedTransport.

Module
  PABoundedRawCodedRestrictedPAOpenShellArithmeticFinalPrerequisitesIntegration.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenIntegration.
Import PABoundedRawCodedRestrictedPAOpenShellArithmeticCarriedResidual.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalStagedPrerequisitesWitnessedTransport.

(** Hide the three concrete prefix descriptors while retaining their exact
    final witnessed context and the three proof roots. *)
Theorem
    raw_dynamicTruthNativeFinalStagedPrerequisites_openShell_arithmetic_growing
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      level numeralCode witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness,
  RawNumeralTermCodeAt M (raw_succ M level) numeralCode ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness ->
  exists finalWitnessList finalBaseContext
      admissibleRoot contextBoundedRoot contextAdequateRoot : M,
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      finalWitnessList finalBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness /\
    RawContextListIncluded M baseContext finalBaseContext /\
    RawCoqRestrictedPAOpenShellArithmeticResidual M inputs
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs numeralCode finalBaseContext)
      admissibleRoot contextBoundedRoot contextAdequateRoot.
Proof.
  intros M hPA inputs level numeralCode witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness hnumeral hlevel hprerequisites.
  pose proof hprerequisites as hprerequisitesCopy.
  destruct hprerequisitesCopy as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot &
      currentFinalRoot & nextLocalRoot & nextCrossLevelRoot &
      nextShiftRoot & nextSubstitutionRoot & nextAxiomSoundnessRoot &
      [hprefix _]).
  destruct hprefix as [hwitnessed _ _ _ _ _ _ _ _ _ _].
  destruct (raw_coqRestrictedPAOpenShell_arithmetic_residual_growing
    M hPA inputs level numeralCode witnessList baseContext
    hnumeral hlevel hwitnessed) as
    (boundedPrefix & adequatePrefix & admissiblePrefix &
      admissibleRoot & contextBoundedRoot & contextAdequateRoot & hgrown).
  cbn zeta in hgrown.
  destruct hgrown as [hfinalWitnessed [hincluded harithmetic]].
  set (boundedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      boundedPrefix witnessList).
  set (boundedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      boundedPrefix baseContext).
  set (adequateWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      adequatePrefix boundedWitnessList).
  set (adequateContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      adequatePrefix boundedContext).
  set (finalWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      admissiblePrefix adequateWitnessList).
  set (finalBaseContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      admissiblePrefix adequateContext).
  assert (hfinalPrerequisites :
      RawDynamicTruthNativeFinalStagedPrerequisitesOn M
        finalWitnessList finalBaseContext
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal
        nextLocal nextCrossLevel nextShift nextSubstitution
        nextAxiomSoundness).
  {
    exact
      (raw_dynamicTruthNativeFinalStagedPrerequisites_witnessed_context_transport
        M hPA witnessList baseContext finalWitnessList finalBaseContext
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal
        nextLocal nextCrossLevel nextShift nextSubstitution
        nextAxiomSoundness hprerequisites hfinalWitnessed hincluded).
  }
  exists finalWitnessList, finalBaseContext,
    admissibleRoot, contextBoundedRoot, contextAdequateRoot.
  split; [exact hfinalPrerequisites |].
  split; [exact hincluded | exact harithmetic].
Qed.

(** The staged trace supplies the successor numeral relation used by the
    arithmetic compiler, so callers need only retain the direct lower-term
    equality for their graph-selected input package. *)
Corollary
    raw_dynamicTruthNativeFinalStagedPrerequisites_openShell_arithmetic_of_trace
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  rawDirectTemplateTerm inputs
    coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness ->
  exists finalWitnessList finalBaseContext
      admissibleRoot contextBoundedRoot contextAdequateRoot : M,
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      finalWitnessList finalBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness /\
    RawContextListIncluded M baseContext finalBaseContext /\
    RawCoqRestrictedPAOpenShellArithmeticResidual M inputs
      (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
        M inputs successorNumeralCode finalBaseContext)
      admissibleRoot contextBoundedRoot contextAdequateRoot.
Proof.
  intros M hPA inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hlevel hprerequisites.
  pose proof htrace as htraceCopy.
  destruct htraceCopy as [_ _ _ _ _ _ _ hsource].
  destruct hsource as [_ hnumeral _ _].
  exact
    (raw_dynamicTruthNativeFinalStagedPrerequisites_openShell_arithmetic_growing
      M hPA inputs level successorNumeralCode witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness hnumeral hlevel hprerequisites).
Qed.

End
  PABoundedRawCodedRestrictedPAOpenShellArithmeticFinalPrerequisitesIntegration.
