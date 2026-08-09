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
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalTargetRefutationCompilation
  RawCodedDynamicTruthNativeFinalUniversalSoundnessComposition
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect
  RawCodedDynamicTruthNativeFinalSelectedAxiomSupportTransport
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
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalTargetRefutationCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalUniversalSoundnessComposition.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.
Import
  PABoundedRawCodedDynamicTruthNativeFinalSelectedAxiomSupportTransport.
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

(** The direct analogue of the refined structural support boundary.  The
    staged prerequisite package already contains the proof of the selected
    [nextAxiomSoundness] field.  Consequently a producer should not be asked
    to return that root a second time: its only mathematical obligations are
    the implication from the selected field to witnessed-context truth and
    the refutation of truth at bottom. *)
Definition RawCoqRestrictedPASelectedAxiomContextTruthDirectResidualSupport
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    (numeralCode baseContext nextAxiomSoundness
      coherenceRoot bottomRefutationRoot : M) : Prop :=
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    (rawFormulaImpCode M nextAxiomSoundness
      (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs))
    coherenceRoot /\
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    (rawCoqRestrictedPABottomTruthRefutationDirectCode M inputs)
    bottomRefutationRoot.

Arguments RawCoqRestrictedPASelectedAxiomContextTruthDirectResidualSupport
  M inputs numeralCode baseContext nextAxiomSoundness
    coherenceRoot bottomRefutationRoot : clear implicits.

(** Transport the staged axiom-soundness root once, then combine it with the
    two direct residual roots.  The transport is representation-neutral: it
    depends only on the staged graph, the represented context shifts, and
    atomic adequacy of the seven projected restricted-proof fields. *)
Theorem
    raw_coqRestrictedPASelectedAxiomContextTruthDirectSupport_of_residual :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      coherenceRoot bottomRefutationRoot,
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
    RawCodedFormulaAtomicallyAdequate M
      (rawRestrictedPAProofFieldsCode M successorNumeralCode) ->
    RawCoqRestrictedPASelectedAxiomContextTruthDirectResidualSupport
      M inputs successorNumeralCode baseContext nextAxiomSoundness
      coherenceRoot bottomRefutationRoot ->
    exists nextAxiomSoundnessRoot : M,
      RawCoqRestrictedPASelectedAxiomContextTruthDirectSupport M inputs
        successorNumeralCode witnessList baseContext nextAxiomSoundness
        nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot.
Proof.
  intros M hPA inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    coherenceRoot bottomRefutationRoot
    htrace hprerequisites hfieldsAdequate hresidual.
  destruct
    (raw_dynamicTruthNativeFinal_nextAxiomSoundnessRoot_to_bridge
      M hPA tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      htrace hprerequisites hfieldsAdequate)
    as [nextAxiomSoundnessRoot hnextAxiomSoundnessRoot].
  pose proof hprerequisites as hprerequisitesCopy.
  destruct hprerequisitesCopy as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot & currentFinalRoot &
      nextLocalRoot & nextCrossLevelRoot & nextShiftRoot &
      nextSubstitutionRoot & oldNextAxiomSoundnessRoot &
      [hprefix _]).
  destruct hprefix as [hwitness _ _ _ _ _ _ _ _ _ _].
  destruct hresidual as [hcoherence hbottomRefutation].
  exists nextAxiomSoundnessRoot.
  unfold RawCoqRestrictedPASelectedAxiomContextTruthDirectSupport.
  exact (conj hwitness
    (conj hnextAxiomSoundnessRoot
      (conj hcoherence hbottomRefutation))).
Qed.

(** Compiler form of the two honest direct truth obligations.  It retains
    the exact graph trace and staged base used downstream, so the two roots
    cannot be supplied for an unrelated truth selector or context. *)
Definition
    RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectResidualSupportCompiler
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
    exists coherenceRoot bottomRefutationRoot : M,
      RawCoqRestrictedPASelectedAxiomContextTruthDirectResidualSupport
        M inputs successorNumeralCode baseContext nextAxiomSoundness
        coherenceRoot bottomRefutationRoot.

Arguments
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectResidualSupportCompiler
  M inputs : clear implicits.

(** The two roots in the residual package are logically independent, but
    they share a long and important indexing discipline: both must be
    produced for the direct truth inputs selected by the same final graph
    trace, and both must live in the bridge context assembled from the same
    staged prerequisites.  Abstract that common spine once.  The
    [formulaAt] argument may inspect the selected axiom-soundness code; this
    covers the coherence implication, while a constant family covers the
    bottom-refutation law. *)
Definition RawDynamicTruthNativeFinalDirectBridgeFormulaRootCompiler
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (formulaAt : M -> M) : Prop :=
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
    exists root : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPAConsistencyBridgeContextCode
          M successorNumeralCode baseContext)
        (formulaAt nextAxiomSoundness) root.

Arguments RawDynamicTruthNativeFinalDirectBridgeFormulaRootCompiler
  M inputs formulaAt : clear implicits.

(** First honest residual: the selected axiom-soundness formula entails the
    witnessed-context truth statement for the same native truth selector. *)
Definition RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectCoherenceCompiler
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawDynamicTruthNativeFinalDirectBridgeFormulaRootCompiler M inputs
    (fun nextAxiomSoundness =>
      rawFormulaImpCode M nextAxiomSoundness
        (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs)).

Arguments
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectCoherenceCompiler
  M inputs : clear implicits.

(** Second honest residual: truth of object-level falsity is refutable for
    the selected successor truth predicate.  This formula does not inspect
    [nextAxiomSoundness], but retaining the common compiler spine guarantees
    that its proof is synchronized with the same trace and bridge context. *)
Definition RawDynamicTruthNativeFinalBottomTruthDirectRefutationCompiler
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawDynamicTruthNativeFinalDirectBridgeFormulaRootCompiler M inputs
    (fun _ => rawCoqRestrictedPABottomTruthRefutationDirectCode M inputs).

Arguments RawDynamicTruthNativeFinalBottomTruthDirectRefutationCompiler
  M inputs : clear implicits.

(** Assemble the historical two-root residual from independently reusable
    compilers.  No choice or semantic proof-to-code principle is used: both
    compilers are invoked at the literal same trace and prerequisite
    package, and their checked roots are paired directly. *)
Theorem
    raw_dynamicTruthNativeFinalSelectedAxiomContextTruthDirectResidualSupportCompiler_of_split
    : forall (M : RawPAModel)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectCoherenceCompiler
    M inputs ->
  RawDynamicTruthNativeFinalBottomTruthDirectRefutationCompiler M inputs ->
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectResidualSupportCompiler
    M inputs.
Proof.
  intros M inputs hcoherence hbottom tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel.
  destruct (hcoherence tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel) as [coherenceRoot hcoherenceRoot].
  destruct (hbottom tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel) as
    [bottomRefutationRoot hbottomRefutationRoot].
  exists coherenceRoot, bottomRefutationRoot.
  split; assumption.
Qed.

(** Conversely, the old joint compiler projects to either independent
    coordinate.  Together with the preceding theorem this records an exact
    boundary refinement, not a strengthening of the mathematical premise. *)
Theorem
    raw_dynamicTruthNativeFinalSelectedAxiomContextTruthDirectCoherenceCompiler_of_residual
    : forall (M : RawPAModel)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectResidualSupportCompiler
    M inputs ->
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectCoherenceCompiler
    M inputs.
Proof.
  intros M inputs hresidual tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel.
  destruct (hresidual tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel) as
    (coherenceRoot & bottomRefutationRoot & hcoherenceRoot & _).
  exists coherenceRoot.
  exact hcoherenceRoot.
Qed.

Theorem
    raw_dynamicTruthNativeFinalBottomTruthDirectRefutationCompiler_of_residual
    : forall (M : RawPAModel)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectResidualSupportCompiler
    M inputs ->
  RawDynamicTruthNativeFinalBottomTruthDirectRefutationCompiler M inputs.
Proof.
  intros M inputs hresidual tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel.
  destruct (hresidual tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel) as
    (coherenceRoot & bottomRefutationRoot & _ & hbottomRefutationRoot).
  exists bottomRefutationRoot.
  exact hbottomRefutationRoot.
Qed.

Corollary
    raw_dynamicTruthNativeFinalSelectedAxiomContextTruthDirectResidualSupportCompiler_iff_split
    : forall (M : RawPAModel)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectResidualSupportCompiler
      M inputs <->
    RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectCoherenceCompiler
      M inputs /\
    RawDynamicTruthNativeFinalBottomTruthDirectRefutationCompiler M inputs.
Proof.
  intros M inputs.
  split.
  - intro hresidual.
    split.
    + exact
        (raw_dynamicTruthNativeFinalSelectedAxiomContextTruthDirectCoherenceCompiler_of_residual
          M inputs hresidual).
    + exact
        (raw_dynamicTruthNativeFinalBottomTruthDirectRefutationCompiler_of_residual
          M inputs hresidual).
  - intros [hcoherence hbottom].
    exact
      (raw_dynamicTruthNativeFinalSelectedAxiomContextTruthDirectResidualSupportCompiler_of_split
        M inputs hcoherence hbottom).
Qed.

(** Reconstruct the older three-root support compiler without exposing the
    purely syntactic fields-head premise.  The graph-selected numeral trace
    discharges that premise unconditionally. *)
Theorem
    raw_dynamicTruthNativeFinalSelectedAxiomContextTruthDirectSupportCompiler_of_residual
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectResidualSupportCompiler
    M inputs ->
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectSupportCompiler
    M inputs.
Proof.
  intros M hPA inputs hresidualCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel.
  pose proof
    (raw_dynamicTruthNativeFinalBridgeFieldsHeadAdequacyCompiler M hPA
      tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      htrace hprerequisites)
    as hfieldsAdequate.
  destruct (hresidualCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel)
    as (coherenceRoot & bottomRefutationRoot & hresidual).
  destruct
    (raw_coqRestrictedPASelectedAxiomContextTruthDirectSupport_of_residual
      M hPA inputs tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      coherenceRoot bottomRefutationRoot htrace hprerequisites
      hfieldsAdequate hresidual)
    as [nextAxiomSoundnessRoot hsupport].
  exists nextAxiomSoundnessRoot, coherenceRoot, bottomRefutationRoot.
  exact hsupport.
Qed.

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

(** Preferred reduction of the direct consistency bridge.  Compared with
    the historical theorem above, the caller no longer transports the staged
    axiom root or proves adequacy of the projected fields. *)
Corollary
    raw_dynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler_of_open_and_residual
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPAConsistencyFromUniversalSoundnessDirectOpenCompiler
    M inputs ->
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectResidualSupportCompiler
    M inputs ->
  RawDynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler
    M inputs.
Proof.
  intros M hPA inputs hopen hresidual.
  exact
    (raw_dynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler_of_open_and_axiom_support
      M hPA inputs hopen
      (raw_dynamicTruthNativeFinalSelectedAxiomContextTruthDirectSupportCompiler_of_residual
        M hPA inputs hresidual)).
Qed.

(** Split form of the preferred reduction.  This is the interface used by
    independent native coherence and falsum-row compilers: either component
    can now be discharged without manufacturing the other root in the same
    implementation. *)
Corollary
    raw_dynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler_of_open_and_split_truth_support
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPAConsistencyFromUniversalSoundnessDirectOpenCompiler
    M inputs ->
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthDirectCoherenceCompiler
    M inputs ->
  RawDynamicTruthNativeFinalBottomTruthDirectRefutationCompiler M inputs ->
  RawDynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler
    M inputs.
Proof.
  intros M hPA inputs hopen hcoherence hbottom.
  exact
    (raw_dynamicTruthNativeFinalConsistencyFromUniversalSoundnessDirectCompiler_of_open_and_residual
      M hPA inputs hopen
      (raw_dynamicTruthNativeFinalSelectedAxiomContextTruthDirectResidualSupportCompiler_of_split
        M inputs hcoherence hbottom)).
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

(** Uniform pointwise producer used by the public callback adapter below.
    The compiler may grow [baseContext] internally; that grown base is hidden
    in [RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeAt]
    and is recovered only by its checked consumer. *)
Definition
    RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeCompiler
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
    RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeAt
      M inputs tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode.

Arguments
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeCompiler
  M inputs : clear implicits.

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

(** ------------------------------------------------------------------
    Consume the grown bridge in the final structural closer. *)

(** Context growth is semantically relevant, so its result must expose the
    merged witnessed base alongside the final local root.  This pointwise
    package is the exact context-flexible counterpart of
    [RawDynamicTruthNativeFinalStagedLocalProofAt]. *)
Definition RawDynamicTruthNativeFinalGrowingStagedLocalProofAt
    (M : RawPAModel) (tail : nat -> M) (level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal : M) : Prop :=
  exists mergedWitnessList mergedBaseContext finalRoot : M,
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      mergedWitnessList mergedBaseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness /\
    RawDynamicTruthNativeFinalStagedLocalProofAt M tail level
      mergedBaseContext nextFinal finalRoot.

Arguments RawDynamicTruthNativeFinalGrowingStagedLocalProofAt
  M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal : clear implicits.

(** The direct grown bridge already contains universal soundness and the
    soundness-to-target implication in the literal merged fields context.
    The independently checked target-refutation compiler supplies the third
    root there.  Two implication eliminations then give the source-linked
    proof expected by the pointwise final closer. *)
Theorem
    raw_dynamicTruthNativeFinalGrowingStagedLocalProof_of_direct_bridge :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeAt
    M inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawDynamicTruthNativeFinalGrowingStagedLocalProofAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal.
Proof.
  intros M hPA inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode htrace hbridge.
  unfold RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeAt,
    RawDynamicTruthNativeFinalGrowingUniversalSoundnessCodeBridgeAt
    in hbridge.
  destruct hbridge as
    (mergedWitnessList & mergedBaseContext & soundnessRoot &
      consistencyBridgeRoot & hmergedPrerequisites & hsoundness & hbridge).
  pose proof
    (raw_dynamicTruthNativeFinalTargetRefutationRootCompiler
      M hPA tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode mergedWitnessList mergedBaseContext
      htrace hmergedPrerequisites)
    as hrefutation.
  pose proof
    (raw_restrictedPADynamicSoundnessImplicationProof_of_universal_soundness
      M hPA successorNumeralCode
      (rawRestrictedPACanonicalShiftedProofContextCode
        M mergedBaseContext successorNumeralCode)
      nextFinal
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
      soundnessRoot consistencyBridgeRoot
      (rawDynamicTruthNativeFinalTargetRefutationRoot
        M nextFinal successorNumeralCode mergedBaseContext)
      hsoundness hbridge hrefutation)
    as hsourceLinked.
  destruct
    (raw_dynamicTruthNativeFinalStagedLocalProof_of_source_linked_implication_at
      M hPA tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode mergedWitnessList mergedBaseContext
      htrace hmergedPrerequisites hsourceLinked)
    as [finalRoot hfinal].
  exists mergedWitnessList, mergedBaseContext, finalRoot.
  split; assumption.
Qed.

(** Package the grown carried root as the exact ordinary graph/proof pair
    expected at the sixth public successor stage.  In particular, merging an
    ordinary soundness certificate no longer strands the proof one layer
    below the public callback interface. *)
Corollary
    raw_dynamicTruthNativeFinalGrowingStagedNextFinalProof_of_direct_bridge :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeAt
    M inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  exists finalCertificate : M,
    RawDynamicTruthNativeStagedNextFinalProofAt M
      tail level nextFinal finalCertificate.
Proof.
  intros M hPA inputs tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode htrace hbridge.
  destruct
    (raw_dynamicTruthNativeFinalGrowingStagedLocalProof_of_direct_bridge
      M hPA inputs tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode htrace hbridge)
    as (mergedWitnessList & mergedBaseContext & finalRoot &
      hmergedPrerequisites & hfinalGraph & hfinalRoot).
  pose proof hmergedPrerequisites as hprerequisitesCopy.
  destruct hprerequisitesCopy as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot & currentFinalRoot &
      nextLocalRoot & nextCrossLevelRoot & nextShiftRoot &
      nextSubstitutionRoot & nextAxiomSoundnessRoot & [hprefix _]).
  destruct hprefix as [hmergedWitnessed _ _ _ _ _ _ _ _ _ _].
  exists (rawCodeList3 M (rawNumeralValue M 0)
    mergedWitnessList finalRoot).
  split; [exact hfinalGraph |].
  exact (raw_codedPAProofOf_dynamicTruthNativeFinal_of_carried_root
    M mergedWitnessList mergedBaseContext nextFinal finalRoot
    hmergedWitnessed hfinalRoot).
Qed.

(** A uniform grown-bridge producer therefore implements the generic
    pointwise sixth-stage interface. *)
Theorem
    raw_dynamicTruthNativeFinalStagedTraceProofCompiler_of_growing_direct_bridge
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeCompiler
    M inputs ->
  RawDynamicTruthNativeFinalStagedTraceProofCompiler M.
Proof.
  intros M hPA inputs hcompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites.
  exact
    (raw_dynamicTruthNativeFinalGrowingStagedNextFinalProof_of_direct_bridge
      M hPA inputs tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode htrace
      (hcompiler tail level
        currentLocal currentCrossLevel currentShift currentSubstitution
        currentAxiomSoundness currentFinal
        nextLocal nextCrossLevel nextShift nextSubstitution
        nextAxiomSoundness nextFinal successorNumeralCode witnessList
        baseContext htrace hprerequisites)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.
