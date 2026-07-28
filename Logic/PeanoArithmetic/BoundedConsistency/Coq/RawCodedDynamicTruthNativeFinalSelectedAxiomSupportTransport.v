(**
  Transport the staged selected axiom-soundness root to the final bridge.

  The final staged prerequisites already contain a represented local proof
  of the graph-selected [nextAxiomSoundness] formula over the witnessed base
  context.  The consistency-from-universal-soundness seam, however, uses the
  canonical context reached after opening the three restricted-proof
  witnesses and then adjoining the six projected proof fields.

  This file proves that the existing root can be weakened to that exact
  bridge context.  The only exposed syntax premise is atomic adequacy of the
  newly adjoined fields formula.  Atomic adequacy of the three shifted heads
  and of the retained base follows from the represented context-shift trace;
  the transport itself is the already proved binder-ready context-inclusion
  weakening theorem.

  Crucially, no truth producer is added here.  The implication from selected
  pointwise axiom soundness to witnessed-context truth and the refutation of
  bottom truth remain two explicit residual proof roots.  The final adapter
  merely combines those two roots with the root already present in the
  staged prerequisites.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedFixedLevelTruthTotality
  RawCodedProofAtomicAdequacy
  RawCodedProofAtomicAdequacyStandard
  RawCodedTemplateStructuralTranslation
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPAAxiomContextSelfShift
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedPAConsistencyTripleExDescent
  RawCodedRestrictedPAConsistencyShiftOrbit
  RawCodedRestrictedPAConsistencyShiftRealization
  RawCodedRestrictedPAProjectedFieldRefutation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness.

Module
  PABoundedRawCodedDynamicTruthNativeFinalSelectedAxiomSupportTransport.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.
Import PABoundedRawCodedRestrictedPAConsistencyShiftOrbit.
Import PABoundedRawCodedRestrictedPAConsistencyShiftRealization.
Import PABoundedRawCodedRestrictedPAProjectedFieldRefutation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.

(** The two genuine truth-coherence obligations left after transporting the
    staged selected root.  There is deliberately no root parameter for
    [nextAxiomSoundness]: that proof is data already carried by the staged
    prerequisites. *)
Definition RawCoqRestrictedPASelectedAxiomContextTruthResidualSupport
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (numeralCode baseContext nextAxiomSoundness
      coherenceRoot bottomRefutationRoot : M) : Prop :=
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    (rawFormulaImpCode M nextAxiomSoundness
      (rawCoqRestrictedPAAxiomContextsTruthCode M inputs))
    coherenceRoot /\
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    (rawCoqRestrictedPABottomTruthRefutationCode M inputs)
    bottomRefutationRoot.

Arguments RawCoqRestrictedPASelectedAxiomContextTruthResidualSupport
  M inputs numeralCode baseContext nextAxiomSoundness
    coherenceRoot bottomRefutationRoot : clear implicits.

(** Pointwise transport of the staged root.  The full graph trace is retained
    because it supplies the exact numeral-code witness used to construct all
    three canonical context shifts.  The full prerequisite package is
    retained because it supplies both the witnessed base and the literal
    [nextAxiomSoundness] proof root in that same base. *)
Theorem raw_dynamicTruthNativeFinal_nextAxiomSoundnessRoot_to_bridge :
    forall (M : RawPAModel), RawPASatisfies M -> forall
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
    RawDynamicTruthNativeFinalStagedPrerequisitesOn M
      witnessList baseContext
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness ->
    RawCodedFormulaAtomicallyAdequate M
      (rawRestrictedPAProofFieldsCode M successorNumeralCode) ->
    exists transportedRoot : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPAConsistencyBridgeContextCode
          M successorNumeralCode baseContext)
        nextAxiomSoundness transportedRoot.
Proof.
  intros M hPA tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hfieldsAdequate.
  pose proof htrace as htraceCopy.
  destruct htraceCopy as
    [_ _ _ _ _ _ _ hsource].
  destruct hsource as [_ hnumeral _ _].
  pose proof hprerequisites as hprerequisitesCopy.
  destruct hprerequisitesCopy as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot & currentFinalRoot &
      nextLocalRoot & nextCrossLevelRoot & nextShiftRoot &
      nextSubstitutionRoot & nextAxiomSoundnessRoot &
      [hprefix hnextAxiomSoundnessRoot]).
  destruct hprefix as
    [hwitness _ _ _ _ _ _ _ _ _ _].
  assert (hbaseRealizable : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitness).
  }
  assert (hbaseShift : RawContextShift M baseContext baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_selfShift M hPA
      witnessList baseContext hwitness).
  }
  set (shiftedRootContext :=
    rawRestrictedPACanonicalShiftedRootContextCode
      M baseContext successorNumeralCode).
  set (shiftedWitnessContext :=
    rawRestrictedPACanonicalShiftedWitnessContextCode
      M baseContext successorNumeralCode).
  set (shiftedProofContext :=
    rawRestrictedPACanonicalShiftedProofContextCode
      M baseContext successorNumeralCode).
  assert (hcontexts : RawRestrictedPAExistentialDescentContexts M
      successorNumeralCode baseContext shiftedRootContext
      shiftedWitnessContext shiftedProofContext).
  {
    unfold shiftedRootContext, shiftedWitnessContext, shiftedProofContext.
    exact (raw_restrictedPAExistentialDescentContexts_realized
      M hPA (raw_succ M level) successorNumeralCode baseContext
      hnumeral hbaseShift).
  }
  destruct hcontexts as [_ [_ hproofShift]].
  assert (hshiftedProofRealizable :
      RawContextListRealizable M shiftedProofContext).
  {
    exact (raw_contextShift_target_realizable M
      (rawRestrictedPAAfterProofContextCode M successorNumeralCode
        shiftedWitnessContext)
      shiftedProofContext hproofShift).
  }
  assert (hshiftedProofAdequate :
      RawContextAllAtomicallyAdequate M shiftedProofContext).
  {
    exact (raw_contextShift_target_all_atomically_adequate M hPA
      (rawRestrictedPAAfterProofContextCode M successorNumeralCode
        shiftedWitnessContext)
      shiftedProofContext hproofShift).
  }
  set (bridgeContext := rawCoqRestrictedPAConsistencyBridgeContextCode
    M successorNumeralCode baseContext).
  assert (hbridgeRealizable : RawContextListRealizable M bridgeContext).
  {
    unfold bridgeContext, rawCoqRestrictedPAConsistencyBridgeContextCode,
      rawRestrictedPAFieldsContextCode.
    exact (raw_contextList_cons_realizable M hPA shiftedProofContext
      (rawRestrictedPAProofFieldsCode M successorNumeralCode)
      hshiftedProofRealizable).
  }
  assert (hbridgeAdequate :
      RawContextAllAtomicallyAdequate M bridgeContext).
  {
    unfold bridgeContext, rawCoqRestrictedPAConsistencyBridgeContextCode,
      rawRestrictedPAFieldsContextCode.
    exact (raw_contextAllAtomicallyAdequate_cons M hPA shiftedProofContext
      (rawRestrictedPAProofFieldsCode M successorNumeralCode)
      hshiftedProofAdequate hfieldsAdequate).
  }
  assert (hbaseIncluded : RawContextListIncluded M baseContext bridgeContext).
  {
    unfold bridgeContext, rawCoqRestrictedPAConsistencyBridgeContextCode,
      rawRestrictedPAFieldsContextCode, shiftedProofContext,
      rawRestrictedPACanonicalShiftedProofContextCode,
      rawRestrictedPAShiftedProofContextCode.
    repeat apply (raw_contextListIncluded_cons_target M hPA).
    exact (raw_contextListIncluded_refl M baseContext).
  }
  assert (hbridgeReady :
      RawContextBinderReady M baseContext bridgeContext).
  {
    exact (raw_contextBinderReady_of_target_all_atomically_adequate
      M hPA baseContext bridgeContext hbaseIncluded hbridgeAdequate).
  }
  destruct
    (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
      M hPA baseContext bridgeContext nextAxiomSoundness
      nextAxiomSoundnessRoot hbaseRealizable hbridgeRealizable
      hbaseIncluded hbridgeReady hnextAxiomSoundnessRoot)
    as [transportedRoot htransported].
  exists transportedRoot.
  unfold bridgeContext in htransported.
  exact htransported.
Qed.

(** Package the transported staged root with exactly the two residual roots.
    This is the smallest pointwise adapter to the older three-root support
    record.  It neither constructs nor strengthens either residual root. *)
Theorem
    raw_coqRestrictedPASelectedAxiomContextTruthSupport_of_residual :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M)
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
    RawCoqRestrictedPASelectedAxiomContextTruthResidualSupport M inputs
      successorNumeralCode baseContext nextAxiomSoundness
      coherenceRoot bottomRefutationRoot ->
    exists nextAxiomSoundnessRoot : M,
      RawCoqRestrictedPASelectedAxiomContextTruthSupport M inputs
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
  destruct (raw_dynamicTruthNativeFinal_nextAxiomSoundnessRoot_to_bridge
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
  unfold RawCoqRestrictedPASelectedAxiomContextTruthSupport.
  exact (conj hwitness
    (conj hnextAxiomSoundnessRoot
      (conj hcoherence hbottomRefutation))).
Qed.

(** A purely syntactic pointwise compiler for the one remaining adequacy
    premise.  Keeping it separate prevents the transport adapter from being
    mistaken for a truth or arithmetic producer. *)
Definition RawDynamicTruthNativeFinalBridgeFieldsHeadAdequacyCompiler
    (M : RawPAModel) : Prop :=
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
    RawCodedFormulaAtomicallyAdequate M
      (rawRestrictedPAProofFieldsCode M successorNumeralCode).

Arguments RawDynamicTruthNativeFinalBridgeFieldsHeadAdequacyCompiler M
  : clear implicits.

(** Refined support compiler: only the two genuine truth roots are returned.
    The graph trace, staged prerequisites, and lower-level code equality are
    exactly the arguments of the pre-existing three-root compiler. *)
Definition
    RawDynamicTruthNativeFinalSelectedAxiomContextTruthResidualSupportCompiler
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : Prop :=
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
    rawStructuralTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
    exists coherenceRoot bottomRefutationRoot : M,
      RawCoqRestrictedPASelectedAxiomContextTruthResidualSupport M inputs
        successorNumeralCode baseContext nextAxiomSoundness
        coherenceRoot bottomRefutationRoot.

Arguments
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthResidualSupportCompiler
    M inputs : clear implicits.

(** Compiler-level compatibility with the existing downstream seam.  The
    two premises expose precisely the unfinished work: one syntax certificate
    for the bridge head and the two truth-coherence proof roots. *)
Theorem
    raw_dynamicTruthNativeFinalSelectedAxiomContextTruthSupportCompiler_of_residual
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeFinalBridgeFieldsHeadAdequacyCompiler M ->
  forall (inputs : RawCodedTemplateStructuralInputs M),
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthResidualSupportCompiler
    M inputs ->
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthSupportCompiler
    M inputs.
Proof.
  intros M hPA hfieldsCompiler inputs hresidualCompiler
    tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel.
  pose proof (hfieldsCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites) as hfieldsAdequate.
  destruct (hresidualCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites hlevel)
    as (coherenceRoot & bottomRefutationRoot & hresidual).
  destruct
    (raw_coqRestrictedPASelectedAxiomContextTruthSupport_of_residual
      M hPA inputs tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      coherenceRoot bottomRefutationRoot
      htrace hprerequisites hfieldsAdequate hresidual)
    as [nextAxiomSoundnessRoot hsupport].
  exists nextAxiomSoundnessRoot, coherenceRoot, bottomRefutationRoot.
  exact hsupport.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeFinalSelectedAxiomSupportTransport.
