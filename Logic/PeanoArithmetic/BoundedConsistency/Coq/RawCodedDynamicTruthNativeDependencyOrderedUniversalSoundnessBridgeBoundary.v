(**
  Discharge the final target-refutation coordinate of the dependency boundary.

  [RawCodedDynamicTruthNativeDependencyOrderedUniversalSoundnessBoundary]
  exposes three same-context proof roots at the final staged coordinate:

    1. a proof of the universal restricted-derivation soundness invariant;
    2. the fixed implication from that invariant to the graph-selected
       restricted-consistency target; and
    3. an implication from that target to bottom in the already opened
       candidate-proof context.

  The third root is now supplied unconditionally by
  [raw_dynamicTruthNativeFinalTargetRefutationRootCompiler].  This module
  therefore sharpens the public dependency bundle once more.  Its final
  residual preserves the first two roots literally, at the same graph trace,
  prerequisite package, context, and intermediate [soundnessCode].  The
  adapter appends only the canonical target-refutation root and delegates the
  remaining proof-tree composition to the previously audited three-root
  boundary.

  All six earlier dependency coordinates remain explicit.  No derivation-
  soundness proof and no consistency-from-soundness bridge is manufactured
  here; those are precisely the two final obligations still visible below.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedPALocalProofExistential
  RawCodedRestrictedPAConsistencyTripleExDescent
  RawCodedRestrictedPAProjectedFieldRefutation
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation
  RawCodedDynamicTruthNativeShiftStagedRootCompilation
  RawCodedDynamicTruthNativeSubstitutionStagedRootCompilation
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalUniversalSoundnessComposition
  RawCodedDynamicTruthNativeFinalTargetRefutationCompilation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeDependencyOrderedCallbackCompilation
  RawCodedDynamicTruthNativeDependencyOrderedUniversalSoundnessBoundary
  RawCodedDynamicTruthNativeMasterEndpoint
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  CompactPAUniformProvability.

Module
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedUniversalSoundnessBridgeBoundary.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.
Import PABoundedRawCodedRestrictedPAProjectedFieldRefutation.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalUniversalSoundnessComposition.
Import PABoundedRawCodedDynamicTruthNativeFinalTargetRefutationCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedUniversalSoundnessBoundary.
Import PABoundedRawCodedDynamicTruthNativeMasterEndpoint.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedCompactPAUniformProvability.

(** The exact two-root final residual.  The existential [soundnessCode] is
    shared by both conjuncts, so a caller cannot provide an unrelated bridge
    formula.  Both roots live in the literal canonical fields context used by
    the final staged compiler. *)
Definition RawDynamicTruthNativeFinalUniversalSoundnessBridgeCompiler
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
    exists soundnessCode soundnessRoot consistencyBridgeRoot : M,
      RawCodedPALocalProofOf M
        (rawRestrictedPAFieldsContextCode M successorNumeralCode
          (rawRestrictedPACanonicalShiftedProofContextCode
            M baseContext successorNumeralCode))
        soundnessCode soundnessRoot /\
      RawCodedPALocalProofOf M
        (rawRestrictedPAFieldsContextCode M successorNumeralCode
          (rawRestrictedPACanonicalShiftedProofContextCode
            M baseContext successorNumeralCode))
        (rawFormulaImpCode M soundnessCode nextFinal)
        consistencyBridgeRoot.

Arguments RawDynamicTruthNativeFinalUniversalSoundnessBridgeCompiler M
  : clear implicits.

(** Append the now-canonical third root.  Notice that the trace and
    prerequisites are passed unchanged to both the caller's two-root
    compiler and the unconditional refutation compiler. *)
Theorem
    raw_dynamicTruthNativeFinalUniversalSoundnessCompositionCompiler_of_bridge
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeFinalUniversalSoundnessBridgeCompiler M ->
  RawDynamicTruthNativeFinalUniversalSoundnessCompositionCompiler M.
Proof.
  intros M hPA hbridgeCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites.
  destruct (hbridgeCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites) as
    (soundnessCode & soundnessRoot & consistencyBridgeRoot &
      hsoundness & hbridge).
  exists soundnessCode, soundnessRoot, consistencyBridgeRoot,
    (rawDynamicTruthNativeFinalTargetRefutationRoot
      M nextFinal successorNumeralCode baseContext).
  split; [exact hsoundness |].
  split; [exact hbridge |].
  exact
    (raw_dynamicTruthNativeFinalTargetRefutationRootCompiler M hPA
      tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      htrace hprerequisites).
Qed.

(** The dependency-ordered bundle with all earlier kernels and the two
    remaining final roots still visible. *)
Definition
    RawDynamicTruthNativeDependencyOrderedUniversalSoundnessBridgeKernelCompilers
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  RawCodedTemplatePAAgreement M translation /\
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation /\
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalUniversalSoundnessBridgeCompiler M.

Arguments
  RawDynamicTruthNativeDependencyOrderedUniversalSoundnessBridgeKernelCompilers
  M translation : clear implicits.

(** Refine exactly the final field of the preceding universal-soundness
    boundary. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilers_of_bridge
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedUniversalSoundnessBridgeKernelCompilers
    M translation ->
  RawDynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilers
    M translation.
Proof.
  intros M hPA translation
    (hagreement & hlocal & hcrossLevel & hshift & hsubstitution & haxiom &
      hbridge).
  split; [exact hagreement |].
  split; [exact hlocal |].
  split; [exact hcrossLevel |].
  split; [exact hshift |].
  split; [exact hsubstitution |].
  split; [exact haxiom |].
  exact
    (raw_dynamicTruthNativeFinalUniversalSoundnessCompositionCompiler_of_bridge
      M hPA hbridge).
Qed.

(** Reuse the audited universal-soundness boundary after filling its third
    root. *)
Corollary
    raw_dynamicTruthNativeDependencyOrderedKernelCompilers_of_universal_soundness_bridge
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedUniversalSoundnessBridgeKernelCompilers
    M translation ->
  RawDynamicTruthNativeDependencyOrderedKernelCompilers M translation.
Proof.
  intros M hPA translation hkernels.
  exact
    (raw_dynamicTruthNativeDependencyOrderedKernelCompilers_of_universal_soundness
      M hPA translation
      (raw_dynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilers_of_bridge
        M hPA translation hkernels)).
Qed.

Corollary
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_universal_soundness_bridge
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedUniversalSoundnessBridgeKernelCompilers
    M translation ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacks M.
Proof.
  intros M hPA translation hkernels.
  exact
    (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_universal_soundness
      M hPA translation
      (raw_dynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilers_of_bridge
        M hPA translation hkernels)).
Qed.

Corollary
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_universal_soundness_bridge
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedUniversalSoundnessBridgeKernelCompilers
    M translation ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor M.
Proof.
  intros M hPA translation hkernels.
  exact
    (raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_universal_soundness
      M hPA translation
      (raw_dynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilers_of_bridge
        M hPA translation hkernels)).
Qed.

Definition
    RawDynamicTruthNativeDependencyOrderedUniversalSoundnessBridgeKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    exists translation : RawCodedTemplateTranslation M,
      RawDynamicTruthNativeDependencyOrderedUniversalSoundnessBridgeKernelCompilers
        M translation.

Theorem
    raw_dynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilersInAllModels_of_bridge
    :
  RawDynamicTruthNativeDependencyOrderedUniversalSoundnessBridgeKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilersInAllModels.
Proof.
  intros hkernels M hPA.
  destruct (hkernels M hPA) as [translation hmodel].
  exists translation.
  exact
    (raw_dynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilers_of_bridge
      M hPA translation hmodel).
Qed.

Theorem
    raw_dynamicTruthNativeDependencyOrderedKernelCompilersInAllModels_of_universal_soundness_bridge
    :
  RawDynamicTruthNativeDependencyOrderedUniversalSoundnessBridgeKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedKernelCompilersInAllModels.
Proof.
  intro hkernels.
  exact
    (raw_dynamicTruthNativeDependencyOrderedKernelCompilersInAllModels_of_universal_soundness
      (raw_dynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilersInAllModels_of_bridge
        hkernels)).
Qed.

(** Conditional compact headline with only the soundness and bridge roots
    remaining at the final coordinate. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_universal_soundness_bridge
    :
  RawDynamicTruthNativeDependencyOrderedUniversalSoundnessBridgeKernelCompilersInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hkernels.
  exact
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_universal_soundness
      (raw_dynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilersInAllModels_of_bridge
        hkernels)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedUniversalSoundnessBridgeBoundary.
