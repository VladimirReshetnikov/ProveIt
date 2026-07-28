(**
  Refine the dependency-ordered kernel boundary at its final coordinate.

  The original dependency bundle ends in one opaque source-linked final
  compiler.  [RawCodedDynamicTruthNativeFinalUniversalSoundnessComposition]
  has since decomposed that compiler into the exact three local roots used by
  the mathematical argument: universal derivation soundness, the fixed
  consistency bridge, and refutation of the selected target in the opened
  candidate-proof context.

  This module substitutes that sharper final package into the complete
  dependency-ordered boundary and reconnects it to the compact headline.  It
  discharges no arithmetic kernel: the five earlier field kernels and all
  three final roots remain visible.  Its purpose is to ensure that the public
  conditional theorem no longer hides the structure of the last residual.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation
  RawCodedDynamicTruthNativeShiftStagedRootCompilation
  RawCodedDynamicTruthNativeSubstitutionStagedRootCompilation
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation
  RawCodedDynamicTruthNativeFinalUniversalSoundnessComposition
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeDependencyOrderedCallbackCompilation
  RawCodedDynamicTruthNativeMasterEndpoint
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  CompactPAUniformProvability.

Module
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedUniversalSoundnessBoundary.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalUniversalSoundnessComposition.
Import
  PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeMasterEndpoint.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedCompactPAUniformProvability.

(** The first six fields are unchanged.  Only the final source-linked seam is
    replaced by its exact three-root universal-soundness decomposition. *)
Definition
    RawDynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilers
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  RawCodedTemplatePAAgreement M translation /\
  RawDynamicTruthNativeLocalCurrentStagedRootBuilder M translation /\
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalUniversalSoundnessCompositionCompiler M.

Arguments
  RawDynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilers
  M translation : clear implicits.

(** Reassemble the older exact bundle only at the final field, using the
    checked two-[ImpE]/[BotE] composition. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedKernelCompilers_of_universal_soundness
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilers
    M translation ->
  RawDynamicTruthNativeDependencyOrderedKernelCompilers M translation.
Proof.
  intros M hPA translation
    (hagreement & hlocal & hcrossLevel & hshift & hsubstitution & haxiom &
      hfinal).
  split; [exact hagreement |].
  split; [exact hlocal |].
  split; [exact hcrossLevel |].
  split; [exact hshift |].
  split; [exact hsubstitution |].
  split; [exact haxiom |].
  exact
    (raw_dynamicTruthNativeFinalSourceLinkedImplicationRootCompiler_of_universal_soundness
      M hPA hfinal).
Qed.

Corollary
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_universal_soundness
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilers
    M translation ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacks M.
Proof.
  intros M hPA translation hkernels.
  exact
    (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_kernel_compilers
      M hPA translation
      (raw_dynamicTruthNativeDependencyOrderedKernelCompilers_of_universal_soundness
        M hPA translation hkernels)).
Qed.

Corollary
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_universal_soundness
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilers
    M translation ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor M.
Proof.
  intros M hPA translation hkernels.
  exact
    (raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_kernel_compilers
      M hPA translation
      (raw_dynamicTruthNativeDependencyOrderedKernelCompilers_of_universal_soundness
        M hPA translation hkernels)).
Qed.

Definition
    RawDynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    exists translation : RawCodedTemplateTranslation M,
      RawDynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilers
        M translation.

Theorem
    raw_dynamicTruthNativeDependencyOrderedKernelCompilersInAllModels_of_universal_soundness
    :
  RawDynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedKernelCompilersInAllModels.
Proof.
  intros hkernels M hPA.
  destruct (hkernels M hPA) as [translation hmodel].
  exists translation.
  exact
    (raw_dynamicTruthNativeDependencyOrderedKernelCompilers_of_universal_soundness
      M hPA translation hmodel).
Qed.

(** Conditional compact headline with the final mathematics fully exposed.
    This theorem is not the unconditional Coq endpoint. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_universal_soundness
    :
  RawDynamicTruthNativeDependencyOrderedUniversalSoundnessKernelCompilersInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hkernels.
  exact
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_kernel_compilers
      (raw_dynamicTruthNativeDependencyOrderedKernelCompilersInAllModels_of_universal_soundness
        hkernels)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedUniversalSoundnessBoundary.
