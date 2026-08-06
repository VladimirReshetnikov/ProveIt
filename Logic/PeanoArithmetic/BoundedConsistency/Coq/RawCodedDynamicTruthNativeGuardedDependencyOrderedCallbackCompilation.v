(**
  Dependency-ordered callback assembly with the guarded local coordinate.

  The historical dependency bundle routed the local field through an
  unconditional implication-predecessor formula.  The guarded local
  development instead derives the two implication collision cells from the
  actual rank-zero predecessor state.  This file plugs that corrected local
  callback into the five unchanged native coordinates and exposes exactly
  the bundle consumed by the compact uniform-provability endpoint.

  This is deliberately an assembly theorem, not a claim that the remaining
  source compilers are already closed.  In particular, the guarded reduced
  staged builder still records the non-implication collision pairs which
  have to be produced on its witnessed target context.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CompactPAUniformProvability
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedDynamicTruthNativeMasterEndpoint
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeLocalGuardedGrowingStagedCallbackCompilation.
From BoundedPAConsistency Require Import
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation
  RawCodedDynamicTruthNativeShiftStagedRootCompilation
  RawCodedDynamicTruthNativeSubstitutionStagedRootCompilation
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeCrossLevelStagedCallbackCompilation
  RawCodedDynamicTruthNativeShiftStagedCallbackCompilation
  RawCodedDynamicTruthNativeSubstitutionStagedCallbackCompilation
  RawCodedDynamicTruthNativeAxiomStagedCallbackCompilation
  RawCodedDynamicTruthNativeFinalStagedCallbackCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeGuardedDependencyOrderedCallbackCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedDynamicTruthNativeMasterEndpoint.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedGrowingStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeCrossLevelStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeShiftStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeSubstitutionStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAxiomStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalStagedCallbackCompilation.

(** The exact guarded replacement for the ordinary growing kernel bundle.
    Only its local coordinate changes; keeping the other five fields
    definitionally identical makes later source compilers reusable. *)
Definition RawDynamicTruthNativeGuardedDependencyOrderedGrowingKernelCompilers
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  RawCodedTemplatePAAgreement M translation /\
  RawDynamicTruthNativeLocalCurrentGrowingGuardedReducedStagedRootBuilder
    M translation /\
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M.

Arguments
  RawDynamicTruthNativeGuardedDependencyOrderedGrowingKernelCompilers
  M translation : clear implicits.

(** Apply each field adapter once.  In the local field this uses the guarded
    42-helper endpoint; no theorem mentioning the legacy predecessor formula
    occurs in this composition. *)
Theorem
    raw_dynamicTruthNativeGuardedDependencyOrderedPositiveCallbacks_of_growing_kernel_compilers
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeGuardedDependencyOrderedGrowingKernelCompilers
    M translation ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacks M.
Proof.
  intros M hPA translation
    (htranslationAgreement & hlocal & hcrossLevel & hshift &
      hsubstitution & haxiomSoundness & hfinal).
  repeat split.
  - exact
      (raw_dynamicTruthNativeStagedNextLocalCompiler_of_growing_guarded_reduced_current_builder
        M hPA translation htranslationAgreement hlocal).
  - exact
      (raw_dynamicTruthNativeStagedNextCrossLevelCompiler_of_body_implication
        M hPA hcrossLevel).
  - exact
      (raw_dynamicTruthNativeStagedNextShiftCompiler_of_body_implication
        M hPA hshift).
  - exact
      (raw_dynamicTruthNativeStagedNextSubstitutionCompiler_of_body_implication
        M hPA hsubstitution).
  - exact
      (raw_dynamicTruthNativeStagedNextAxiomSoundnessCompiler_of_kernel_implication
        M hPA haxiomSoundness).
  - exact
      (raw_dynamicTruthNativeStagedNextFinalCompiler_of_source_linked_implication
        M hPA hfinal).
Qed.

(** Model-local successor package, useful when a caller does not need to
    expose the intermediate callback tuple. *)
Corollary
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_guarded_growing_kernel_compilers
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeGuardedDependencyOrderedGrowingKernelCompilers
    M translation ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor M.
Proof.
  intros M hPA translation hkernels.
  exact
    (raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_dependency_ordered_callbacks
      M hPA
      (raw_dynamicTruthNativeGuardedDependencyOrderedPositiveCallbacks_of_growing_kernel_compilers
        M hPA translation hkernels)).
Qed.

(** The translation may depend on the arbitrary raw PA model. *)
Definition
    RawDynamicTruthNativeGuardedDependencyOrderedGrowingKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    exists translation : RawCodedTemplateTranslation M,
      RawDynamicTruthNativeGuardedDependencyOrderedGrowingKernelCompilers
        M translation.

Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_guarded_growing_kernel_compilers
    :
  RawDynamicTruthNativeGuardedDependencyOrderedGrowingKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels.
Proof.
  intros hkernels M hPA.
  destruct (hkernels M hPA) as [translation htranslation].
  exact
    (raw_dynamicTruthNativeGuardedDependencyOrderedPositiveCallbacks_of_growing_kernel_compilers
      M hPA translation htranslation).
Qed.

(** Exact compact target reached from the guarded dependency bundle.  The
    theorem is intentionally stated at the final object-language sentence,
    so closing this bundle later discharges the actual uniform-PA goal rather
    than a parallel semantic surrogate. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_guarded_dependency_ordered_growing_kernel_compilers
    :
  RawDynamicTruthNativeGuardedDependencyOrderedGrowingKernelCompilersInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hkernels.
  exact
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_callbacks
      (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_guarded_growing_kernel_compilers
        hkernels)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeGuardedDependencyOrderedCallbackCompilation.
