(**
  Combine three independent call-site reductions for the native successor.

  The established combined boundary already restricts cross-level to the
  genuine current package and final to the trace-indexed V2/carried resource
  handoff.  This module additionally restricts substitution to the exact
  package visible at its public callback: the genuine current package plus
  the selected local, cross-level, and shift graph/proof pairs.

  Agreement, local, shift, axiom, and the V2-carried final coordinate are
  literally unchanged.  The direct callback assembler is important: it does
  not reconstruct the historical arbitrary nine-root substitution compiler.
  Thus the compact endpoint exposes all three reductions simultaneously and
  remains honestly conditional on every compiler premise displayed below.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation
  RawCodedDynamicTruthNativeCrossLevelCurrentPackageCompilation
  RawCodedDynamicTruthNativeShiftStagedRootCompilation
  RawCodedDynamicTruthNativeShiftStagedCallbackCompilation
  RawCodedDynamicTruthNativeSubstitutionCurrentPackageCompilation
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation
  RawCodedDynamicTruthNativeAxiomStagedCallbackCompilation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalStagedCallbackCompilation
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeDependencyOrderedTraceProofBoundary
  RawCodedDynamicTruthNativeFinalV2CarriedTraceProofCompilation
  RawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelV2CarriedBoundary
  CompactPAUniformProvability.

Module
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelSubstitutionV2CarriedBoundary.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeCrossLevelCurrentPackageCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeSubstitutionCurrentPackageCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedTraceProofBoundary.
Import
  PABoundedRawCodedDynamicTruthNativeFinalV2CarriedTraceProofCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelV2CarriedBoundary.
Import PABoundedCompactPAUniformProvability.

(** Dependency order and the six other coordinate types are preserved.  Only
    the fifth conjunct differs from the previously combined boundary. *)
Definition
    RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelSubstitutionV2CarriedKernelCompilers
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  RawCodedTemplatePAAgreement M translation /\
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation /\
  RawDynamicTruthNativeCrossLevelCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalV2CarriedTraceResourcesCompiler M hPA.

Arguments
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelSubstitutionV2CarriedKernelCompilers
  M hPA translation : clear implicits.

(** Embed the already checked cross-level/V2-carried package by applying the
    one-way substitution call-site reduction and passing every other field
    through without conversion. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelSubstitutionV2CarriedKernelCompilers_of_crossLevel_v2_carried
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelV2CarriedKernelCompilers
    M hPA translation ->
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelSubstitutionV2CarriedKernelCompilers
    M hPA translation.
Proof.
  intros M hPA translation
    (hagreement & hlocal & hcrossLevel & hshift & hsubstitution & haxiom &
      hfinal).
  split; [exact hagreement |].
  split; [exact hlocal |].
  split; [exact hcrossLevel |].
  split; [exact hshift |].
  split.
  - exact
      (raw_dynamicTruthNativeSubstitutionCurrentPackageProofCompiler_of_body_implication
        M hPA hsubstitution).
  - split; assumption.
Qed.

(** Assemble all six public successor callbacks directly from the combined
    reduced package.  The final callback is factored through the V2/carried
    trace proof, while substitution is factored through its call-site proof
    compiler. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_currentPackageCrossLevelSubstitution_v2_carried_kernel_compilers
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelSubstitutionV2CarriedKernelCompilers
    M hPA translation ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacks M.
Proof.
  intros M hPA translation
    (htranslationAgreement & hlocal & hcrossLevel & hshift &
      hsubstitution & haxiomSoundness & hfinal).
  repeat split.
  - exact
      (raw_dynamicTruthNativeStagedNextLocalCompiler_of_reduced_current_builder
        M hPA translation htranslationAgreement hlocal).
  - exact
      (raw_dynamicTruthNativeStagedNextCrossLevelCompiler_of_currentPackageProofCompiler
        M hcrossLevel).
  - exact
      (raw_dynamicTruthNativeStagedNextShiftCompiler_of_body_implication
        M hPA hshift).
  - exact
      (raw_dynamicTruthNativeStagedNextSubstitutionCompiler_of_currentPackageProofCompiler
        M hsubstitution).
  - exact
      (raw_dynamicTruthNativeStagedNextAxiomSoundnessCompiler_of_kernel_implication
        M hPA haxiomSoundness).
  - exact
      (raw_dynamicTruthNativeStagedNextFinalCompiler_of_trace_proof
        M hPA
        (raw_dynamicTruthNativeFinalStagedTraceProofCompiler_of_v2_carried_resources
          M hPA hfinal)).
Qed.

Definition
    RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelSubstitutionV2CarriedKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
    exists translation : RawCodedTemplateTranslation M,
      RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelSubstitutionV2CarriedKernelCompilers
        M hPA translation.

(** Model-uniform form of the one-coordinate package reduction. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelSubstitutionV2CarriedKernelCompilersInAllModels_of_crossLevel_v2_carried
    :
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelV2CarriedKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelSubstitutionV2CarriedKernelCompilersInAllModels.
Proof.
  intros hold M hPA.
  destruct (hold M hPA) as [translation hmodel].
  exists translation.
  exact
    (raw_dynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelSubstitutionV2CarriedKernelCompilers_of_crossLevel_v2_carried
      M hPA translation hmodel).
Qed.

Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_currentPackageCrossLevelSubstitution_v2_carried_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelSubstitutionV2CarriedKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels.
Proof.
  intros hkernels M hPA.
  destruct (hkernels M hPA) as [translation hmodel].
  exact
    (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_currentPackageCrossLevelSubstitution_v2_carried_kernel_compilers
      M hPA translation hmodel).
Qed.

(** Compact conditional endpoint with all three call-site reductions visible
    in its sole premise. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_currentPackageCrossLevelSubstitution_v2_carried_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelSubstitutionV2CarriedKernelCompilersInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hkernels.
  exact
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_callbacks
      (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_currentPackageCrossLevelSubstitution_v2_carried_kernel_compilers
        hkernels)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelSubstitutionV2CarriedBoundary.
