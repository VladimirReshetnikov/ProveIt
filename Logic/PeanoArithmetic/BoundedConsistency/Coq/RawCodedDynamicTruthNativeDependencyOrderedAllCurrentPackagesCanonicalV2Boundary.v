(**
  Strongest dependency boundary with every positive stage at its call site.

  The preceding combined boundary still retained a template translation, PA
  agreement, and the reduced local staged-root builder.  The local public
  callback does not receive those coordinates.  Its exact current-package
  compiler consumes only the genuine current six-field package and returns
  one selected orbit/transform/proof triple.

  Replacing the first two coordinates by that compiler removes the final use
  of [translation] from the combined boundary.  Cross-level, shift,
  substitution, axiom soundness, and canonical-extended V2 final compilation
  are preserved literally.  Thus this module exposes six call-site residuals
  and no longer existentially quantifies an unused translation in its
  all-model premise.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplateProofCompiler
  RawCodedDynamicTruthNativeLocalCurrentPackageCompilation
  RawCodedDynamicTruthNativeCrossLevelCurrentPackageCompilation
  RawCodedDynamicTruthNativeShiftCurrentPackageCompilation
  RawCodedDynamicTruthNativeSubstitutionCurrentPackageCompilation
  RawCodedDynamicTruthNativeAxiomSoundnessCurrentPackageCompilation
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeFinalStagedCallbackCompilation
  RawCodedDynamicTruthNativeDependencyOrderedCallbackCompilation
  RawCodedDynamicTruthNativeDependencyOrderedTraceProofBoundary
  RawCodedDynamicTruthNativeFinalV2UnifiedCarriedResidualReduction
  RawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2Boundary
  CompactPAUniformProvability.

Module
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedAllCurrentPackagesCanonicalV2Boundary.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedDynamicTruthNativeLocalCurrentPackageCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeCrossLevelCurrentPackageCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftCurrentPackageCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeSubstitutionCurrentPackageCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAxiomSoundnessCurrentPackageCompilation.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeDependencyOrderedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedTraceProofBoundary.
Import
  PABoundedRawCodedDynamicTruthNativeFinalV2UnifiedCarriedResidualReduction.
Import
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2Boundary.
Import PABoundedCompactPAUniformProvability.

(** The six coordinates occur in their public dependency order.  There is no
    translation parameter: every remaining compiler is already phrased at
    its literal callback domain. *)
Definition RawDynamicTruthNativeDependencyOrderedAllCurrentPackagesCanonicalV2KernelCompilers
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  RawDynamicTruthNativeLocalCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeCrossLevelCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeShiftCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeSubstitutionCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeAxiomSoundnessCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeFinalV2CanonicalExtendedRemainingRuleCasesCompiler
    M hPA.

Arguments
  RawDynamicTruthNativeDependencyOrderedAllCurrentPackagesCanonicalV2KernelCompilers
  M hPA : clear implicits.

(** The preceding strongest package embeds by reducing only its first two
    coordinates.  Agreement and the reduced staged-root builder are consumed
    to construct the local current-package compiler; every later field is
    passed through unchanged. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedAllCurrentPackagesCanonicalV2KernelCompilers_of_reduced_local_boundary
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2KernelCompilers
    M hPA translation ->
  RawDynamicTruthNativeDependencyOrderedAllCurrentPackagesCanonicalV2KernelCompilers
    M hPA.
Proof.
  intros M hPA translation
    (hagreement & hlocal & hcrossLevel & hshift & hsubstitution & haxiom &
      hfinal).
  split.
  - exact
      (raw_dynamicTruthNativeLocalCurrentPackageProofCompiler_of_reduced_current_builder
        M hPA translation hagreement hlocal).
  - split; [exact hcrossLevel |].
    split; [exact hshift |].
    split; [exact hsubstitution |].
    split; [exact haxiom | exact hfinal].
Qed.

(** Assemble the public callbacks directly from the six call-site
    compilers.  In particular, the local field no longer passes through a
    staged-root builder at this boundary. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_all_currentPackages_canonical_v2_kernel_compilers
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeDependencyOrderedAllCurrentPackagesCanonicalV2KernelCompilers
    M hPA ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacks M.
Proof.
  intros M hPA
    (hlocal & hcrossLevel & hshift & hsubstitution & haxiomSoundness &
      hfinal).
  repeat split.
  - exact
      (raw_dynamicTruthNativeStagedNextLocalCompiler_of_currentPackageProofCompiler
        M hlocal).
  - exact
      (raw_dynamicTruthNativeStagedNextCrossLevelCompiler_of_currentPackageProofCompiler
        M hcrossLevel).
  - exact
      (raw_dynamicTruthNativeStagedNextShiftCompiler_of_currentPackageProofCompiler
        M hshift).
  - exact
      (raw_dynamicTruthNativeStagedNextSubstitutionCompiler_of_currentPackageProofCompiler
        M hsubstitution).
  - exact
      (raw_dynamicTruthNativeStagedNextAxiomSoundnessCompiler_of_currentPackageProofCompiler
        M haxiomSoundness).
  - exact
      (raw_dynamicTruthNativeStagedNextFinalCompiler_of_trace_proof
        M hPA
        (raw_dynamicTruthNativeFinalStagedTraceProofCompiler_of_canonical_extended_remaining_v2
          M hPA hfinal)).
Qed.

(** No existential translation remains in the all-model premise. *)
Definition
    RawDynamicTruthNativeDependencyOrderedAllCurrentPackagesCanonicalV2KernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
    RawDynamicTruthNativeDependencyOrderedAllCurrentPackagesCanonicalV2KernelCompilers
      M hPA.

Theorem
    raw_dynamicTruthNativeDependencyOrderedAllCurrentPackagesCanonicalV2KernelCompilersInAllModels_of_reduced_local_boundary
    :
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2KernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedAllCurrentPackagesCanonicalV2KernelCompilersInAllModels.
Proof.
  intros hold M hPA.
  destruct (hold M hPA) as [translation hmodel].
  exact
    (raw_dynamicTruthNativeDependencyOrderedAllCurrentPackagesCanonicalV2KernelCompilers_of_reduced_local_boundary
      M hPA translation hmodel).
Qed.

Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_all_currentPackages_canonical_v2_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedAllCurrentPackagesCanonicalV2KernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels.
Proof.
  intros hkernels M hPA.
  exact
    (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_all_currentPackages_canonical_v2_kernel_compilers
      M hPA (hkernels M hPA)).
Qed.

(** Compact object-language endpoint from the translation-free strongest
    call-site boundary.  Its all-model compiler premise remains explicit. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_all_currentPackages_canonical_v2_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedAllCurrentPackagesCanonicalV2KernelCompilersInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hkernels.
  exact
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_callbacks
      (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_all_currentPackages_canonical_v2_kernel_compilers
        hkernels)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedAllCurrentPackagesCanonicalV2Boundary.
