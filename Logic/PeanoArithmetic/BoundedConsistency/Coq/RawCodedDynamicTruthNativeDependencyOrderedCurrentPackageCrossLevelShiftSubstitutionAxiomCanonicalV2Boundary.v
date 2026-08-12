(**
  Strongest dependency boundary with every staged transform at its call site.

  This module adds the checked axiom-soundness call-site cut to the combined
  cross-level, shift, substitution, and canonical-final boundary.  The axiom
  compiler sees the genuine current six-field package and exactly the four
  graph/proof pairs returned by the preceding callbacks.  It is not required
  to handle an arbitrary ten-root package or independently chosen shifts.

  Translation agreement, local, the other three current-package compilers,
  and the canonical-extended V2 final residual are passed through literally.
  The public callback assembler invokes every reduced interface directly,
  leaving the all-model lifetime of the displayed premises explicit.
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
  RawCodedDynamicTruthNativeShiftCurrentPackageCompilation
  RawCodedDynamicTruthNativeSubstitutionCurrentPackageCompilation
  RawCodedDynamicTruthNativeAxiomSoundnessCurrentPackageCompilation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalStagedCallbackCompilation
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeDependencyOrderedTraceProofBoundary
  RawCodedDynamicTruthNativeFinalV2UnifiedCarriedResidualReduction
  RawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionCanonicalV2Boundary
  CompactPAUniformProvability.

Module
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2Boundary.

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
Import PABoundedRawCodedDynamicTruthNativeShiftCurrentPackageCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeSubstitutionCurrentPackageCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAxiomSoundnessCurrentPackageCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedTraceProofBoundary.
Import
  PABoundedRawCodedDynamicTruthNativeFinalV2UnifiedCarriedResidualReduction.
Import
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionCanonicalV2Boundary.
Import PABoundedCompactPAUniformProvability.

(** Production order is unchanged.  The sixth conjunct is the sole change
    from the preceding combined boundary. *)
Definition
    RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2KernelCompilers
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  RawCodedTemplatePAAgreement M translation /\
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation /\
  RawDynamicTruthNativeCrossLevelCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeShiftCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeSubstitutionCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeAxiomSoundnessCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeFinalV2CanonicalExtendedRemainingRuleCasesCompiler
    M hPA.

Arguments
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2KernelCompilers
  M hPA translation : clear implicits.

(** The prior strongest package embeds one way by reducing only its axiom
    coordinate.  No other field is reconstructed or converted. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2KernelCompilers_of_without_axiom_cut
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionCanonicalV2KernelCompilers
    M hPA translation ->
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2KernelCompilers
    M hPA translation.
Proof.
  intros M hPA translation
    (hagreement & hlocal & hcrossLevel & hshift & hsubstitution & haxiom &
      hfinal).
  split; [exact hagreement |].
  split; [exact hlocal |].
  split; [exact hcrossLevel |].
  split; [exact hshift |].
  split; [exact hsubstitution |].
  split.
  - exact
      (raw_dynamicTruthNativeAxiomSoundnessCurrentPackageProofCompiler_of_kernel_implication
        M hPA haxiom).
  - exact hfinal.
Qed.

(** Assemble the six public callbacks without returning through any of the
    historical arbitrary-root compilers. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_currentPackageCrossLevelShiftSubstitutionAxiom_canonical_v2_kernel_compilers
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2KernelCompilers
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

Definition
    RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2KernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
    exists translation : RawCodedTemplateTranslation M,
      RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2KernelCompilers
        M hPA translation.

Theorem
    raw_dynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2KernelCompilersInAllModels_of_without_axiom_cut
    :
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionCanonicalV2KernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2KernelCompilersInAllModels.
Proof.
  intros hold M hPA.
  destruct (hold M hPA) as [translation hmodel].
  exists translation.
  exact
    (raw_dynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2KernelCompilers_of_without_axiom_cut
      M hPA translation hmodel).
Qed.

Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_currentPackageCrossLevelShiftSubstitutionAxiom_canonical_v2_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2KernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels.
Proof.
  intros hkernels M hPA.
  destruct (hkernels M hPA) as [translation hmodel].
  exact
    (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_currentPackageCrossLevelShiftSubstitutionAxiom_canonical_v2_kernel_compilers
      M hPA translation hmodel).
Qed.

(** Strongest compact conditional endpoint currently assembled from the
    call-site cuts.  Its premise is intentionally not discharged here. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_currentPackageCrossLevelShiftSubstitutionAxiom_canonical_v2_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2KernelCompilersInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hkernels.
  exact
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_callbacks
      (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_currentPackageCrossLevelShiftSubstitutionAxiom_canonical_v2_kernel_compilers
        hkernels)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionAxiomCanonicalV2Boundary.
