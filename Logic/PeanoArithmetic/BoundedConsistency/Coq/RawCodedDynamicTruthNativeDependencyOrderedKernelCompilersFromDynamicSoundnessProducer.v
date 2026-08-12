(**
  Replace the final source-linked callback by the canonical dynamic-soundness
  producer.

  The ordinary dependency-ordered kernel has six upstream fields followed by
  [RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler].  The
  preceding adapter proves that final field from
  [RawRestrictedPADynamicSoundnessProducer], so this module exposes the
  resulting boundary without repeating the seven-field conjunction at every
  call site.
*)

From PAHF Require Import PAHF.
From Stdlib Require Import List.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CompactPAUniformProvability
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeCrossLevelStagedCallbackCompilation
  RawCodedDynamicTruthNativeCrossLevelStagedRootCompilation
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation
  RawCodedDynamicTruthNativeShiftStagedRootCompilation
  RawCodedDynamicTruthNativeSubstitutionStagedRootCompilation
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation
  RawCodedDynamicTruthNativeDependencyOrderedCallbackCompilation
  RawCodedDynamicTruthNativeFinalSourceLinkedFromDynamicSoundnessProducer
  RawCodedRestrictedPADynamicSoundnessProducer.

Module
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedKernelCompilersFromDynamicSoundnessProducer.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalSourceLinkedFromDynamicSoundnessProducer.
Import PABoundedRawCodedRestrictedPADynamicSoundnessProducer.

(** The six upstream coordinates, with the final source callback removed. *)
Definition
    RawDynamicTruthNativeDependencyOrderedKernelCompilersWithoutFinalSource
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  RawCodedTemplatePAAgreement M translation /\
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation /\
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M.

Arguments
  RawDynamicTruthNativeDependencyOrderedKernelCompilersWithoutFinalSource
  M translation : clear implicits.

Definition
    RawDynamicTruthNativeDependencyOrderedKernelCompilersWithoutFinalSourceInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    exists translation : RawCodedTemplateTranslation M,
      RawDynamicTruthNativeDependencyOrderedKernelCompilersWithoutFinalSource
        M translation.

(** Reconstruct the full kernel in one model. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedKernelCompilers_of_dynamicSoundnessProducer
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedKernelCompilersWithoutFinalSource
    M translation ->
  RawRestrictedPADynamicSoundnessProducer M ->
  RawDynamicTruthNativeDependencyOrderedKernelCompilers M translation.
Proof.
  intros M hPA translation
    hfields hproducer.
  destruct hfields as [hagreement hfields].
  destruct hfields as [hlocal hfields].
  destruct hfields as [hcrossLevel hfields].
  destruct hfields as [hshift hfields].
  destruct hfields as [hsubstitution haxiom].
  refine (conj hagreement
    (conj hlocal
      (conj hcrossLevel
        (conj hshift
          (conj hsubstitution
            (conj haxiom _)))))).
  exact
    (raw_dynamicTruthNativeFinalSourceLinkedImplicationRootCompiler_of_dynamicSoundnessProducer
      M hPA hproducer).
Qed.

(** Uniform model-indexed reconstruction. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedKernelCompilersInAllModels_of_dynamicSoundnessProducer
    : RawDynamicTruthNativeDependencyOrderedKernelCompilersWithoutFinalSourceInAllModels ->
  RawRestrictedPADynamicSoundnessProducerInAllModels ->
  RawDynamicTruthNativeDependencyOrderedKernelCompilersInAllModels.
Proof.
  intros hupstream hproducer M hPA.
  destruct (hupstream M hPA) as [translation hupstreamTranslation].
  exists translation.
  exact
    (raw_dynamicTruthNativeDependencyOrderedKernelCompilers_of_dynamicSoundnessProducer
      M hPA translation hupstreamTranslation (hproducer M hPA)).
Qed.

(** Conditional compact endpoint with exactly the six upstream kernel fields
    and the one model-uniform dynamic-soundness producer. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_kernel_compilers_and_dynamicSoundnessProducer
    : RawDynamicTruthNativeDependencyOrderedKernelCompilersWithoutFinalSourceInAllModels ->
  RawRestrictedPADynamicSoundnessProducerInAllModels ->
  Formula.BProv Formula.Ax_s nil
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intros hupstream hproducer.
  apply
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_kernel_compilers.
  exact
    (raw_dynamicTruthNativeDependencyOrderedKernelCompilersInAllModels_of_dynamicSoundnessProducer
      hupstream hproducer).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedKernelCompilersFromDynamicSoundnessProducer.
