(**
  Dependency-ordered compact endpoint with the call-site substitution cut.

  The substitution coordinate is replaced by the exact proof operation
  invoked by the public staged successor: a genuine current package followed
  by the graph/proof pairs returned at local, cross-level, and shift.  Every
  other coordinate is definitionally identical to the established
  trace-proof boundary, including its context-flexible final compiler.

  This makes the domain reduction visible in the premise of the compact
  conditional theorem.  It does not assert that the remaining coordinates
  are closed or turn any graph truth into represented proof syntax.
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
  RawCodedDynamicTruthNativeCrossLevelStagedCallbackCompilation
  RawCodedDynamicTruthNativeShiftStagedRootCompilation
  RawCodedDynamicTruthNativeShiftStagedCallbackCompilation
  RawCodedDynamicTruthNativeSubstitutionCurrentPackageCompilation
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation
  RawCodedDynamicTruthNativeAxiomStagedCallbackCompilation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalStagedCallbackCompilation
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeDependencyOrderedTraceProofBoundary
  CompactPAUniformProvability.

Module
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageSubstitutionBoundary.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeCrossLevelStagedCallbackCompilation.
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
Import PABoundedCompactPAUniformProvability.

(** The trace-proof kernel with exactly the fifth conjunct weakened. *)
Definition
    RawDynamicTruthNativeDependencyOrderedCurrentPackageSubstitutionTraceProofKernelCompilers
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  RawCodedTemplatePAAgreement M translation /\
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation /\
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalStagedTraceProofCompiler M.

Arguments
  RawDynamicTruthNativeDependencyOrderedCurrentPackageSubstitutionTraceProofKernelCompilers
  M translation : clear implicits.

(** The former trace-proof package embeds by changing only substitution. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedCurrentPackageSubstitutionTraceProofKernelCompilers_of_trace_proof
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedTraceProofKernelCompilers
    M translation ->
  RawDynamicTruthNativeDependencyOrderedCurrentPackageSubstitutionTraceProofKernelCompilers
    M translation.
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

(** Assemble the public callbacks directly.  In particular, substitution is
    not strengthened back to the arbitrary linked implication compiler. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_currentPackageSubstitution_trace_proof_kernel_compilers
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedCurrentPackageSubstitutionTraceProofKernelCompilers
    M translation ->
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
      (raw_dynamicTruthNativeStagedNextCrossLevelCompiler_of_body_implication
        M hPA hcrossLevel).
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
        M hPA hfinal).
Qed.

Definition
    RawDynamicTruthNativeDependencyOrderedCurrentPackageSubstitutionTraceProofKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    exists translation : RawCodedTemplateTranslation M,
      RawDynamicTruthNativeDependencyOrderedCurrentPackageSubstitutionTraceProofKernelCompilers
        M translation.

(** Model-uniform compatibility projection. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedCurrentPackageSubstitutionTraceProofKernelCompilersInAllModels_of_trace_proof
    :
  RawDynamicTruthNativeDependencyOrderedTraceProofKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedCurrentPackageSubstitutionTraceProofKernelCompilersInAllModels.
Proof.
  intros hold M hPA.
  destruct (hold M hPA) as [translation hmodel].
  exists translation.
  exact
    (raw_dynamicTruthNativeDependencyOrderedCurrentPackageSubstitutionTraceProofKernelCompilers_of_trace_proof
      M hPA translation hmodel).
Qed.

Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_currentPackageSubstitution_trace_proof_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedCurrentPackageSubstitutionTraceProofKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels.
Proof.
  intros hkernels M hPA.
  destruct (hkernels M hPA) as [translation hmodel].
  exact
    (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_currentPackageSubstitution_trace_proof_kernel_compilers
      M hPA translation hmodel).
Qed.

(** Compact conditional endpoint with the reduced substitution coordinate in
    its sole premise. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_currentPackageSubstitution_trace_proof_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedCurrentPackageSubstitutionTraceProofKernelCompilersInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hkernels.
  exact
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_callbacks
      (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_currentPackageSubstitution_trace_proof_kernel_compilers
        hkernels)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageSubstitutionBoundary.
