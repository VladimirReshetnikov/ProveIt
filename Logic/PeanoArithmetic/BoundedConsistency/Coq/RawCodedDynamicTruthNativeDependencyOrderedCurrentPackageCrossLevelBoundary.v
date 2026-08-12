(**
  Dependency-ordered compact endpoint with the call-site cross-level residual.

  [RawCodedDynamicTruthNativeCrossLevelCurrentPackageCompilation] weakens the
  cross-level coordinate from an implication compiler over every arbitrary
  seven-root package to the proof operation actually invoked by the staged
  successor: the genuine current master package together with its genuine
  next-local graph/proof pair.  This file installs precisely that replacement
  in the dependency-ordered trace-proof boundary.

  The other coordinates are unchanged: template agreement, the current-local
  reduced builder, the shift/substitution/axiom implication compilers, and the
  final trace-proof compiler remain explicit.  Consequently the compact
  headline below witnesses a real premise reduction at the requested target,
  rather than merely introducing an isolated adapter API.
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
  RawCodedDynamicTruthNativeSubstitutionStagedRootCompilation
  RawCodedDynamicTruthNativeSubstitutionStagedCallbackCompilation
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation
  RawCodedDynamicTruthNativeAxiomStagedCallbackCompilation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalStagedCallbackCompilation
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeDependencyOrderedTraceProofBoundary
  CompactPAUniformProvability.

Module
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelBoundary.

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
Import PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeSubstitutionStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedTraceProofBoundary.
Import PABoundedCompactPAUniformProvability.

(** The trace-proof kernel with exactly one changed coordinate.  Compare the
    third conjunct with
    [RawDynamicTruthNativeDependencyOrderedTraceProofKernelCompilers]. *)
Definition
    RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilers
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  RawCodedTemplatePAAgreement M translation /\
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation /\
  RawDynamicTruthNativeCrossLevelCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalStagedTraceProofCompiler M.

Arguments
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilers
  M translation : clear implicits.

(** The historical trace-proof bundle embeds in the reduced bundle.  All
    fields except cross-level are passed through literally; at cross-level we
    use the audited one-way call-site reduction. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilers_of_trace_proof
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedTraceProofKernelCompilers
    M translation ->
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilers
    M translation.
Proof.
  intros M hPA translation
    (hagreement & hlocal & hcrossLevel & hshift & hsubstitution & haxiom &
      hfinal).
  split; [exact hagreement |].
  split; [exact hlocal |].
  split.
  - exact
      (raw_dynamicTruthNativeCrossLevelCurrentPackageProofCompiler_of_body_implication
        M hPA hcrossLevel).
  - repeat split; assumption.
Qed.

(** Assemble the public callbacks directly, so no reconstruction of the
    stronger cross-level implication compiler is needed. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_currentPackageCrossLevel_trace_proof_kernel_compilers
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilers
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
      (raw_dynamicTruthNativeStagedNextCrossLevelCompiler_of_currentPackageProofCompiler
        M hcrossLevel).
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
      (raw_dynamicTruthNativeStagedNextFinalCompiler_of_trace_proof
        M hPA hfinal).
Qed.

Definition
    RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    exists translation : RawCodedTemplateTranslation M,
      RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilers
        M translation.

(** Model-uniform form of the premise reduction. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilersInAllModels_of_trace_proof
    :
  RawDynamicTruthNativeDependencyOrderedTraceProofKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilersInAllModels.
Proof.
  intros hold M hPA.
  destruct (hold M hPA) as [translation hmodel].
  exists translation.
  exact
    (raw_dynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilers_of_trace_proof
      M hPA translation hmodel).
Qed.

Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_currentPackageCrossLevel_trace_proof_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels.
Proof.
  intros hkernels M hPA.
  destruct (hkernels M hPA) as [translation hmodel].
  exact
    (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_currentPackageCrossLevel_trace_proof_kernel_compilers
      M hPA translation hmodel).
Qed.

(** Compact conditional endpoint with the weaker cross-level coordinate
    visible in its sole premise.  This remains conditional on all six
    proof-producing coordinates and is not an unconditional Coq proof. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_currentPackageCrossLevel_trace_proof_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilersInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hkernels.
  exact
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_callbacks
      (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_currentPackageCrossLevel_trace_proof_kernel_compilers
        hkernels)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelBoundary.
