(**
  Dependency-ordered endpoint with a context-flexible final coordinate.

  The historical dependency bundle requires the last stage to return a
  source-linked implication in the caller's original witnessed base.  A
  direct represented-soundness proof is an ordinary PA certificate and may
  contain additional induction instances, so its honest implementation first
  merges that certificate's hidden axiom context with the staged base.

  [RawDynamicTruthNativeFinalStagedTraceProofCompiler] is exactly the public
  interface which permits this growth: at a fixed graph trace it returns the
  final ordinary proof, hiding whichever witnessed extension was used.  This
  module substitutes that interface for only the seventh coordinate of the
  dependency bundle, reconstructs all six public callbacks, and carries the
  result to the compact uniform-provability headline.

  A second bundle specializes the final coordinate to the preferred family
  of direct universal-soundness bridges.  The family may select a different
  direct structural input at each level, which is necessary because its
  represented lower and upper numeral parameters are level-indexed.
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
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeCrossLevelStagedCallbackCompilation
  RawCodedDynamicTruthNativeShiftStagedCallbackCompilation
  RawCodedDynamicTruthNativeSubstitutionStagedCallbackCompilation
  RawCodedDynamicTruthNativeAxiomStagedCallbackCompilation
  RawCodedDynamicTruthNativeFinalStagedCallbackCompilation
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  CompactPAUniformProvability.

Module
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedTraceProofBoundary.

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
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeCrossLevelStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeSubstitutionStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import PABoundedCompactPAUniformProvability.

(** The first six fields are unchanged from the original model-local kernel
    boundary.  Only the final field is replaced by the pointwise public
    trace-proof compiler. *)
Definition RawDynamicTruthNativeDependencyOrderedTraceProofKernelCompilers
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  RawCodedTemplatePAAgreement M translation /\
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation /\
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalStagedTraceProofCompiler M.

Arguments RawDynamicTruthNativeDependencyOrderedTraceProofKernelCompilers
  M translation : clear implicits.

(** Assemble the literal public callbacks in production order. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_trace_proof_kernel_compilers
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedTraceProofKernelCompilers
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
      (raw_dynamicTruthNativeStagedNextSubstitutionCompiler_of_body_implication
        M hPA hsubstitution).
  - exact
      (raw_dynamicTruthNativeStagedNextAxiomSoundnessCompiler_of_kernel_implication
        M hPA haxiomSoundness).
  - exact
      (raw_dynamicTruthNativeStagedNextFinalCompiler_of_trace_proof
        M hPA hfinal).
Qed.

(** Replace the trace-proof field by the native direct bridge family. *)
Definition
    RawDynamicTruthNativeDependencyOrderedDirectBridgeFamilyKernelCompilers
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  RawCodedTemplatePAAgreement M translation /\
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation /\
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalGrowingUniversalSoundnessDirectBridgeFamilyCompiler
    M.

Arguments
  RawDynamicTruthNativeDependencyOrderedDirectBridgeFamilyKernelCompilers
  M translation : clear implicits.

Theorem
    raw_dynamicTruthNativeDependencyOrderedTraceProofKernelCompilers_of_direct_bridge_family
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedDirectBridgeFamilyKernelCompilers
    M translation ->
  RawDynamicTruthNativeDependencyOrderedTraceProofKernelCompilers
    M translation.
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
    (raw_dynamicTruthNativeFinalStagedTraceProofCompiler_of_growing_direct_bridge_family
      M hPA hfinal).
Qed.

Corollary
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_direct_bridge_family
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedDirectBridgeFamilyKernelCompilers
    M translation ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacks M.
Proof.
  intros M hPA translation hkernels.
  exact
    (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_trace_proof_kernel_compilers
      M hPA translation
      (raw_dynamicTruthNativeDependencyOrderedTraceProofKernelCompilers_of_direct_bridge_family
        M hPA translation hkernels)).
Qed.

(** All-model packages and their exact compact endpoints. *)
Definition
    RawDynamicTruthNativeDependencyOrderedTraceProofKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    exists translation : RawCodedTemplateTranslation M,
      RawDynamicTruthNativeDependencyOrderedTraceProofKernelCompilers
        M translation.

Definition
    RawDynamicTruthNativeDependencyOrderedDirectBridgeFamilyKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    exists translation : RawCodedTemplateTranslation M,
      RawDynamicTruthNativeDependencyOrderedDirectBridgeFamilyKernelCompilers
        M translation.

Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_trace_proof_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedTraceProofKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels.
Proof.
  intros hkernels M hPA.
  destruct (hkernels M hPA) as [translation hmodel].
  exact
    (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_trace_proof_kernel_compilers
      M hPA translation hmodel).
Qed.

Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_direct_bridge_family
    :
  RawDynamicTruthNativeDependencyOrderedDirectBridgeFamilyKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels.
Proof.
  intros hkernels M hPA.
  destruct (hkernels M hPA) as [translation hmodel].
  exact
    (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_direct_bridge_family
      M hPA translation hmodel).
Qed.

Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_trace_proof_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedTraceProofKernelCompilersInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hkernels.
  exact
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_callbacks
      (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_trace_proof_kernel_compilers
        hkernels)).
Qed.

Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_direct_bridge_family
    :
  RawDynamicTruthNativeDependencyOrderedDirectBridgeFamilyKernelCompilersInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hkernels.
  exact
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_callbacks
      (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_direct_bridge_family
        hkernels)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedTraceProofBoundary.
