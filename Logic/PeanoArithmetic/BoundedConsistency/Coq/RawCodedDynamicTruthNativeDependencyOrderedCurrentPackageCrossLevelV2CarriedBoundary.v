(**
  Combine the two independent call-site reductions for the native successor.

  The cross-level boundary now consumes only the genuine current package and
  selected next-local proof.  Independently, the final boundary now consumes
  an explicit trace-indexed V2/carried resource compiler.  Their first, local,
  shift, substitution, and axiom coordinates are definitionally identical,
  so both reductions can be installed at once.

  This module is deliberately an assembler, not a new arithmetic argument.
  It exposes the strongest currently checked compact endpoint using both
  reduced coordinates and keeps every remaining compiler premise visible.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeCrossLevelCurrentPackageCompilation
  RawCodedDynamicTruthNativeShiftStagedRootCompilation
  RawCodedDynamicTruthNativeSubstitutionStagedRootCompilation
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation
  RawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelBoundary
  RawCodedDynamicTruthNativeFinalV2CarriedTraceProofCompilation
  CompactPAUniformProvability.

Import ListNotations.

Module
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelV2CarriedBoundary.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelCurrentPackageCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelBoundary.
Import
  PABoundedRawCodedDynamicTruthNativeFinalV2CarriedTraceProofCompilation.
Import PABoundedCompactPAUniformProvability.

(** Dependency order is unchanged; only fields three and seven use their
    smaller call-site interfaces. *)
Definition
    RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelV2CarriedKernelCompilers
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  RawCodedTemplatePAAgreement M translation /\
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation /\
  RawDynamicTruthNativeCrossLevelCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalV2CarriedTraceResourcesCompiler M hPA.

Arguments
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelV2CarriedKernelCompilers
  M hPA translation : clear implicits.

(** Install only the final-field adapter.  The current-package cross-level
    coordinate already has exactly the target bundle's type. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilers_of_v2_carried_resources
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelV2CarriedKernelCompilers
    M hPA translation ->
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilers
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
    (raw_dynamicTruthNativeFinalStagedTraceProofCompiler_of_v2_carried_resources
      M hPA hfinal).
Qed.

Definition
    RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelV2CarriedKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
    exists translation : RawCodedTemplateTranslation M,
      RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelV2CarriedKernelCompilers
        M hPA translation.

Theorem
    raw_dynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilersInAllModels_of_v2_carried_resources
    :
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelV2CarriedKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilersInAllModels.
Proof.
  intros hresources M hPA.
  destruct (hresources M hPA) as [translation hmodel].
  exists translation.
  exact
    (raw_dynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilers_of_v2_carried_resources
      M hPA translation hmodel).
Qed.

(** Exact compact target with both reduced coordinates visible in the sole
    premise.  The theorem remains conditional on the displayed arbitrary-
    model compiler family. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_currentPackageCrossLevel_v2_carried_resources
    :
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelV2CarriedKernelCompilersInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hresources.
  exact
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_currentPackageCrossLevel_trace_proof_kernel_compilers
      (raw_dynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelTraceProofKernelCompilersInAllModels_of_v2_carried_resources
        hresources)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelV2CarriedBoundary.
