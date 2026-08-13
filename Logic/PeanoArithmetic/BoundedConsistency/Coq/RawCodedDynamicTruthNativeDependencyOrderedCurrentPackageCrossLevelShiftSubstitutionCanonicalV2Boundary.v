(**
  Strongest dependency-ordered boundary from the four checked reductions.

  Cross-level, shift, and substitution now consume only the genuine staged
  current package and the graph/proof pairs produced earlier in the public
  callback order.  Final consumes only the canonical-extended V2 compiler
  for the remaining rule cases; the synchronized construction internally
  supplies the code equalities, closure remainder, and carried-consistency
  bridge which appeared in the broader trace-resource record.

  The translation agreement, reduced local builder, and axiom compiler are
  unchanged.  The callback proof below uses every reduced adapter directly,
  so none of the historical arbitrary-root interfaces or the broader final
  record is silently reconstructed.
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
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation
  RawCodedDynamicTruthNativeAxiomStagedCallbackCompilation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalStagedCallbackCompilation
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeDependencyOrderedTraceProofBoundary
  RawCodedDynamicTruthNativeFinalV2UnifiedCarriedResidualReduction
  RawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelSubstitutionV2CarriedBoundary
  CompactPAUniformProvability.

Module
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionCanonicalV2Boundary.

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
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedTraceProofBoundary.
Import
  PABoundedRawCodedDynamicTruthNativeFinalV2UnifiedCarriedResidualReduction.
Import
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelSubstitutionV2CarriedBoundary.
Import PABoundedCompactPAUniformProvability.

(** The production order is unchanged.  Coordinates three through five and
    seven are precisely the four strict reductions named in the module. *)
Definition
    RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionCanonicalV2KernelCompilers
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  RawCodedTemplatePAAgreement M translation /\
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation /\
  RawDynamicTruthNativeCrossLevelCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeShiftCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeSubstitutionCurrentPackageProofCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalV2CanonicalExtendedRemainingRuleCasesCompiler
    M hPA.

Arguments
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionCanonicalV2KernelCompilers
  M hPA translation : clear implicits.

(** Direct assembly is what preserves the premise reductions.  In
    particular, neither current-package field is strengthened to a compiler
    over independently chosen roots, and the final coordinate is sent
    through the canonical-extended residual theorem rather than a V2 record
    constructor. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_currentPackageCrossLevelShiftSubstitution_canonical_v2_kernel_compilers
    : forall (M : RawPAModel) (hPA : RawPASatisfies M),
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionCanonicalV2KernelCompilers
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
      (raw_dynamicTruthNativeStagedNextAxiomSoundnessCompiler_of_kernel_implication
        M hPA haxiomSoundness).
  - exact
      (raw_dynamicTruthNativeStagedNextFinalCompiler_of_trace_proof
        M hPA
        (raw_dynamicTruthNativeFinalStagedTraceProofCompiler_of_canonical_extended_remaining_v2
          M hPA hfinal)).
Qed.

Definition
    RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionCanonicalV2KernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
    exists translation : RawCodedTemplateTranslation M,
      RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionCanonicalV2KernelCompilers
        M hPA translation.

Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_currentPackageCrossLevelShiftSubstitution_canonical_v2_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionCanonicalV2KernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels.
Proof.
  intros hkernels M hPA.
  destruct (hkernels M hPA) as [translation hmodel].
  exact
    (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_currentPackageCrossLevelShiftSubstitution_canonical_v2_kernel_compilers
      M hPA translation hmodel).
Qed.

(** Strongest currently checked compact conditional endpoint: its single
    assumption displays the exact arbitrary-model lifetime of the six
    remaining proof-producing coordinates. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_currentPackageCrossLevelShiftSubstitution_canonical_v2_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionCanonicalV2KernelCompilersInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hkernels.
  exact
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_callbacks
      (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_currentPackageCrossLevelShiftSubstitution_canonical_v2_kernel_compilers
        hkernels)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCurrentPackageCrossLevelShiftSubstitutionCanonicalV2Boundary.
