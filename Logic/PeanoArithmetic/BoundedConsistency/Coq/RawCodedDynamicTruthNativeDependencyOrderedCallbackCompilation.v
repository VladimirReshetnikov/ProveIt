(**
  Assemble the six native staged callbacks from their exact kernel seams.

  The field-specific callback files deliberately stop at one explicit
  arithmetic residual each.  This module collects precisely those residuals,
  in dependency order, and applies the six proved structural adapters.  The
  local field additionally needs a concrete template translation together
  with its PA-quotation agreement; the translation is therefore an explicit
  parameter of the model-local bundle rather than an implicit global choice.

  The resulting theorem is conditional.  In particular, the bundle still
  contains the final source-linked dynamic-soundness implication compiler.
  Nothing here assumes semantic truth-to-proof conversion, an unrestricted
  soundness producer, or a compact-consistency successor certificate.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
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
  CompactPAUniformProvability
  RawCodedDynamicTruthNativeMasterEndpoint
  RawCodedDynamicTruthNativeStagedPositiveSuccessor
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGrowingStagedCallbackCompilation
  RawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation
  RawCodedDynamicTruthNativeCrossLevelStagedCallbackCompilation
  RawCodedDynamicTruthNativeShiftStagedCallbackCompilation
  RawCodedDynamicTruthNativeSubstitutionStagedCallbackCompilation
  RawCodedDynamicTruthNativeAxiomStagedCallbackCompilation
  RawCodedDynamicTruthNativeFinalStagedCallbackCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCallbackCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedDynamicTruthNativeMasterEndpoint.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeStagedPositiveSuccessor.
Import
  PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGrowingStagedCallbackCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGrowingPredecessorStagedCallbackCompilation.
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

(** The exact model-local kernel boundary.  The conjunction order mirrors
    the order in which the public staged successor invokes its callbacks. *)
Definition RawDynamicTruthNativeDependencyOrderedKernelCompilers
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  RawCodedTemplatePAAgreement M translation /\
  RawDynamicTruthNativeLocalCurrentReducedStagedRootBuilder M translation /\
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M.

Arguments RawDynamicTruthNativeDependencyOrderedKernelCompilers
  M translation : clear implicits.

(** Preferred model-local boundary.  Global traversal and selected-row
    compilation may add finitely many PA witnesses while constructing the
    local coordinate, so the local residual uses the witnessed-extension
    builder.  The five later coordinates are unchanged. *)
Definition RawDynamicTruthNativeDependencyOrderedGrowingKernelCompilers
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  RawCodedTemplatePAAgreement M translation /\
  RawDynamicTruthNativeLocalCurrentGrowingReducedStagedRootBuilder
    M translation /\
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M.

Arguments RawDynamicTruthNativeDependencyOrderedGrowingKernelCompilers
  M translation : clear implicits.

(** Sharper growing boundary with the local predecessor coordinate split
    into its zero case, aligned positive logical roots, and the three-root
    collision remainder.  The aligned compiler is the exact destination of
    the selected-payload/global-row work. *)
Definition
    RawDynamicTruthNativeDependencyOrderedSplitPredecessorKernelCompilers
    (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop :=
  RawCodedTemplatePAAgreement M translation /\
  RawDynamicTruthNativeLocalZeroPredecessorRootCompiler M translation /\
  RawDynamicTruthNativeLocalAlignedGrowingLogicalRootsCompiler M /\
  RawDynamicTruthNativeLocalCurrentGrowingReducedStagedRemainderBuilder
    M translation /\
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M.

Arguments
  RawDynamicTruthNativeDependencyOrderedSplitPredecessorKernelCompilers
  M translation : clear implicits.

(** Assemble the relaxed growing local builder dependency-order: first choose
    and prove the predecessor root on its witnessed extension, then compile
    the remaining staged resources on that exact target context. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedGrowingKernelCompilers_of_split_predecessor
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedSplitPredecessorKernelCompilers
    M translation ->
  RawDynamicTruthNativeDependencyOrderedGrowingKernelCompilers
    M translation.
Proof.
  intros M hPA translation
    (hagreement & hzero & haligned & hremainder & hcrossLevel & hshift &
      hsubstitution & haxiom & hfinal).
  split; [exact hagreement |].
  split.
  - apply
      (raw_dynamicTruthNativeLocalCurrentGrowingReducedStagedRootBuilder_of_predecessor_and_remainder
        M translation).
    + exact
        (raw_dynamicTruthNativeLocalCurrentGrowingPredecessorRootBuilder_of_zero_and_aligned_logical_roots
          M hPA translation hzero haligned).
    + exact hremainder.
  - repeat split; assumption.
Qed.

(** The historical fixed-context bundle embeds in the growing bundle by
    selecting the source helper context as the target extension. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedGrowingKernelCompilers_of_fixed
    : forall (M : RawPAModel)
      (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedKernelCompilers M translation ->
  RawDynamicTruthNativeDependencyOrderedGrowingKernelCompilers
    M translation.
Proof.
  intros M translation
    (hagreement & hlocal & hcrossLevel & hshift & hsubstitution & haxiom &
      hfinal).
  split; [exact hagreement |].
  split.
  - exact
      (raw_dynamicTruthNativeLocalCurrentGrowingReducedStagedRootBuilder_of_fixed
        M translation hlocal).
  - repeat split; assumption.
Qed.

(** Apply each field-specific adapter once.  The conclusion is the literal
    callback bundle consumed by dependency-ordered successor assembly. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_kernel_compilers
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedKernelCompilers M translation ->
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
      (raw_dynamicTruthNativeStagedNextFinalCompiler_of_source_linked_implication
        M hPA hfinal).
Qed.

(** Dependency-ordered callback assembly using the relaxed local coordinate.
    This is the adapter needed by global-row predecessor compilers which
    honestly retain their added finite witness suffix. *)
Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_growing_kernel_compilers
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedGrowingKernelCompilers M translation ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacks M.
Proof.
  intros M hPA translation
    (htranslationAgreement & hlocal & hcrossLevel & hshift &
      hsubstitution & haxiomSoundness & hfinal).
  repeat split.
  - exact
      (raw_dynamicTruthNativeStagedNextLocalCompiler_of_growing_reduced_current_builder
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

Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_split_predecessor_kernel_compilers
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedSplitPredecessorKernelCompilers
    M translation ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacks M.
Proof.
  intros M hPA translation hkernels.
  exact
    (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_growing_kernel_compilers
      M hPA translation
      (raw_dynamicTruthNativeDependencyOrderedGrowingKernelCompilers_of_split_predecessor
        M hPA translation hkernels)).
Qed.

(** Model-local positive-component successor.  All context synchronization,
    target preservation, and six-field assembly are discharged by the
    previously proved dependency-ordered endpoint. *)
Corollary
    raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_kernel_compilers
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawDynamicTruthNativeDependencyOrderedKernelCompilers M translation ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor M.
Proof.
  intros M hPA translation hkernels.
  exact
    (raw_dynamicTruthNativeSplicedMasterPositiveComponentSuccessor_of_dependency_ordered_callbacks
      M hPA
      (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_kernel_compilers
        M hPA translation hkernels)).
Qed.

(** The all-model form permits the concrete template translation to depend on
    the raw PA model.  Its existential witness is opened only to construct
    the model-local callback bundle. *)
Definition
    RawDynamicTruthNativeDependencyOrderedKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    exists translation : RawCodedTemplateTranslation M,
      RawDynamicTruthNativeDependencyOrderedKernelCompilers M translation.

Definition
    RawDynamicTruthNativeDependencyOrderedGrowingKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    exists translation : RawCodedTemplateTranslation M,
      RawDynamicTruthNativeDependencyOrderedGrowingKernelCompilers
        M translation.

Definition
    RawDynamicTruthNativeDependencyOrderedSplitPredecessorKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    exists translation : RawCodedTemplateTranslation M,
      RawDynamicTruthNativeDependencyOrderedSplitPredecessorKernelCompilers
        M translation.

Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels.
Proof.
  intros hkernels M hPA.
  destruct (hkernels M hPA) as [translation hmodelKernels].
  exact
    (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_kernel_compilers
      M hPA translation hmodelKernels).
Qed.

Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_growing_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedGrowingKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels.
Proof.
  intros hkernels M hPA.
  destruct (hkernels M hPA) as [translation hmodelKernels].
  exact
    (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_growing_kernel_compilers
      M hPA translation hmodelKernels).
Qed.

Theorem
    raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_split_predecessor_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedSplitPredecessorKernelCompilersInAllModels ->
  RawDynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels.
Proof.
  intros hkernels M hPA.
  destruct (hkernels M hPA) as [translation hmodelKernels].
  exact
    (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacks_of_split_predecessor_kernel_compilers
      M hPA translation hmodelKernels).
Qed.

(** Exact conditional compact headline.  This does not discharge any member
    of the kernel bundle; it states that no further structural assumption is
    required after those six source-level seams have been compiled. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedKernelCompilersInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hkernels.
  exact
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_callbacks
      (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_kernel_compilers
        hkernels)).
Qed.

(** Preferred conditional compact headline.  Relative to the previous
    endpoint, its local premise has been strictly relaxed to allow exactly
    the witnessed context growth performed by native global traversal. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_growing_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedGrowingKernelCompilersInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hkernels.
  exact
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_callbacks
      (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_growing_kernel_compilers
        hkernels)).
Qed.

(** Conditional headline with the positive local predecessor mathematics
    exposed as the trace-aligned three-logical-root compiler. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_split_predecessor_kernel_compilers
    :
  RawDynamicTruthNativeDependencyOrderedSplitPredecessorKernelCompilersInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hkernels.
  exact
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dependency_ordered_callbacks
      (raw_dynamicTruthNativeDependencyOrderedPositiveCallbacksInAllModels_of_split_predecessor_kernel_compilers
        hkernels)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeDependencyOrderedCallbackCompilation.
