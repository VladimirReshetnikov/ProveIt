(**
  Select the guarded rank-zero row sources once per raw PA model.

  The retained-prefix zero callback currently asks, at every normalized
  invocation, for a direct structural input package together with guarded
  evidence identification and six fixed row-source compilers (two modes for
  each of implication, conjunction, and disjunction).  The input package and
  those fixed sources are independent of the invocation's trace and
  witnessed context.  This file factors that model-global content out of the
  callback.

  There are two useful boundaries below.  The selected-source boundary is
  the weakest uniform formulation: it chooses one selector-bearing direct
  translation and supplies exactly the six fixed sources for that choice.
  The source-compiler boundary is easier for a producer to implement: it
  supplies those sources for every input package satisfying the already
  proved evidence-identification record.  The unconditional selector theorem
  then makes the choice.

  Neither adapter proves a canonical application over a bare PA context.
  In particular, the bottom direct translation is used only by the separate
  normalization coordinate; guarded evidence and fixed production continue
  to share the selector-bearing translation returned here.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateBottomDirectStructuralInputs
  RawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification
  RawCodedDynamicTruthNativeZeroGuardedFixedProductionBoundary
  RawCodedDynamicTruthNativeLocalGuardedCollisionCaseSplit
  RawCodedDynamicTruthNativeLocalGuardedBuilderDecomposition
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation
  RawCodedDynamicTruthNativeShiftStagedRootCompilation
  RawCodedDynamicTruthNativeSubstitutionStagedRootCompilation
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeGuardedDependencyOrderedCallbackCompilation.

Module
  PABoundedRawCodedDynamicTruthNativeZeroGuardedSelectedSourceCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateBottomDirectStructuralInputs.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedEvidenceIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroGuardedFixedProductionBoundary.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedCollisionCaseSplit.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedBuilderDecomposition.
Import
  PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeSubstitutionStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeGuardedDependencyOrderedCallbackCompilation.

(** One model-global choice of the direct translation used by all guarded
    rank-zero collision branches.  The second conjunct is precisely the six
    caller-independent fixed-production-or-refutation compilers at their
    literal constructor-specific prefixes. *)
Definition RawDynamicTruthNativeZeroGuardedSelectedFixedSourceResources
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    RawDynamicTruthZeroGuardedEvidenceIdentification M inputs /\
    RawDynamicTruthZeroCanonicalIdentifiedGuardedCollisionFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
      M hPA inputs.

Arguments RawDynamicTruthNativeZeroGuardedSelectedFixedSourceResources
  M hPA : clear implicits.

(** Producer-facing form.  Evidence identification is not a new proof
    obligation: the existing selector construction produces an identified
    input package in every raw PA model.  What remains here is exactly fixed
    row production (or a proof that the corresponding temporary row context
    is contradictory). *)
Definition RawDynamicTruthNativeZeroGuardedFixedSourceCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  forall inputs : RawCodedTemplateDirectStructuralInputs M,
    RawDynamicTruthZeroGuardedEvidenceIdentification M inputs ->
    RawDynamicTruthZeroCanonicalIdentifiedGuardedCollisionFixedDeepIndependentGrowingFixedProductionOrRefutationCompilers
      M hPA inputs.

Arguments RawDynamicTruthNativeZeroGuardedFixedSourceCompiler
  M hPA : clear implicits.

(** Make the selector choice once, then invoke only the proof-producing
    fixed-source compiler. *)
Theorem
    raw_dynamicTruthNativeZeroGuardedSelectedFixedSourceResources_of_compiler :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeZeroGuardedFixedSourceCompiler M hPA ->
  RawDynamicTruthNativeZeroGuardedSelectedFixedSourceResources M hPA.
Proof.
  intros M hPA hcompiler.
  destruct (raw_dynamicTruthZeroGuardedEvidenceIdentification_exists M hPA)
    as [inputs hidentification].
  exists inputs. split.
  - exact hidentification.
  - exact (hcompiler inputs hidentification).
Qed.

(** A selected model-global source package supplies every normalized zero
    invocation.  The normalized resources and canonical trace remain in the
    target API because downstream callback assembly needs their shape, but
    fixed row production does not inspect them.  This direction is
    intentionally one-way: an invocation-indexed callback could be vacuous
    in a model with no matching invocation and therefore need not determine
    one model-global source package. *)
Theorem
    raw_dynamicTruthNativeLocalZeroGuardedCollisionFixedResourcesCompilerOnNormalizedResources_of_selected_fixed_sources :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeZeroGuardedSelectedFixedSourceResources M hPA ->
  RawDynamicTruthNativeLocalZeroGuardedCollisionFixedResourcesCompilerOnNormalizedResources
    M hPA.
Proof.
  intros M hPA
    (inputs & hidentification & hfixed)
    tail witnessList baseContext helperRoots
    sigmaDomain piDomain sigmaEvidence piEvidence
    _hnormalized _htrace.
  exists inputs. split; assumption.
Qed.

(** Replace only the first coordinate of the sharp retained-assumption
    dependency bundle.  Every later coordinate is copied definitionally. *)
Definition
    RawDynamicTruthNativeGuardedDependencyOrderedSelectedFixedSourceSplitGrowingKernelCompilers
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  RawDynamicTruthNativeZeroGuardedSelectedFixedSourceResources M hPA /\
  RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnWitnessedBase
    M hPA /\
  RawDynamicTruthNativeLocalCurrentNonConditionalReducedStagedRemainderBuilder
    M (rawBottomDirectStructuralTemplateTranslation M hPA) /\
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M.

Arguments
  RawDynamicTruthNativeGuardedDependencyOrderedSelectedFixedSourceSplitGrowingKernelCompilers
  M hPA : clear implicits.

(** The proof-producing variant discharges input selection through the
    unconditional evidence-identification theorem. *)
Definition
    RawDynamicTruthNativeGuardedDependencyOrderedFixedSourceCompilerSplitGrowingKernelCompilers
    (M : RawPAModel) (hPA : RawPASatisfies M) : Prop :=
  RawDynamicTruthNativeZeroGuardedFixedSourceCompiler M hPA /\
  RawDynamicTruthNativeLocalAlignedGrowingGuardedCollisionRootsCompilerUnderCallerPrefixOnWitnessedBase
    M hPA /\
  RawDynamicTruthNativeLocalCurrentNonConditionalReducedStagedRemainderBuilder
    M (rawBottomDirectStructuralTemplateTranslation M hPA) /\
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeSubstitutionLinkedStagedBodyImplicationRootCompiler M /\
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler M /\
  RawDynamicTruthNativeFinalSourceLinkedImplicationRootCompiler M.

Arguments
  RawDynamicTruthNativeGuardedDependencyOrderedFixedSourceCompilerSplitGrowingKernelCompilers
  M hPA : clear implicits.

Theorem
    raw_dynamicTruthNativeGuardedDependencyOrderedSelectedFixedSourceSplitGrowingKernelCompilers_of_fixed_source_compiler :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeGuardedDependencyOrderedFixedSourceCompilerSplitGrowingKernelCompilers
    M hPA ->
  RawDynamicTruthNativeGuardedDependencyOrderedSelectedFixedSourceSplitGrowingKernelCompilers
    M hPA.
Proof.
  intros M hPA
    (hzero & haligned & hremainder & hcrossLevel & hshift &
      hsubstitution & haxiom & hfinal).
  split.
  - exact
      (raw_dynamicTruthNativeZeroGuardedSelectedFixedSourceResources_of_compiler
        M hPA hzero).
  - split; [exact haligned |].
    split; [exact hremainder |].
    split; [exact hcrossLevel |].
    split; [exact hshift |].
    split; [exact hsubstitution |].
    split; [exact haxiom | exact hfinal].
Qed.

(** Install the selected zero source in the existing normalized dependency
    boundary.  This theorem is the componentwise handoff used by clients of
    the guarded callback assembly. *)
Theorem
    raw_dynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilers_of_selected_fixed_sources :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeGuardedDependencyOrderedSelectedFixedSourceSplitGrowingKernelCompilers
    M hPA ->
  RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilers
    M hPA.
Proof.
  intros M hPA
    (hzero & haligned & hremainder & hcrossLevel & hshift &
      hsubstitution & haxiom & hfinal).
  split.
  - exact
      (raw_dynamicTruthNativeLocalZeroGuardedCollisionFixedResourcesCompilerOnNormalizedResources_of_selected_fixed_sources
        M hPA hzero).
  - split; [exact haligned |].
    split; [exact hremainder |].
    split; [exact hcrossLevel |].
    split; [exact hshift |].
    split; [exact hsubstitution |].
    split; [exact haxiom | exact hfinal].
Qed.

(** Direct handoff to the retained-prefix split builder.  This does not
    contract caller assumptions and hence does not recreate the historical
    unguarded zero predecessor callback. *)
Corollary
    raw_dynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingSplitGrowingKernelCompilers_of_selected_fixed_sources :
    forall (M : RawPAModel) (hPA : RawPASatisfies M),
  RawDynamicTruthNativeGuardedDependencyOrderedSelectedFixedSourceSplitGrowingKernelCompilers
    M hPA ->
  RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingSplitGrowingKernelCompilers
    M hPA.
Proof.
  intros M hPA hselected.
  exact
    (raw_dynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingSplitGrowingKernelCompilers_of_normalized_collision_resources
      M hPA
      (raw_dynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilers_of_selected_fixed_sources
        M hPA hselected)).
Qed.

(** Model-uniform forms make the reduction available without reopening the
    eight dependency coordinates at the eventual compact endpoint. *)
Definition
    RawDynamicTruthNativeGuardedDependencyOrderedSelectedFixedSourceSplitGrowingKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
    RawDynamicTruthNativeGuardedDependencyOrderedSelectedFixedSourceSplitGrowingKernelCompilers
      M hPA.

Definition
    RawDynamicTruthNativeGuardedDependencyOrderedFixedSourceCompilerSplitGrowingKernelCompilersInAllModels
    : Prop :=
  forall (M : RawPAModel) (hPA : RawPASatisfies M),
    RawDynamicTruthNativeGuardedDependencyOrderedFixedSourceCompilerSplitGrowingKernelCompilers
      M hPA.

Theorem
    raw_dynamicTruthNativeGuardedDependencyOrderedSelectedFixedSourceSplitGrowingKernelCompilersInAllModels_of_fixed_source_compilers :
  RawDynamicTruthNativeGuardedDependencyOrderedFixedSourceCompilerSplitGrowingKernelCompilersInAllModels ->
  RawDynamicTruthNativeGuardedDependencyOrderedSelectedFixedSourceSplitGrowingKernelCompilersInAllModels.
Proof.
  intros hcompilers M hPA.
  exact
    (raw_dynamicTruthNativeGuardedDependencyOrderedSelectedFixedSourceSplitGrowingKernelCompilers_of_fixed_source_compiler
      M hPA (hcompilers M hPA)).
Qed.

Theorem
    raw_dynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilersInAllModels_of_selected_fixed_sources :
  RawDynamicTruthNativeGuardedDependencyOrderedSelectedFixedSourceSplitGrowingKernelCompilersInAllModels ->
  RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilersInAllModels.
Proof.
  intros hselected M hPA.
  exact
    (raw_dynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilers_of_selected_fixed_sources
      M hPA (hselected M hPA)).
Qed.

(** One-call producer-facing composition.  Keeping it named lets the final
    endpoint consume the proof-producing source compiler without exposing
    the existential selector package, while the preceding two theorems retain
    the logically weaker selected-source factorization for reuse. *)
Corollary
    raw_dynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilersInAllModels_of_fixed_source_compilers :
  RawDynamicTruthNativeGuardedDependencyOrderedFixedSourceCompilerSplitGrowingKernelCompilersInAllModels ->
  RawDynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilersInAllModels.
Proof.
  intro hcompilers.
  exact
    (raw_dynamicTruthNativeGuardedDependencyOrderedAssumptionRetainingNormalizedCollisionResourceSplitGrowingKernelCompilersInAllModels_of_selected_fixed_sources
      (raw_dynamicTruthNativeGuardedDependencyOrderedSelectedFixedSourceSplitGrowingKernelCompilersInAllModels_of_fixed_source_compilers
        hcompilers)).
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroGuardedSelectedSourceCompilation.
