(**
  Specialize the exact six-field endpoint to the five native positive graphs.

  The generic spliced master files deliberately quantify over five future
  positive graphs.  Four of those graphs are now committed and the fifth is
  the native PA-axiom-soundness graph.  This module fixes those parameters
  once, records the unconditional zero callback, and exposes the precise
  common-context successor compiler that still has to be constructed.

  In particular, the final theorem below is not an unconditional proof of the
  uniform sentence.  Its sole premise is the exact all-model successor
  callback consumed by the represented PA induction; no truth assumption or
  arbitrary proof transplant is hidden in the specialization.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CompactPAUniformProvability
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeCrossLevelPositiveGraph
  RawCodedDynamicTruthNativeShiftPositiveGraph
  RawCodedDynamicTruthNativeSubstitutionPositiveGraph
  RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph
  RawCodedDynamicTruthMasterSplicedBasePackage
  RawCodedDynamicTruthMasterSplicedSuccessorBridge
  RawCodedTruthCertificateMasterInduction
  RawCodedTruthCertificateConcreteEndpoint.

Module PABoundedRawCodedDynamicTruthNativeMasterEndpoint.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeCrossLevelPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeShiftPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeSubstitutionPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.
Import PABoundedRawCodedDynamicTruthMasterSplicedBasePackage.
Import PABoundedRawCodedDynamicTruthMasterSplicedSuccessorBridge.
Import PABoundedRawCodedTruthCertificateMasterInduction.
Import PABoundedRawCodedTruthCertificateConcreteEndpoint.

(** Name each actual field graph after the zero/positive splice.  These are
    the five graph parameters passed to the concrete six-field assembler. *)
Definition dynamicTruthNativeSplicedLocalFieldGraph : formula :=
  dynamicTruthSplicedLocalFieldGraph dynamicTruthNativeLocalPositiveGraph.

Definition dynamicTruthNativeSplicedCrossLevelFieldGraph : formula :=
  dynamicTruthSplicedCrossLevelFieldGraph
    dynamicTruthNativeCrossLevelPositiveGraph.

Definition dynamicTruthNativeSplicedShiftFieldGraph : formula :=
  dynamicTruthSplicedShiftFieldGraph dynamicTruthNativeShiftPositiveGraph.

Definition dynamicTruthNativeSplicedSubstitutionFieldGraph : formula :=
  dynamicTruthSplicedSubstitutionFieldGraph
    dynamicTruthNativeSubstitutionPositiveGraph.

Definition dynamicTruthNativeSplicedAxiomSoundnessFieldGraph : formula :=
  dynamicTruthSplicedAxiomSoundnessFieldGraph
    dynamicTruthNativeAxiomSoundnessPositiveGraph.

(** The exact native master relation: the first five coordinates are the
    spliced fields above and the sixth coordinate is forced by the generic
    assembler to be compact bounded consistency at the same index. *)
Definition dynamicTruthNativeSplicedMasterGraph : formula :=
  dynamicTruthSplicedMasterGraph
    dynamicTruthNativeLocalPositiveGraph
    dynamicTruthNativeCrossLevelPositiveGraph
    dynamicTruthNativeShiftPositiveGraph
    dynamicTruthNativeSubstitutionPositiveGraph
    dynamicTruthNativeAxiomSoundnessPositiveGraph.

(** Zero is already completely constructive: every field reduces to its
    checked standard base formula and the compact final coordinate has its
    independently proved level-zero certificate. *)
Theorem raw_dynamicTruthNativeSplicedMasterPackageBase : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawSixFieldMasterPackageBase M dynamicTruthNativeSplicedMasterGraph.
Proof.
  intros M hPA.
  unfold dynamicTruthNativeSplicedMasterGraph.
  exact (raw_dynamicTruthSplicedMasterPackageBase M hPA
    dynamicTruthNativeLocalPositiveGraph
    dynamicTruthNativeCrossLevelPositiveGraph
    dynamicTruthNativeShiftPositiveGraph
    dynamicTruthNativeSubstitutionPositiveGraph
    dynamicTruthNativeAxiomSoundnessPositiveGraph).
Qed.

(** The one positive-step obligation after all graph parameters are fixed.
    It receives the six current roots in one witnessed PA context and must
    return the six next roots in one (possibly extended) witnessed context. *)
Definition RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor
    (M : RawPAModel) : Prop :=
  RawDynamicTruthSplicedMasterRawPositiveComponentSuccessor M
    dynamicTruthNativeLocalPositiveGraph
    dynamicTruthNativeCrossLevelPositiveGraph
    dynamicTruthNativeShiftPositiveGraph
    dynamicTruthNativeSubstitutionPositiveGraph
    dynamicTruthNativeAxiomSoundnessPositiveGraph.

Arguments RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor M
  : clear implicits.

Definition
    RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessorInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor M.

(** The specialized compiler produces the public master-successor callback
    without re-decoding a proof or changing any selected field code. *)
Theorem raw_dynamicTruthNativeSplicedMasterPackageSuccessor_of_compiler :
  forall (M : RawPAModel), RawPASatisfies M ->
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessor M ->
  RawSixFieldMasterPackageSuccessor M dynamicTruthNativeSplicedMasterGraph.
Proof.
  intros M hPA hcompiler.
  unfold dynamicTruthNativeSplicedMasterGraph.
  exact
    (raw_dynamicTruthSplicedMasterPackageSuccessor_of_positive_components
      M hPA
      dynamicTruthNativeLocalPositiveGraph
      dynamicTruthNativeCrossLevelPositiveGraph
      dynamicTruthNativeShiftPositiveGraph
      dynamicTruthNativeSubstitutionPositiveGraph
      dynamicTruthNativeAxiomSoundnessPositiveGraph hcompiler).
Qed.

(** Package base and successor in the exact component interface consumed by
    the already completed master graph decomposition and internal induction. *)
Theorem raw_dynamicTruthNativeSplicedMasterComponents_of_compiler :
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessorInAllModels ->
  RawConcreteSixFieldMasterComponentsInAllModels
    dynamicTruthNativeSplicedLocalFieldGraph
    dynamicTruthNativeSplicedCrossLevelFieldGraph
    dynamicTruthNativeSplicedShiftFieldGraph
    dynamicTruthNativeSplicedSubstitutionFieldGraph
    dynamicTruthNativeSplicedAxiomSoundnessFieldGraph.
Proof.
  intros hcompiler M hPA.
  split.
  - unfold dynamicTruthNativeSplicedLocalFieldGraph,
      dynamicTruthNativeSplicedCrossLevelFieldGraph,
      dynamicTruthNativeSplicedShiftFieldGraph,
      dynamicTruthNativeSplicedSubstitutionFieldGraph,
      dynamicTruthNativeSplicedAxiomSoundnessFieldGraph.
    exact (raw_dynamicTruthMasterSplicedBaseComponentPackage
      dynamicTruthNativeLocalPositiveGraph
      dynamicTruthNativeCrossLevelPositiveGraph
      dynamicTruthNativeShiftPositiveGraph
      dynamicTruthNativeSubstitutionPositiveGraph
      dynamicTruthNativeAxiomSoundnessPositiveGraph M hPA).
  - left.
    unfold dynamicTruthNativeSplicedLocalFieldGraph,
      dynamicTruthNativeSplicedCrossLevelFieldGraph,
      dynamicTruthNativeSplicedShiftFieldGraph,
      dynamicTruthNativeSplicedSubstitutionFieldGraph,
      dynamicTruthNativeSplicedAxiomSoundnessFieldGraph.
    exact
      (raw_dynamicTruthSplicedMasterRawComponentSuccessor_of_positive_components
        M hPA
        dynamicTruthNativeLocalPositiveGraph
        dynamicTruthNativeCrossLevelPositiveGraph
        dynamicTruthNativeShiftPositiveGraph
        dynamicTruthNativeSubstitutionPositiveGraph
        dynamicTruthNativeAxiomSoundnessPositiveGraph
        (hcompiler M hPA)).
Qed.

(** Exact conditional headline.  Once the specialized successor compiler is
    filled, this theorem yields the literal requested Coq sentence with no
    further graph, induction, projection, or completeness premise. *)
Theorem
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_native_compiler
    :
  RawDynamicTruthNativeSplicedMasterPositiveComponentSuccessorInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hcompiler.
  exact
    (PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_components
      dynamicTruthNativeSplicedLocalFieldGraph
      dynamicTruthNativeSplicedCrossLevelFieldGraph
      dynamicTruthNativeSplicedShiftFieldGraph
      dynamicTruthNativeSplicedSubstitutionFieldGraph
      dynamicTruthNativeSplicedAxiomSoundnessFieldGraph
      (raw_dynamicTruthNativeSplicedMasterComponents_of_compiler hcompiler)).
Qed.

End PABoundedRawCodedDynamicTruthNativeMasterEndpoint.
