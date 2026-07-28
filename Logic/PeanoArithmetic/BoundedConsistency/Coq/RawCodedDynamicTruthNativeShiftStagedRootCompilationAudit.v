(** Kernel-facing audit for the dependency-aware native shift stage. *)

From BoundedPAConsistency Require Import
  RawCodedDynamicTruthNativeShiftStagedRootCompilation.

Import
  PABoundedRawCodedDynamicTruthNativeShiftStagedRootCompilation.

(** The staged antecedent is Lean's exact [crossContext]: the preceding
    six-field master and next local field, paired with next cross-level. *)
Check rawDynamicTruthNativeShiftStagedAntecedentCode.
Check RawDynamicTruthNativeShiftStagedPrerequisitesAt.

(** The only mathematical residual is one trace-linked implication to the
    synchronized body, over the same visible witnessed context. *)
Check RawDynamicTruthNativeShiftBodyRootOn.
Check RawDynamicTruthNativeShiftStagedBodyImplicationRootOn.
Check RawDynamicTruthNativeShiftLinkedStagedBodyImplicationRootCompiler.
Check raw_dynamicTruthNativeShiftStagedBodyRoot_of_implication.

(** Structural decomposition recovers the old four-root/four-leaf boundary
    without altering the selected carrier formulas or the base context. *)
Check raw_dynamicTruthNativeShiftAntecedent_atomically_adequate.
Check raw_dynamicTruthNativeShiftLocalRootsOn_of_body_root.
Check raw_dynamicTruthNativeShiftStagedLocalRoots_of_body_implication.
Check raw_dynamicTruthNativeShiftDirectionalLeaf_of_local_root.
Check raw_dynamicTruthNativeShiftDirectionalLeavesOn_of_local_roots.
Check
  raw_dynamicTruthNativeShiftStagedLocalRoots_via_directional_leaves.

(** The eight universal introductions retain the witnessed PA context, and
    the graph-facing theorem proves the exact transform-selected target. *)
Check rawDynamicTruthNativeShiftStagedProofCertificate.
Check raw_codedPAProofOf_dynamicTruthNativeShiftField_of_body_root_on.
Check raw_dynamicTruthNativeShiftStagedFieldProof_of_body_implication.
Check raw_dynamicTruthNativeShiftStagedTransformProof_of_body_implication.

Print Assumptions raw_dynamicTruthNativeShiftStagedBodyRoot_of_implication.
Print Assumptions raw_dynamicTruthNativeShiftLocalRootsOn_of_body_root.
Print Assumptions
  raw_dynamicTruthNativeShiftStagedLocalRoots_via_directional_leaves.
Print Assumptions
  raw_codedPAProofOf_dynamicTruthNativeShiftField_of_body_root_on.
Print Assumptions
  raw_dynamicTruthNativeShiftStagedTransformProof_of_body_implication.
