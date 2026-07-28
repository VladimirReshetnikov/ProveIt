(** Kernel-facing audit for dependency-aware native cross-level guards. *)

From BoundedPAConsistency Require Import
  RawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.

Import
  PABoundedRawCodedDynamicTruthNativeCrossLevelGuardRootCompilation.

(** One coherence-body root is sufficient for both polarity guards, over a
    base context which remains syntactically visible. *)
Check RawDynamicTruthNativeCrossLevelBodyRootOn.
Check raw_dynamicTruthNativeCrossLevelGuardRootsOn_of_body_root.
Check RawDynamicTruthNativeCrossLevelLinkedBodyRootCompilerOn.
Check
  raw_dynamicTruthNativeCrossLevelLinkedGuardRootCompilerOn_of_body.
Check raw_dynamicTruthNativeCrossLevelLinkedGuardRootCompiler_of_body.

(** The production boundary has the dependency order used by the Lean
    staged compiler: the preceding six-field master and the next local field
    share one witnessed context before cross-level coherence is applied. *)
Check rawDynamicTruthNativeCrossLevelStagedAntecedentCode.
Check RawDynamicTruthNativeCrossLevelStagedPrerequisitesAt.
Check RawDynamicTruthNativeCrossLevelStagedBodyImplicationRootOn.
Check
  RawDynamicTruthNativeCrossLevelLinkedStagedBodyImplicationRootCompiler.
Check
  raw_dynamicTruthNativeCrossLevelStagedGuardRoots_of_body_implication.

Print Assumptions
  raw_dynamicTruthNativeCrossLevelGuardRootsOn_of_body_root.
Print Assumptions
  raw_dynamicTruthNativeCrossLevelLinkedGuardRootCompilerOn_of_body.
Print Assumptions
  raw_dynamicTruthNativeCrossLevelLinkedGuardRootCompiler_of_body.
Print Assumptions
  raw_dynamicTruthNativeCrossLevelStagedGuardRoots_of_body_implication.
