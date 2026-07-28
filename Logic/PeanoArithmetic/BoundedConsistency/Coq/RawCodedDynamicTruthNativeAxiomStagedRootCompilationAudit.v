(** Kernel-facing audit for the dependency-aware native axiom stage. *)

From BoundedPAConsistency Require Import
  RawCodedDynamicTruthNativeAxiomStagedRootCompilation.

Import PABoundedRawCodedDynamicTruthNativeAxiomStagedRootCompilation.

(** The cumulative antecedent and prerequisite package expose all six
    current fields followed by local, cross-level, shift, and substitution. *)
Check rawDynamicTruthNativeAxiomStagedAntecedentCode.
Check RawDynamicTruthNativeAxiomStagedPrerequisitesAt.
Check rawDynamicTruthNativeAxiomStagedAntecedentRoot.
Check raw_dynamicTruthNativeAxiomStagedAntecedentRoot_of_prerequisites.

(** The only residual is a linked, shift-indexed implication whose consequent
    is the existing curried witness-body kernel. *)
Check RawDynamicTruthNativeAxiomStagedKernelImplicationRootOn.
Check
  RawDynamicTruthNativeAxiomLinkedStagedKernelImplicationRootCompiler.
Check
  raw_dynamicTruthNativeAxiomWitnessBodyKernelRoot_of_staged_implication.

(** All witness leaves and logical eliminations are discharged before the
    carried All/Imp closure and exact-transform ordinary-proof endpoint. *)
Check raw_dynamicTruthNativeAxiomLocalRootOn_of_staged_kernel_implication.
Check RawDynamicTruthNativeAxiomFieldLocalRootOn.
Check raw_dynamicTruthNativeAxiomFieldLocalRootOn_of_local_root.
Check raw_codedPAProofOf_dynamicTruthNativeAxiomField_of_carried_root.
Check
  raw_dynamicTruthNativeAxiomTransformSelectedProof_of_staged_kernel_implication.
Check
  raw_dynamicTruthNativeAxiomPositiveProofAt_of_staged_kernel_implication.

Print Assumptions
  raw_dynamicTruthNativeAxiomStagedAntecedentRoot_of_prerequisites.
Print Assumptions
  raw_dynamicTruthNativeAxiomWitnessBodyKernelRoot_of_staged_implication.
Print Assumptions
  raw_dynamicTruthNativeAxiomLocalRootOn_of_staged_kernel_implication.
Print Assumptions
  raw_dynamicTruthNativeAxiomFieldLocalRootOn_of_local_root.
Print Assumptions
  raw_codedPAProofOf_dynamicTruthNativeAxiomField_of_carried_root.
Print Assumptions
  raw_dynamicTruthNativeAxiomTransformSelectedProof_of_staged_kernel_implication.
Print Assumptions
  raw_dynamicTruthNativeAxiomPositiveProofAt_of_staged_kernel_implication.
