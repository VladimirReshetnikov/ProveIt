(** Audit for the public sixth-stage callback adapter. *)

From BoundedPAConsistency Require Import
  RawCodedDynamicTruthNativeFinalStagedCallbackCompilation.

Import PABoundedRawCodedDynamicTruthNativeFinalStagedCallbackCompilation.

(** The conclusion is the exact public dependency-ordered final callback.
    The historical source-linked adapter remains audited, together with the
    smaller bridge interface whose target-refutation root is now produced
    internally. *)
Check raw_dynamicTruthNativeStagedNextFinalCompiler_of_trace_proof.
Check
  raw_dynamicTruthNativeStagedNextFinalCompiler_of_source_linked_implication.
Check
  raw_dynamicTruthNativeStagedNextFinalCompiler_of_universal_soundness_bridge.
Check
  raw_dynamicTruthNativeStagedNextFinalCompiler_of_growing_direct_bridge.
Check
  raw_dynamicTruthNativeStagedNextFinalCompiler_of_growing_direct_bridge_family.

Print Assumptions
  raw_dynamicTruthNativeStagedNextFinalCompiler_of_trace_proof.
Print Assumptions
  raw_dynamicTruthNativeStagedNextFinalCompiler_of_source_linked_implication.
Print Assumptions
  raw_dynamicTruthNativeStagedNextFinalCompiler_of_universal_soundness_bridge.
Print Assumptions
  raw_dynamicTruthNativeStagedNextFinalCompiler_of_growing_direct_bridge.
Print Assumptions
  raw_dynamicTruthNativeStagedNextFinalCompiler_of_growing_direct_bridge_family.
