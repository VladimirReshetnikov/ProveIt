(** Audit for the public sixth-stage callback adapter. *)

From BoundedPAConsistency Require Import
  RawCodedDynamicTruthNativeFinalStagedCallbackCompilation.

Import PABoundedRawCodedDynamicTruthNativeFinalStagedCallbackCompilation.

(** The conclusion is the exact public dependency-ordered final callback;
    its only proof-producing premise is the previously isolated source-linked
    dynamic-soundness implication compiler. *)
Check
  raw_dynamicTruthNativeStagedNextFinalCompiler_of_source_linked_implication.

Print Assumptions
  raw_dynamicTruthNativeStagedNextFinalCompiler_of_source_linked_implication.
