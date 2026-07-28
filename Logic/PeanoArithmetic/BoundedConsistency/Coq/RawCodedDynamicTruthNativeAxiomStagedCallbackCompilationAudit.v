(** Audit for the public staged native axiom-soundness callback. *)

From BoundedPAConsistency Require Import
  RawCodedDynamicTruthNativeAxiomStagedCallbackCompilation.

Import PABoundedRawCodedDynamicTruthNativeAxiomStagedCallbackCompilation.

(** Graph selection retains one adequate orbit, its exact axiom transform,
    and the corresponding positive-graph output. *)
Check raw_dynamicTruthNativeAxiom_staged_graph_selection.

(** The public callback's only proof-producing premise is the committed
    linked staged kernel-implication compiler. *)
Check
  raw_dynamicTruthNativeStagedNextAxiomSoundnessCompiler_of_kernel_implication.

Print Assumptions raw_dynamicTruthNativeAxiom_staged_graph_selection.
Print Assumptions
  raw_dynamicTruthNativeStagedNextAxiomSoundnessCompiler_of_kernel_implication.
