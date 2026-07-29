(** Audit of native-trace reconstruction of the local-exclusive template. *)

From BoundedPAConsistency Require Import
  RawCodedDynamicTruthLocalExclusiveTemplateTraceCompilation.

Import
  PABoundedRawCodedDynamicTruthLocalExclusiveTemplateTraceCompilation.

Check
  raw_coqDynamicTruthLocalExclusiveTemplateIdentification_of_native_trace.

Print Assumptions
  raw_coqDynamicTruthLocalExclusiveTemplateIdentification_of_native_trace.
