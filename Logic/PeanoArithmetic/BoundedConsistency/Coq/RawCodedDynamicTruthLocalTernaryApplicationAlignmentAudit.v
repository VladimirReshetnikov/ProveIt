(** Assumption audit for native/generic ternary application alignment. *)

From BoundedPAConsistency Require Import
  RawCodedDynamicTruthLocalTernaryApplicationAlignment.

Import PABoundedRawCodedDynamicTruthLocalTernaryApplicationAlignment.

Check raw_dynamicTruthLocalTernaryApplication_ternary_iff.

Print Assumptions raw_dynamicTruthLocalTernaryApplication_ternary_iff.
