(** Audit for the exact native/generic axiom-application alignment. *)

From BoundedPAConsistency Require Import
  RawCodedDynamicTruthNativeAxiomApplicationTernaryAlignment.

Import
  PABoundedRawCodedDynamicTruthNativeAxiomApplicationTernaryAlignment.

Check raw_dynamicTruthNativeAxiomApplication_ternary_iff.

Print Assumptions raw_dynamicTruthNativeAxiomApplication_ternary_iff.
