(** Assumption audit for adequacy of the paired dynamic-truth base. *)

From BoundedPAConsistency Require Import
  RawCodedDynamicTruthPairedBaseAdequacy.

Import PABoundedRawCodedDynamicTruthPairedBaseAdequacy.

Check dynamicTruthPairedBaseFormulaCodeGraph_adequate_total.

Print Assumptions dynamicTruthPairedBaseFormulaCodeGraph_adequate_total.
