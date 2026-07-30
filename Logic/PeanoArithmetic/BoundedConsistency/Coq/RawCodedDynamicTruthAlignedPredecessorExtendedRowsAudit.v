(** Kernel-facing audit for aligned-predecessor shared row extraction. *)

From BoundedPAConsistency Require Import
  RawCodedDynamicTruthAlignedPredecessorExtendedRows.

Module PABoundedRawCodedDynamicTruthAlignedPredecessorExtendedRowsAudit.

Import PABoundedRawCodedDynamicTruthAlignedPredecessorExtendedRows.

Check raw_dynamicTruthAlignedPredecessor_extended_rows_exists.

(** This is the full extraction endpoint: current lower-level numeral and
    domains, common upper numeral, current-global selectors, wrapped local
    rows, and selector-polymorphic shared translation equations. *)
Print raw_dynamicTruthAlignedPredecessor_extended_rows_exists.
Print Assumptions
  raw_dynamicTruthAlignedPredecessor_extended_rows_exists.

End PABoundedRawCodedDynamicTruthAlignedPredecessorExtendedRowsAudit.
