(** Assumption audit for the raw additive identity laws. *)

From BoundedPAConsistency Require Import RawCodedAdditionLaws.

Import PABoundedRawCodedAdditionLaws.

Check raw_add_zero_right.
Check raw_add_zero_left.
Check raw_lt_zero_succ.

Print Assumptions raw_add_zero_right.
Print Assumptions raw_add_zero_left.
Print Assumptions raw_lt_zero_succ.
