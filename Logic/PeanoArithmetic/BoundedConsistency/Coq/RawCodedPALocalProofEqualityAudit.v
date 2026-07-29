(** Assumption audit for represented local equality elimination. *)

From BoundedPAConsistency Require Import RawCodedPALocalProofEquality.

Import PABoundedRawCodedPALocalProofEquality.

Check raw_codedPALocalProofOf_eqElim.
Check raw_codedPALocalProofOf_templateEqElim.
Print Assumptions raw_codedPALocalProofOf_eqElim.
Print Assumptions raw_codedPALocalProofOf_templateEqElim.
