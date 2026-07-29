(** Assumption audit for arbitrary-context propositional composition. *)

From BoundedPAConsistency Require Import
  RawCodedPALocalProofComposition.

Import PABoundedRawCodedPALocalProofComposition.

Check raw_codedPALocalProofOf_botE.
Check raw_codedPALocalProofOf_impE.
Check raw_codedPALocalProofOf_impE3.

Print Assumptions raw_codedPALocalProofOf_botE.
Print Assumptions raw_codedPALocalProofOf_impE.
Print Assumptions raw_codedPALocalProofOf_impE3.
