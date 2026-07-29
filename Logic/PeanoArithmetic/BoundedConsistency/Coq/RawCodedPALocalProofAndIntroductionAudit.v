(** Exact-interface and assumption audit for local conjunction introduction. *)

From BoundedPAConsistency Require Import
  RawCodedPALocalProofAndIntroduction.

Import PABoundedRawCodedPALocalProofAndIntroduction.

Check raw_codedPALocalProofOf_andI.

Print Assumptions raw_codedPALocalProofOf_andI.
