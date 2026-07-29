(** Assumption audit for dependency-ordered growing conjunction. *)

From BoundedPAConsistency Require Import
  RawCodedPAGrowingTemplateConjunction.

Import PABoundedRawCodedPAGrowingTemplateConjunction.

Check raw_codedPALocalProofOf_and7I.
Check raw_codedPAGrowingTemplateLocalProofAt_and7_of_six_local.

Print Assumptions raw_codedPALocalProofOf_and7I.
Print Assumptions
  raw_codedPAGrowingTemplateLocalProofAt_and7_of_six_local.
