(** Assumption audit for unary growing-template rebasing. *)

From BoundedPAConsistency Require Import RawCodedPAGrowingTemplateRebase.

Import PABoundedRawCodedPAGrowingTemplateRebase.

Check raw_codedPALocalProof_templateSuffix.
Check raw_codedPAGrowingTemplateLocalProofAt_rebase.
Print Assumptions raw_codedPALocalProof_templateSuffix.
Print Assumptions raw_codedPAGrowingTemplateLocalProofAt_rebase.
