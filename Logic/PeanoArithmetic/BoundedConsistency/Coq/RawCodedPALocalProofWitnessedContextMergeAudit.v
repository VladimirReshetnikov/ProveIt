(**
  Kernel-facing audit for represented witnessed-context prefix merge.

  The unconditional checks expose the complete nonstandard reverse fold and
  its right-hand proof transport.  The final checks keep the sole unresolved
  direction visible by name: witnessed-context inclusion weakening.  Thus the
  six-field reduction cannot be mistaken for an assumption-free merge.
*)

From BoundedPAConsistency Require Import
  RawCodedPALocalProofWitnessedContextMerge.

Module PABoundedRawCodedPALocalProofWitnessedContextMergeAudit.

Import PABoundedRawCodedPALocalProofWitnessedContextMerge.

(** Definable relations and their satisfaction bridges. *)
Check RawContextListIncluded.
Check contextListIncludedTermAt.
Check raw_sat_contextListIncludedTermAt_iff.

Check RawCodedPALocalProofContextTransport.
Check codedPALocalProofContextTransportTermAt.
Check raw_sat_codedPALocalProofContextTransportTermAt_iff.

(** Honest list-domain and inclusion support. *)
Check raw_codedPAAxiomWitnessContext_witnessList_realizable.
Check raw_codedPAAxiomWitnessContext_context_realizable.
Check raw_contextListIncluded_refl.
Check raw_contextListIncluded_zero.
Check raw_contextListIncluded_cons.
Check raw_contextListIncluded_cons_target.

(** Carrier-valued reverse construction. *)
Check RawCodedPAWitnessedPrefixMergeState.
Check codedPAWitnessedPrefixMergeStateTermAt.
Check raw_sat_codedPAWitnessedPrefixMergeStateTermAt_iff.
Check raw_codedPAWitnessedPrefixMergeState_zero.
Check raw_codedPAWitnessedPrefixMergeState_succ.
Check raw_codedPAWitnessedPrefixMergeState_all.

(** Unconditional public endpoints. *)
Check raw_codedPAAxiomWitnessContext_prefixMerge.
Check raw_codedPALocalProof_witnessedContext_prefixMerge_right.

(** Exact remaining seam and reductions conditional only on that seam. *)
Check RawCodedPALocalProofWitnessedContextInclusionWeakening.
Check raw_codedPALocalProof_twoWitnessedContexts_commonContext_of_weakening.
Check raw_codedPALocalProof_addWitnessedContext_of_weakening.
Check raw_codedPAProofOf_witnessedLocal_fields.
Check
  raw_sixFieldMasterOrdinaryProofsCommonContextLift_of_witnessedContextInclusionWeakening.

(** Direct assumption reports. *)
Print Assumptions raw_sat_contextListIncludedTermAt_iff.
Print Assumptions raw_sat_codedPALocalProofContextTransportTermAt_iff.
Print Assumptions raw_codedPAWitnessedPrefixMergeState_zero.
Print Assumptions raw_codedPAWitnessedPrefixMergeState_succ.
Print Assumptions raw_codedPAWitnessedPrefixMergeState_all.
Print Assumptions raw_codedPAAxiomWitnessContext_prefixMerge.
Print Assumptions
  raw_codedPALocalProof_witnessedContext_prefixMerge_right.
Print Assumptions
  raw_codedPALocalProof_twoWitnessedContexts_commonContext_of_weakening.
Print Assumptions raw_codedPALocalProof_addWitnessedContext_of_weakening.
Print Assumptions
  raw_sixFieldMasterOrdinaryProofsCommonContextLift_of_witnessedContextInclusionWeakening.

End PABoundedRawCodedPALocalProofWitnessedContextMergeAudit.
