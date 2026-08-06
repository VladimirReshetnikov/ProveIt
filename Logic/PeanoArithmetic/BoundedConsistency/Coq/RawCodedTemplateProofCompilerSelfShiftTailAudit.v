(**
  Kernel-facing audit for the template compiler over a self-shifting tail.

  The public compiler deliberately exposes exactly two semantic properties
  of its carrier-coded tail: list realizability and self-shift.  The final
  specialization discharges both properties for a witnessed PA-axiom
  context, without decoding the context or weakening a proof.
*)

From BoundedPAConsistency Require Import
  RawCodedTemplateProofCompilerSelfShiftTail.

Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.

(** Tail-parameterized context and proof-code folds. *)
Check rawTemplateContextCodeOnTail.
Check rawTemplateProofCodeOnTail.

(** Structural facts used by the quantifier rules. *)
Check raw_templateContextOnTail_realizable.
Check raw_templateContextOnTail_member.
Check raw_templateContextOnTail_shift.

(** Exact endpoint, all-rule coverage, and the public local-proof package. *)
Check raw_templateProofOnTail_endpoint.
Check raw_templateProofOnTail_endpoint_at.
Check raw_templateProofOnTail_ruleCoverage.
Check raw_templateProofOnTail_localProof.

(** Specialization to any carrier-coded PA-axiom witness context. *)
Check raw_templateProofOnPAAxiomContext_localProof.
Check raw_templateAssumptionOnPAAxiomContext_localProof.

Print Assumptions raw_templateContextOnTail_realizable.
Print Assumptions raw_templateContextOnTail_member.
Print Assumptions raw_templateContextOnTail_shift.
Print Assumptions raw_templateProofOnTail_endpoint.
Print Assumptions raw_templateProofOnTail_ruleCoverage.
Print Assumptions raw_templateProofOnTail_localProof.
Print Assumptions raw_templateProofOnPAAxiomContext_localProof.
Print Assumptions raw_templateAssumptionOnPAAxiomContext_localProof.
