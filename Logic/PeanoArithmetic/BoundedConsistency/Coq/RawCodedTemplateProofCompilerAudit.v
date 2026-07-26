From BoundedPAConsistency Require Import RawCodedTemplateProofCompiler.

Import PABoundedRawCodedTemplateProofCompiler.

(** The source translation contract exposes precisely the constructor and
    operation obligations used by the proof compiler. *)
Check RawCodedTemplateTranslation.
Check rawTemplateContextCode.
Check rawTemplateProofCode.

(** Structural context compilation. *)
Check raw_templateContext_realizable.
Check raw_templateContext_member.
Check raw_templateContext_shift.

(** Exact endpoint, proof-wide coverage, and the final local proof package. *)
Check raw_templateProof_endpoint.
Check raw_templateProof_endpoint_at.
Check raw_templateProof_ruleCoverage.
Check raw_templateProof_localProof.

Print Assumptions raw_templateContext_realizable.
Print Assumptions raw_templateContext_member.
Print Assumptions raw_templateContext_shift.
Print Assumptions raw_templateProof_endpoint.
Print Assumptions raw_templateProof_ruleCoverage.
Print Assumptions raw_templateProof_localProof.
