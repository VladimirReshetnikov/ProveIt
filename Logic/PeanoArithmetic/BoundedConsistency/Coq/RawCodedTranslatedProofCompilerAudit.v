(**
  Assumption audit for the translated raw-proof compiler.

  The checks expose the public translation contract and all three compiler
  layers: structural contexts, exact endpoints, and proof-wide rule
  coverage.  [Print Assumptions] is intentionally run on the final local
  proof theorem as well as its two logical components, so an accidental
  axiom in either branch remains visible in automated build logs.
*)

From BoundedPAConsistency Require Import
  RawCodedTranslatedProofCompiler.

Import PABoundedRawCodedTranslatedProofCompiler.

Check RawCodedProofTranslation.
Check rawTranslatedTerm.
Check rawTranslatedFormula.
Check rawTranslatedFormula_shift.
Check rawTranslatedFormula_substitution.

Check rawTranslatedContextCode.
Check raw_translatedContext_realizable.
Check raw_translatedContext_member.
Check raw_translatedContext_shift.

Check rawTranslatedProofCode.
Check raw_translatedProof_endpoint.
Check raw_translatedProof_ruleCoverage.
Check raw_translatedProof_localProof.

Print Assumptions raw_translatedContext_realizable.
Print Assumptions raw_translatedContext_member.
Print Assumptions raw_translatedContext_shift.
Print Assumptions raw_translatedProof_endpoint.
Print Assumptions raw_translatedProof_ruleCoverage.
Print Assumptions raw_translatedProof_localProof.
