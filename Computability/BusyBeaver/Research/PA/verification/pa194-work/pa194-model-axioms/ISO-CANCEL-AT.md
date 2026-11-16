# Successor cancellation at arbitrary internal indices

For any internal theory, sequent context and model-valued indices a, b, p and q, `isoCancelAtProof` takes a contextual proof of the fixed four-binder cancellation theorem and contextual proofs of domain(b), successor(p,a), successor(q,b), and orderIso(a,b), all expressed as substitutions into the literal arity-four templates. It derives orderIso(p,q). `isoCancelAtGraph_defined` gives a fixed Σ₁ graph for the proof-code operation, and `isoCancelAtProof_val` checks its exact value. The universal theorem is separately proved in the full source theory; its proof code is still an explicit input here.

This result applies in PRA models with IΣ₁ arithmetic reduct. It does not yet identify these substituted literal templates with every separately coded formula constructor or derive the actual translated PA induction/successor-injectivity axioms, native iPRA equivalence, or machine equivalence.

Run `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-iso-cancel-at.sh "$PWD" /dev/shm/pa194-iso-cancel-at-repo-NEW` at the repository root. The checker source-compiles the module against hash-pinned prebuilt dependencies including repository-replayed full-source cancellation and four-fold specialization. Successful output: `/dev/shm/pa194-iso-cancel-at-replay-v2`.
