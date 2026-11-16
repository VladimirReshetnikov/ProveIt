# One-step closure proof code

`closeOneCodeProof` generalizes an arbitrary singleton source proof through one universal closure, in every PRA model whose arithmetic reduct models IΣ₁. `closeOneCodeProof_val` identifies its exact computed proof code, and `closeOneGraph_defined` defines that function with one fixed Σ₁ graph. The proof uses explicit contextual universal introduction and is uniform in the internal formula code and theory; the Lean theorem is model-level, not a native iPRA proof.

Run `bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-close-one-code.sh "$PWD" /dev/shm/pa194-close-one-code-repo` at the repository root; the output directory must not exist. This compiles the source with hash-pinned prebuilt dependencies and checks the printed axiom reports. The completed replay is `/dev/shm/pa194-close-one-code-replay`.
