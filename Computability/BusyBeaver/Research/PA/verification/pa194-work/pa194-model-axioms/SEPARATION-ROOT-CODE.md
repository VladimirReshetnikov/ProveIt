# Full-source separation-root proof-code constructor

`separationRootCode p` builds the closed separation axiom proof and applies the model-length reopening iterator. `separationRootGraph_defined` supplies one fixed Σ₁ graph; `separationRootProof` and `separationRootProof_val` certify that the computed code proves the open root in the actual full-separation source theory, for every internally valid arity-one property code, including nonstandard codes. The assumptions are a model of PRA whose arithmetic reduct models IΣ₁. These are Lean model-level theorems, not a native iPRA derivation of the machine equivalence.

The checker compiles this file from source in a new output using hash-pinned, prebuilt dependencies, including the repository-replayed reopening iterator. Its dependency graph is not itself built from source by this checker. It checks input hashes before and after, six inherited hashes plus other dependencies, and rejects `sorryAx`; inspect `check.sh` for the exact pinned set.

Run from the repository root:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-separation-root-code.sh "$PWD" /dev/shm/pa194-separation-root-code-repo
```

The output path must not already exist. The successful audit output is `/dev/shm/pa194-separation-root-code-replay`, with log `/tmp/pa194-separation-root-code-audit.log`.
