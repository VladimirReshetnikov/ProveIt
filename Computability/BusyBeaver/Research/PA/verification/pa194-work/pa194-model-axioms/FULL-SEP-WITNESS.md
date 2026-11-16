# Separation witness in the full adjunctive source theory

In each covered candidate PRA model with IΣ₁ arithmetic reduct, `fullSepWitnessBranchProof` constructs an actual internal derivation in the classifier-defined adjunctive-plus-parameter-closed-separation theory. It consumes a derivation of a conclusion under the shifted context and opened separation witness, and produces a derivation of that conclusion in the original context. The property code, index, context and branch proof may be nonstandard. The theory's separation-root proof is supplied by the previously checked internal provability theorem.

The shifted branch derivation remains a hypothesis and is the substantive missing part. The root proof is selected using Lean choice from model-level provability; this result does not provide a uniform graph for that selection, establish the ordinal induction sequent, or prove native iPRA equivalence.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-full-sep-witness.sh "$PWD" /dev/shm/pa194-full-sep-witness-branch-replay-v2
```

The checker rebuilds the source against prebuilt dependency outputs, verifies direct input hashes, checks two axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
