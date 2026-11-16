# Opening the greatest-element witness

For any model-valued index x, the exact source formula greatestExists(x) is proved equal to an existential with the explicitly coded one-variable greatest-witness body. Opening that witness yields greatest(x+1,0), matching the actual shifted-context convention: the new witness is free variable 0 and the old x becomes x+1. Both equalities hold for nonstandard model indices.

`greatestWitnessElimProof` consumes a contextual proof of greatestExists(x) and a branch proof under the shifted conclusion/context with greatest(x+1,0) assumed, and returns a proof of the original conclusion. Its fixed parameter-free Σ₁ graph computes exactly the internal output proof code. This is model-level for covered candidate PRA models with IΣ₁ arithmetic reducts and arbitrary internal Δ₁ source theories. Both proofs remain hypotheses; constructing the predecessor branch, the complete minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-greatest-witness-open.sh "$PWD" /dev/shm/pa194-greatest-witness-open-repo
```

The checker rebuilds the source against prebuilt dependencies, verifies direct hashes, checks six axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
