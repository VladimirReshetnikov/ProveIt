# A bad-trace member is nonzero by downward closure

For every internally valid property `p` and model-valued indices `s` and `x`, the constructor takes contextual proofs of the opened separation trace of `¬p`, `x ∈ witness`, the universal member-domain theorem, domain(shifted-s), and the ordinal base statement for shifted `p`. It derives `¬zero(x)` under the same context: trace membership supplies `x ∈ shifted-s` and the bad property instance, and the universal theorem supplies domain(x). A fixed parameter-free Σ₁ graph computes exactly the output internal proof code, including for nonstandard property, indices, context and proof codes.

`traceNonzeroFromDomainLogic` supplies the universal member-domain theorem internally by model-level choice, leaving the trace, witness-membership, source-domain and base proofs as the four hypotheses. No uniform graph is claimed for the choice of that theorem proof. These results are model-level for covered candidate PRA models with IΣ₁ arithmetic reducts and arbitrary internal Δ₁ source theories; the full minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-trace-nonzero-domain.sh "$PWD" /dev/shm/pa194-trace-nonzero-from-domain-replay
```

The checker rebuilds the source against prebuilt dependencies, verifies direct hashes, checks four axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
