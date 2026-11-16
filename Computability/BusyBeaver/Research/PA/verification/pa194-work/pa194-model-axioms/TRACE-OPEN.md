# Opened separation trace and specialization

For arbitrary internally valid property code `p` and model index `s`, the opened witness of the specialized separation trace is proved equal to a universal formula with the explicitly constructed and internally scoped body `traceOpenBodyCode p s`. A fixed parameter-free Σ₁ graph defines that body throughout the covered arithmetic models. Given a contextual proof of the opened trace, `traceAtProof` specializes the universal at any model-valued index `x` and constructs an actual contextual proof of the exact substituted body; a second fixed Σ₁ graph computes exactly that proof code. Properties, indices, contexts and proofs may be nonstandard.

This is model-level for covered candidate PRA models with IΣ₁ arithmetic reducts and arbitrary internal Δ₁ source theories. The input trace proof remains a hypothesis. Identifying the substituted body with an independently expanded membership/property equivalence, the complete minimum-bad contradiction, the ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-separation-trace-open.sh "$PWD" /dev/shm/pa194-separation-trace-open-replay
```

The checker rebuilds the source against prebuilt dependencies, verifies direct hashes, checks eight axiom reports and rejects `sorryAx`; reports list only `propext`, `Classical.choice`, and `Quot.sound`.
