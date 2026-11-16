# Specializing separation to the existential trace

For every valid internal arity-one property code `p` and internal index `s`, `traceExistsCode p s` is exactly the substitution of the free variable `s` into the body of the actual separation root `sepRoot p`; the result has the existential witness for the corresponding separation trace. `traceFromSepProof` takes an actual internal contextual derivation of that separation root and constructs a derivation of this exact instance. The fixed parameter-free Σ₁ graph is proved to compute exactly the constructed proof code. The property, index, context and input proof may be nonstandard.

The construction is model-level for covered candidate PRA models with IΣ₁ arithmetic reducts and any internal Δ₁ source theory. The source proof of separation remains an explicit premise. This result does not yet prove an independent expanded trace-template identity or the ordinal induction sequent, and does not establish native iPRA equivalence.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-separation-trace-at.sh "$PWD" /dev/shm/pa194-separation-trace-at-code-replay
```

The checker rebuilds the source, verifies its and direct dependency hashes, checks three axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
