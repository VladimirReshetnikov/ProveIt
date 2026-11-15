# Least bad witness elimination in the full source

For every PRA model with IΣ₁ arithmetic reduct and arbitrary internally valid property and model-valued free indices, assume contextual derivations of a direct trace of the negated property, the source domain, an element of the trace, and the ordinal base and step. The construction derives any requested formula in that context: it constructs least existence, opens a least bad point, derives its trace membership and domain, constructs a greatest predecessor, eliminates that greatest witness by the previous result, and eliminates the least witness. Fixed universal source theorems are selected by model-level choice.

This is a model-level full-source construction; the overall proof-code transformer is not yet accompanied by a fixed Σ₁ graph. The listed contextual derivations, including the initial trace member, remain explicit premises. It does not itself construct a bad member, close the full induction proof, or prove a native iPRA theorem or machine equivalence. The checker recompiles the source with selected byte-checked repository-built dependencies; other imports are prebuilt. Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-least-bad-eliminate.sh "$PWD" /dev/shm/pa194-least-bad-eliminate-repo
```

Choose a fresh output for another run.
