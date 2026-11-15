# Arbitrary-index trace proof shift

For any arithmetic PRA model satisfying IΣ₁, internal theory, internally coded property and source and witness indices, the opened trace derivation can be cast to the direct syntax with unchanged code. The contextual proof shifter then constructs a derivation of the shifted direct trace, with fixed Σ₁ graph for its exact output code, provided the original derivation is given. This applies to nonstandard syntax and indices.

This neither supplies the original separation trace nor proves the induction sequent, iPRA theorem or machine equivalence. The replay recompiles this source with repository-rebuilt, byte-checked direct-syntax and selected other dependencies; remaining imports are also prebuilt. Run after the direct-syntax replay, from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-trace-direct-shift.sh "$PWD" /dev/shm/pa194-trace-direct-shift-repo-v2
```
Use a fresh output directory for another run.
