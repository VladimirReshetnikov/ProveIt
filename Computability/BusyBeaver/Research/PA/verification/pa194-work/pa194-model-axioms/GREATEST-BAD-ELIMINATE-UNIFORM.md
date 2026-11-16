# Uniform proof code for greatest-witness elimination

This strengthens the previously replayed full-source greatest-witness elimination. In every PRA model with IΣ₁ arithmetic reduct and any internal theory, four fixed universal source-theorem derivations are now explicit singleton inputs. Given those and the listed trace, domain, membership, leastness, induction-step and greatest-existence derivations, the generic construction derives any requested contextual formula after eliminating the greatest witness. `greatestBadEliminateCode` is proved exactly equal to the constructed proof value, and `greatestBadEliminateGraph` is a fixed Σ₁ graph defining it for all inputs, including nonstandard codes and indices. The original full-source wrapper remains and supplies the four fixed proofs by model-level choice.

This does not supply the listed inputs, eliminate the least witness, complete the ordinal-induction supplier, or prove the native iPRA theorem or machine equivalence. The checker recompiles this replacement source using selected byte-checked repository-built modules; other imports are prebuilt. Run from the repository root:

```
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-greatest-bad-eliminate-uniform.sh "$PWD" /dev/shm/pa194-greatest-bad-eliminate-uniform-repo
```

Choose a fresh output for another run.
