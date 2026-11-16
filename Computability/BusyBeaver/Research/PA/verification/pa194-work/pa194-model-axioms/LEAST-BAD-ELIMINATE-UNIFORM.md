# Uniform code for least-bad witness elimination

This strengthens the previously replayed full-source least-bad witness elimination. In every PRA model with IΣ₁ arithmetic reduct and any internal theory, six fixed universal source-theorem derivations are explicit singleton inputs. Given those and contextual derivations of the direct bad trace, source domain, a trace member, and ordinal base and step, the generic construction eliminates both least and greatest witnesses to derive any requested contextual formula. The exact constructed proof code is `leastBadEliminateCode`, and `leastBadEliminateGraph` is a fixed Σ₁ graph defining it for arbitrary model-valued inputs, including nonstandard property codes and indices. The original full-source wrapper remains and selects fixed universal proofs by model-level choice.

The trace member and other contextual derivations remain explicit premises. This does not construct a bad member, close the complete ordinal-induction proof, or prove the native iPRA theorem or machine equivalence. The checker recompiles this replacement source with selected byte-checked repository-built dependencies; other imports are prebuilt. Run from the repository root:

```
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-least-bad-eliminate-uniform.sh "$PWD" /dev/shm/pa194-least-bad-eliminate-uniform-repo
```

Choose a fresh output for another run.
