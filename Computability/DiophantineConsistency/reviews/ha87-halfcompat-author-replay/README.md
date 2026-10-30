# Additive half-binomial compatibility repair

The three-module author run passed: `ArithmeticHalfBinomialCompat.lean`, its checks, and the minimally modified `ArithmeticAdaptivePopulation2011.lean`. The support module proves the two required facts in a distinct namespace while importing, rather than replacing, the historical `ArithmeticHalfBinomial` object. The failed focused run's 32 successful prefix source/object/log hashes and 1,136 historical objects were rechecked, as were current HA and adaptive source hashes. The exact snapshots, logs and author state are retained.

**Qualification:** the earlier 32-module prefix did not record direct imported-object or external-package hashes at compilation time. Its current hashes cannot retroactively authenticate those inputs, so that prefix remains an inherited, author-only provisional boundary; this packet does not prove a coherent 87-gate HA endpoint or full source-current provenance. The new focused rebuild recompiles that prefix with direct dependency guards. Foundation/Mathlib and their transitive package closure are also inherited.

```sh
python3 Computability/DiophantineConsistency/reviews/ha87-halfcompat-author-replay/replay.py \
  --expected Computability/DiophantineConsistency/reviews/ha87-halfcompat-author-replay/author/state.json
```
