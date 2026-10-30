# Bounded comparison replay after fixed-goal merge

This packet rebuilds the bounded-only IΣ₀-to-candidate-PRA comparison; it does not establish Σ₁ conservation. It authenticates the post-merge candidate provider and direct `ParsonsRule` source/object. Foundation, Mathlib and transitive Parsons artifacts are inherited.

Manifest SHA-256: `b2d7718a77399237cc723b6bafb494eecc4d62c05561af51b16907ce410c5bf4`. The author run and the independent replay at `/tmp/parsons-bounded-post-fixed-independent-5pukvc5y` both passed. The latter used root's separately accepted 31-module provider `/tmp/pra-after-fixed-merge-independent-vpyarv0n/lib`. The `author` and `independent` directories retain state, source snapshots and full logs.

```sh
python Computability/DiophantineConsistency/reviews/parsons-bounded-post-fixed-replay/replay.py --parent /tmp/pra-after-fixed-merge-independent-vpyarv0n/lib
```
