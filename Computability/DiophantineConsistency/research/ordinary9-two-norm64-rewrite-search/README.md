# Bounded exact-ring rewrite screen of the 9/64 graph

This source-only seeded beam search tests local reassociation, signed three-term rearrangement, common-factor extraction and distribution on the pinned 9-variable, 64-operation two-norm graph. It retains at most 100 states at each of eight depths and permits at most 65 operations during the search. A common-factor positive control verifies that the search can find a basic three-to-two gate reduction. Its best found graph has 64 live operations.

The search is beam-pruned and depth/size limited. It is not exhaustive, a minimality bound, a compact-coefficient-specialized test, a zero-set or witness-map search, or a Lean proof. In particular, a separately derived [10-variable/61-operation divisibility graph](../ordinary10-two-norm-divisible61/README.md) is outside these exact-polynomial rewrite rules; its two-way standard-integer map and its missing original-parent bridge have their own scope.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary9-two-norm64-rewrite-search/search.py | cmp - research/ordinary9-two-norm64-rewrite-search/receipt.json
```
