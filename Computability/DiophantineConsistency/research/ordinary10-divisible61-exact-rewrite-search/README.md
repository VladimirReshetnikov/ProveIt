# Bounded exact-ring rewrite screen of the 10/61 graph

This source-only seeded beam search tests local reassociation, signed three-term rearrangement, common-factor extraction and distribution on the pinned 10-variable, 61-operation divisibility graph. It retains at most 100 states at each of eight depths and permits at most 62 operations during the search. A common-factor positive control verifies that the search can find a basic three-to-two gate reduction. Its best found graph has 61 live operations.

The search is beam-pruned and depth/size limited. It is not exhaustive, a minimality bound, a compact-coefficient-specialized test, a zero-set or witness-map search, or a Lean proof. The 10/61 graph's standard-integer equivalence to the relaxed two-norm child and its open original-parent reverse bridge are stated in its own packet.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary10-divisible61-exact-rewrite-search/search.py | cmp - research/ordinary10-divisible61-exact-rewrite-search/receipt.json
```
