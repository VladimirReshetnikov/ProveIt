# Bounded exact-ring rewrite screen of the eta/zeta 85-row parent

The exact parent `research/ordinary13-eta-zero-graph-adapter-audit/prototype.json` has 85 live binary operations under hash-consing and commutative add/multiply. The two pinned source-only screens reuse the existing canonical local rewrite generator and a seeded beam search. Both include a positive control where common-product factoring reduces three gates to two.

The wider screen retains at most 120 states per depth for eight depths, temporarily permits 86 live gates, and retains 85 as its smallest graph. The smaller independent seeded configuration retains at most 30 states for four depths and also finds no reduction. The rewrite rules cover local reassociation, signed three-term rearrangements, factoring and distribution; beam pruning, depth limits and the allowed intermediate size make this **non-exhaustive**. It is not a global lower bound and says nothing about zero-equivalent changes of coordinates. No Lean or endpoint claim follows.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-eta85-exact-rewrite-investigation/screen.py | cmp - research/ordinary13-eta85-exact-rewrite-investigation/receipt.json
python3 -I -S -B research/ordinary13-eta85-exact-rewrite-investigation/wide.py | cmp - research/ordinary13-eta85-exact-rewrite-investigation/wide-receipt.json
```
