# Affine-inlined sharing seed candidate: 59 witnesses

This is an **external candidate**, not yet a Lean model theorem or a nine-variable iPRA endpoint. Its source is the current 14-positive-variable, 65-operation graph used by the maintained equation, with the exact four current fixed ports. A separate external `source_binding.py` compares its complete graph DAG with `ObjectCurrentEquation2011.expressionAt`, modulo associative/commutative multiplication and signed addition. The independently checked port-byte records remain external; no Lean theorem reads this graph JSON or gzip files.

The seed reserves coordinate 0 as the distinguished Jones input and uses coordinates 1–14 for natural values shifted by one. Each graph value is represented as a pair of nonnegative natural expressions whose difference is the integer value. For addition, subtraction, and multiplication the pair operations are respectively

```
(a⁺+b⁺, a⁻+b⁻)
(a⁺+b⁻, a⁻+b⁺)
(a⁺b⁺+a⁻b⁻, a⁺b⁻+a⁻b⁺).
```

With zero terms simplified, the generator inlines a graph node if both pair components are affine in the seed witnesses. Otherwise it introduces natural witnesses for its nonzero pair components and adds one residual per introduced coordinate. Every materialized right-hand side has degree at most two because its previously inlined operands are affine. The final source operation is asserted directly as one residual. The concrete `seed.json` has 30 inlined and 34 materialized internal gates, requiring 45 materialized gate coordinates, hence `14 + 45 = 59` natural witnesses plus the distinguished input. There are 46 residuals. The seed is the sum of their squares and has degree at most four in those 60 coordinates, treating the fixed ports as constants.

The seed does not use the distinguished input coordinate. At zero witnesses the first residual is `−(β+1)²`; the actual fixed β bytes represent a positive integer, so this residual is nonzero for **every** distinguished input. Consequently the sum of squares is nonzero there, which is the required Jones normalization. No separate guard witness is needed.

The intended all-IΣ₁-model proof is finite: construct each materialized nonnegative pair component recursively from a positive zero of the 65 graph, and conversely use the vanishing squared residuals to inductively identify every represented pair difference with its graph value. The final residual then enforces the graph's zero. A checked Jones endpoint would also require a Lean `Expr` construction for this exact seed, a formal quartic degree bound, the normalization proof, this two-way model bridge and an application of `NineFreshJones.nine_iff` followed by the current consistency bridge. None of those new Lean obligations is claimed complete.

`check.py` independently recomputes the pair formulas as sparse formal polynomials, verifies every inlining/materialization decision, residual, coordinate, degree bound and exact fixed-port byte/bit-length record, checks the nonzero first residual, and exercises 12 deterministic witness constructions. `source_binding.py` independently checks the source graph against the current Lean expression DAG. These are external computations, not a Lean numeric, file-content, graph, degree or iPRA proof. The 59 figure is the declared quartic-seed witness count; it is not the operation count or degree of the resulting nine-variable Jones polynomial.

Run `python3 -I -S -B check.py` and `python3 -I -S -B source_binding.py` from this directory. `build.py` deterministically emits the frozen `seed.json` and refuses to overwrite it.
