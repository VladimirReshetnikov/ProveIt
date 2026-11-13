# Bounded local rewrite screen for the 78-operation graph

This applies the [79-operation screen](../p64-qcube79-local-rewrite-search/README.md)
to the pinned 78 graph: one- or two-gate exact-target rewrites, aliases to
earlier nodes or literals, and negation of nodes used only by immediate
square consumers. Three deterministic samples use the checked prime
1,000,000,007; any exact port-uniform identity in those enumerated families
must pass the signatures.

No strict reduction survived. The screen covered all 78 rows, 673,907 first
gates, 19,110 second-operation queries and 200 square-root queries; no aliases
or square-only negations survived. Both positive controls passed, and no
target or nonconstant divisor had a zero sample.

This finite external filter is not a Lean proof or a global operation lower
bound; it excludes neither general multi-node changes nor zero-set-preserving
transformations. A distinct subsequent unit-factor proposal changes the
polynomial itself and is outside the screen.

The following command generated [`result.json`](result.json) with exit 0 on
2026-11-04:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube78-local-rewrite-search/search.py
```

| Artifact | SHA-256 |
| --- | --- |
| 78 `graph.json` | `8037b90bdeb55c5fe91ab2db7e96b8c200f6c48c3ae6f0902e87435d1f1ba096` |
| `search.py` | `e2ff304f02c98f8eb5d4e2c876bff929cf5834fc745357c2f82387dc6ff7e504` |
| `result.json` | `9beac87fab9333c8071f2e86c843a3d29c1ea386d5dc88fa672e66d3b714ea37` |
