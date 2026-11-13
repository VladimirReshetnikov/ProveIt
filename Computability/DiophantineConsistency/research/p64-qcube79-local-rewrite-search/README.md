# Bounded local rewrite screen for the 79-operation graph

[`search.py`](search.py) applies the same restricted prefilter as the
[83-operation screen](../p64-local-rewrite-search/README.md) to the pinned
[79-operation graph](../p64-qcube79-candidate/graph.json): one- or two-gate
exact-target rewrites, aliases to earlier nodes or literals, and negation of
nodes used only by immediate square consumers. It evaluates three deterministic
assignments modulo the checked prime 1,000,000,007; any exact port-uniform
identity in the enumerated families must pass those signatures.

The screen found no strict reduction in these families. It examined all 79
rows, 694,410 candidate first gates, 19,513 second-operation queries, and
200 square-root queries; neither aliases nor square-only negations produced a
candidate. Its double-negation and square-sign positive controls passed; no
target or nonconstant divisor signature had a zero sample.

This is a finite external filter, not a Lean proof or a global lower bound.
It does not exclude general multi-node changes, three-gate rewrites,
fixed-port identities, witness substitutions, or zero-set-preserving changes.
One unproved semantic possibility is replacing `eta+zeta` by an independent
positive `k`: recovering the positive `zeta` would require proving `k>eta`
for all resulting zeros. Neither that implication nor a counterexample is
established here.

From the repository root, the following command generated
[`result.json`](result.json) with exit 0 on 2026-11-04:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube79-local-rewrite-search/search.py
```

| Artifact | SHA-256 |
| --- | --- |
| 79 `graph.json` | `d70bbed8b36895ffcf144f51bf78287e03fb2942d62c016ac9c845e691820b9b` |
| `search.py` | `4c8e09ecb5ca438123ab0ac1b6cb6e07b5d27f95c6cee651debde2ccbb438f46` |
| `result.json` | `15e1af0a49a3d475fc870dca0a0e848ccabc8053f3936225fda0e489df8d44c9` |
