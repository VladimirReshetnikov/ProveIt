# Bounded local rewrite and alias screen for 76Y

[`search.py`](search.py) adapts the P64 local screen to the pinned 76-gate
independent-`y` graph. It tests these restricted families for a smaller live
graph:

* replace one target by one or two binary operations on earlier nodes and
  literals 0–4, with the second operation using the fresh intermediate;
* alias one target to an equal earlier node or literal; or
* negate a target used only by immediate square consumers, using one
  subtraction of earlier nodes or literals.

It uses exact modular arithmetic at three deterministic assignments modulo
the checked prime 1,000,000,007, varying all 14 witnesses and four ports.
No strict candidate survived. The screen covered all 76 targets, 634,106
first-gate constructions, 18,316 second-operation queries and 216
square-root-sign queries. No target or nonconstant divisor had a zero
sample; the built-in double-negation and square-sign positive controls
passed. Any exact port-uniform identity in these enumerated families would
have to match the tested signatures. Conversely, a surviving signature would
be only a candidate requiring exact symbolic and Lean verification.

This is a finite external filter, **not** a Lean theorem or a global operation
lower bound. It does not cover arbitrary multi-node changes, three-gate
rewrites, fixed-port-only identities, changed witness domains, general sign
symmetries, or semantic zero-set equivalence without polynomial equality.
The graph JSON is an external artifact; its connection to the Lean graph and
the iPRA endpoint have their own separate qualifications.

The pinned input is
[`graph.json`](../p64-qcube76-independent-y-candidate/graph.json), SHA-256
`196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c`.
The command below exited 0 on 2026-11-04, and a separate author rerun
reproduced [`result.json`](result.json) byte-for-byte. Both runs used nice 19,
idle I/O and a 60-second wall bound; no Lean process was invoked. From the
repository root:

```sh
nice -n 19 ionice -c 3 timeout 60s python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube76y-local-rewrite-search/search.py > /tmp/p64-qcube76y-local-result.json
```

| Artifact | SHA-256 |
| --- | --- |
| `search.py` | `3f6982c59a0148053ffa2b0e3f97b8267feff1e4eaeb0b2e645a439e91d32fea` |
| `result.json` | `820e962b32d6759765b43122d2f91e94471a9d29a8c205079dfcc51882892b1b` |

An [independent review](../../reviews/p64-qcube76y-local-rewrite-independent/README.md)
reproduced the result and the candidate counts. It retains the same bounded
filter scope and does not establish a global lower bound.
