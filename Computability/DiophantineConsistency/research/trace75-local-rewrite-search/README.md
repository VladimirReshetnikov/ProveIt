# Bounded local rewrite screen for the established trace75 graph

`search.py` screens the hash-pinned 75-operation trace graph for strictly
smaller live DAGs in three restricted families:

* Replace the value of one existing target node by one or two binary
  operations on earlier nodes and literals 0–4. For two operations the
  second uses the fresh intermediate; the implementation includes both
  subtraction orientations and a square of that intermediate.
* Replace a target by an earlier node or literal with the same value.
* Replace a target used exclusively by square nodes by the negative of
  its value, represented as one subtraction of earlier nodes or literals.
  Negation is output-preserving for this restricted consumer pattern.

All four ports and ten witnesses are sampled independently, so this is a
port-uniform filter. It uses three deterministic assignments modulo the
checked prime 1,000,000,007. An exact integer-polynomial identity in one of
these families must match all three signatures; surviving candidates would
need exact symbolic and Lean verification. No strict reduction survived:
75 targets, 544,900 first-gate constructions, 16,725 second-operation
queries and 96 square-root-sign queries were examined. No target or
nonconstant divisor signature contained a zero. The two additional
families found no candidates either.

Two positive controls detect a redundant double negation at the output and
a strictly reducing sign change before a square. They exercise the search,
not the mathematical equivalence of a new equation. The sign family only
enumerates a single subtraction and square-only immediate consumers; it is
not a general search for sign symmetries.

The result is **not** a global operation lower bound or a Lean theorem. It
does not cover changes to multiple target values, arbitrary three-gate
rewrites, fixed-port-only identities, different witness domains, zero-set
equivalence without polynomial equality, or all simultaneous sign changes.
In particular it does not prove the trace75 equation is minimal. The
source graph is package 163's `trace75_degree402.json`, SHA-256
`8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9`;
this packet does not authenticate any external or Lean provider ancestry.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/trace75-local-rewrite-search/search.py
```

Actual session 74018 exited 0 and produced [`result.json`](result.json).
Optimized Python was separately rejected with exit 1. Source SHA-256:
`a36c5237f2b667f44a4450b8a504a993e3fe0b459b24615dbc3dd1a50945a4e5`;
result SHA-256:
`492966500a8b60d48462777d4a44a0da4328ed21fd1942dc6b1a9c1142c24b0b`.
