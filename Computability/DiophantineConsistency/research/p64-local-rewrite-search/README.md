# Bounded local rewrite screen for the P64 graph

[`search.py`](search.py) screens the pinned 83-operation package-64 graph
for strictly smaller live DAGs in the same restricted families as the
[trace75 screen](../trace75-local-rewrite-search/README.md):

* replace one target by one or two binary operations on earlier nodes and
  literals 0–4, with the second gate using the fresh intermediate;
* replace a target by an equal earlier node or literal; or
* negate a target used only by immediate square consumers, using one
  subtraction of earlier nodes or literals.

It samples the 14 witnesses and four ports independently at three
deterministic assignments modulo the checked prime 1,000,000,007. Exact
port-uniform identities in these enumerated families must pass all signatures;
any surviving reduction would require exact symbolic and Lean verification.
No strict reduction survived: the screen examined all 83 targets, 780,532
first-gate constructions, 21,165 second-operation queries and 192
square-root-sign queries. No target or nonconstant divisor signature had a
zero sample. Neither the alias nor the square-only negation family produced a
candidate. Two positive controls exercise double-negation and square-sign
rewrites.

This is an external finite filter, **not** a Lean theorem or a global
operation lower bound. It does not cover arbitrary multi-node changes,
three-gate rewrites, fixed-port identities, zero-set equivalence without
polynomial equality, changed witness domains, or general sign symmetries.
The [P64 endpoint record](../fourteen-p64-endpoint/README.md) has separate
proof and provider qualifications.

The source is package 64's `positive14/polynomial.json`, SHA-256
`b9731360a30bcbcfd6f9161241cafb01b8c5d68aa40b84ddc50ba689a0745d0e`.
From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-local-rewrite-search/search.py
```

On 2026-11-04 the command exited 0 and produced [`result.json`](result.json).
A separate author rerun exited 0 and reproduced it byte-for-byte. The
runner rejects Python optimized mode.

```text
772c02d5cca78720adcbf4602ebcf0652b70ac1e928655d590f00bb548687196  search.py
b9a90f77bf85a9f3c0e97697297213ac3d41b726f9992426be0d1bfb9d6f079a  result.json
```
