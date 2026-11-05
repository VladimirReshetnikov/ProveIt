# Independent review of the bounded 76Y rewrite screen

The [screen packet](../../research/p64-qcube76y-local-rewrite-search/README.md)
was independently rerun under nice 19, idle I/O and a 60-second limit; its
output matched the retained result byte-for-byte and the process exited 0.
The pinned graph has 76 live rows, 14 witness inputs and four port inputs.
The screen reported no smaller live graph in its tested families: one- and
two-operation exact-target substitutions using earlier nodes and literals
0–4, aliases, and a negation when every immediate consumer squares the
candidate node.

The reviewer independently derived the first-gate and second-query counts.
With `n` earlier values, there are `2n²+n` enumerated first gates and, since
no nonconstant sample divisor vanishes and target signatures are nonzero,
`4n−1` second-operation queries. Summing for `n=23,…,98` yields **634,106**
and **18,316**, matching the receipt. The square-root-sign count is 216.
The recorded double-negation control finds a strict reduction, and the separate
square-only sign control finds the expected `0−x` replacement with three live
gates. The script checks primality and rejects optimized Python.

This is a review and reproducibility check of a **finite modular filter**,
not an independent exhaustive symbolic identity proof, a Lean check, or a
global operation lower bound. In particular, it does not rule out multi-node
or semantic zero-set transformations, different witness domains, or
fixed-port-only identities. No Lean process was run for this review.

The [review checker](check.py) pins the graph, screen source and result,
executes the screen, checks exact output bytes, independently recomputes the
first/second query counts and checks both control signatures. Its
[result](result.json) records the checked hashes and scope. Reproduce from
the repository root:

```sh
nice -n 19 ionice -c 3 timeout 60s python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube76y-local-rewrite-independent/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `6fefefe36dfc18115bd09cab3c4a726036a4b3be93e15803dc0253d22b04ba09` |
| `result.json` | `db402c4c652b668e39cc82cb6b189298b945ed62f951c0e9a0343f056bc06416` |
