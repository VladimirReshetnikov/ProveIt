# Static review of the bounded P64 rewrite screen

The source and saved result are consistent with the packet's **limited
modular screen**. This review did not rerun the full search or run Lean.

The pinned graph, search script, and result hashes match. An independent
walk found 23 initial inputs/literals, 83 topologically ordered binary
gates and 83 gates reachable from the output. The first-gate count follows
independently from `Σ(2n²+n)=780532` over the 83 earlier-node pool sizes.
Assuming the recorded absence of nonconstant zero divisors, the four
second-operation queries per earlier value except literal zero give
`Σ(4n−1)=21165`, also matching the saved result. The recorded candidate
lists are empty and the saved positive controls contain candidates. The
192 square-root queries and sample-zero claims were inspected in the
saved result but not independently recomputed.

The code samples all witnesses and ports at three deterministic assignments
over a checked prime field; first gates use earlier nodes and literals
0–4, and second gates use the fresh first result with an earlier value,
including the square case. Separate code tests direct aliases and
negations used only by immediate squares. Any exact port-uniform identity
in those enumerated forms must match its sampled signatures, but the
saved absence of candidates is not an unrestricted polynomial lower
bound, a zero-set equivalence search, or an iPRA theorem. The stated
exclusions for larger rewrites, fixed-port identities, changed domains
and general sign transformations remain material.

The following read-only static check exited 0, producing
[`result.json`](result.json):

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-local-rewrite-independent/review.py
```

```text
f8cfd5a16c397ca18f012f19a6a32071656927216c8bbe20882947556d1446a7  review.py
b8df935c061ec97d970902da1a2db5dc0993e459b495274cd0014aff0825d5b3  result.json
```
