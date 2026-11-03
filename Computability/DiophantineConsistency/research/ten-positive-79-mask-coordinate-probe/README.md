# 79-row mask-coordinate probe

This is a **candidate**, not a proved consistency equation. It keeps the ten
positive input slots and four fixed ports of the original-kernel 80-row graph,
but uses `C` instead of `alpha` in input slot 2. It retains the parent's
coefficient tuple by reference; no new coefficient file or display is claimed.
The graph has 79 live operations: 48 multiplications, 17 additions and 14
subtractions. All ten witness inputs and all four port inputs remain live.
No degree claim is made for the changed coordinate chart.

Write `b = beta*J` and `q = b+1`. The old graph computes

```
qmF = q - F
C   = qmF - alpha
G1  = b * qmF
G   = G1 + alpha
```

The new graph takes `C` as input and computes instead

```
qmF = q - F
G1  = q * qmF
G   = G1 - C
```

It deletes only the old `C` row and otherwise keeps every parent row in its
original order. Substituting `alpha = q-F-C` gives the same old and new `C`
and `G`, since `b*(q-F)+(q-F-C) = q*(q-F)-C`. The private `G1` has no other
users, and all remaining rows therefore agree by induction. Thus, for every
commutative ring and arbitrary ports,

```
P79(J,F,C,...) = P80(J,F,q-F-C,...).
```

The affine coordinate map is an involution over an unrestricted ring, so the
two polynomial equations have equivalent unrestricted ring valuations. This
does **not** establish equivalence for strictly positive witnesses. An old
positive zero has positive old `C` under the hypotheses of the existing
`Direct80TransportModel.graph_transport_and_mask` theorem. In the reverse
direction, a positive candidate zero must additionally satisfy
`F+C < q` to recover positive `alpha = q-F-C`. The currently checked transport
bound establishes positivity of `C` in the old chart; it does not by itself
establish this new inequality. Existing `Direct80RankOrientation` also uses
the positivity of the old `alpha`. We do not know whether the candidate's zero
equation forces the missing inequality or whether positive spurious zeros
exist.

`check.py` is a standalone read-only check. It pins the parent and candidate
bytes, verifies topology, operation counts, all inputs and rows live, the
exact changed rows and all other rows, and proves the small changed-region
identities by integer sparse-polynomial normalization. This is an external
algorithmic check of a ring identity, not a Lean theorem. It additionally
checks 100 modular sample evaluations as a regression check; the samples are
not the proof of the identity. Run it with `python3 -I -S -B check.py`.
The captured output is `check-observation.txt`, SHA-256
`febb46c08a50887ce159f44b1d242483870a20c506a27fbc424c828440ae71c8`.
The candidate SHA-256 is
`5389bb9386371ca71790c5bbac3e5307f4b15ee278e560c13089d65f3ea25d00`;
the checker SHA-256 is
`fbbc2b62479d8c3978598893b8833a24feebcb696da0698607e6f9f94a7b377c`.
There is no claimed positive-domain converse, HA/iPRA endpoint, formal Lean
binding, or file/PDF correspondence for this candidate.
