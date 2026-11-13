# Exploratory per-position no-carry extraction

`CompactPositionIncrement.increment_digits` exposes the intermediate
per-position fact used inside the existing `CompactMixedIncrement` proof. In
an arbitrary `IΣ₁` model, for positive `m,N`, a low mask `MC<2^(67m)` whose
origin digit is `2^67−2`, `C≥1`, and the explicit global premise

```
NoCarry (C-1) (MC * rep (67*m) N + 1),
```

it proves `dig 67 C 0=1` and, for every `0<k<m*N`,
`NoCarry (dig 67 C k) (dig 67 MC (k % m))`. The strict `k>0` condition is
essential to the stated argument; the origin is handled separately.

`CompactPositionGraph` combines that lemma with the existing exploratory
same-witness graph saturation result. Its generic theorem has explicit
symbolic beta and low/high mask equalities. Its fixed wrapper assumes the
fixed *symbolic* beta, low and high ports, arbitrary natural `K`, positive
graph coordinates and the literal graph zero. It obtains common model values
`N,w` giving the graph radix and repunit identities, the graph congruence,
origin digit, the per-position low-mask no-carry fact above with `m=8807`,
and the existing global high-mask no-carry statement. The exact propositions
and casts are in the source.

Successful single-side exploratory sessions 27550 and 96628 actually exited
0, without warnings; all three named reports were `[propext, Classical.choice,
Quot.sound]`. Exact commands, source and object hashes, and observed reports
are recorded in `observation.txt`. The first direct fixed-symbolic attempt
session 7128 exited 1 on recursion depth and printed a `sorryAx` report for
the failed theorem. A retry with increased recursion depth, session 14373,
exited 1 at Lean's 3,000 MB kernel memory limit and did not prove the fixed
client. Both failed sources are retained: attempt 02 is the exact retained
retry; attempt 01 is reconstructed by removing the sole added
`maxRecDepth` option from it. Splitting the generic extraction and graph
specialization avoids that observed failure.

The sources were compiled once on a scratch author-side overlay with
exploratory same-witness saturation and congruence objects. This is not a
coherent paired replay or independent artifact audit. It does not prove that
symbolic ports or K equal retained bytes, classify each selector slot, prove
word or fractional-rotation bounds, construct a clean carry, instantiate the
943-row local decoder, derive a machine computation, or establish an internal
iPRA theorem. Those remain separate obligations.
