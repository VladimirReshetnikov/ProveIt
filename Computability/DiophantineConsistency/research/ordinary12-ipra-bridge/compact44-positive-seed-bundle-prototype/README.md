# Positive ordinary coordinates in the compact seed bundle

`CompactPositiveSeedBundle.seed_bundle_positive` applies to any
model-Σ₁-definable cell function `X` in a model of `IΣ₁`, under the full
symbolic compact `PackingInput` and the existing `SeedBundle` for the same
kernel, length, stride and `X`. It yields `PositiveSeedBundle`: one
existential family of outer and auxiliary witnesses that satisfies every
original seed relation, size bound and positivity statement, and in
addition satisfies

```
0 < f-1, (f-1)+1=f,
0 < delta a*i, 0 < delta a*i+w,
delta a*(f*f-1) = (c*c*c*c)*(delta a*i)*(delta a*i).
```

Here `w>0` is the **auxiliary seed** witness, and its positivity remains
explicit in the output. It is not the shifted-transport power that is also
called `w` in some other interfaces. The `f-1` positivity and square identity
support the ordinary-tail construction, but `delta a*i+w` is not the required
graph coordinate. The exact ordinary-tail bridge requires
`n=delta a*i+(y-w)`; the separate
[ordinate-order theorem](../compact44-aux-ordinate-order-prototype/README.md)
proves `w ≤ y` under explicit seed hypotheses. The proof derives positivity of
the exact constructed rank from
the packing and uses the auxiliary coordinate theorem after unpacking the
seed. Every original and new assertion in the conclusion concerns the
**same existential witnesses**. The statement does not identify these
witnesses with a separately unpacked existential seed; a downstream client
that has already chosen concrete witnesses can apply the pointwise
`CompactAuxPositiveCoordinates.ordinary_coordinates` theorem directly.

The source does not itself construct a packing, evaluate the ordinary graph
coordinates, prove the free-J literal zero, bind retained coefficients or
PDF bytes, or establish an iPRA derivation.

Bounded single-author `observations/attempt01` actually exited 0 without
warnings or `sorryAx`. The named Lean metatheory axiom report is exactly
`[propext, Classical.choice, Quot.sound]`, not an object-theory axiom list.
The client source SHA-256 is
`db828481743fb799570efa2a27d24a668478ece3cbb0d14265e6ca078a18cc1d`; the
output object SHA-256 is
`d4472919732ac045a4987c967f468f8905c7854b671d8c531b877b4a79cb9c5b`.
The attempt records the exact source, terminal receipt, direct dependencies
and companion guards, and selected project/root inventories. The seed and
halt project overlays had 531 matching names at preflight, and recorded
guards and selected inventories were unchanged after the run.

This is a mixed-provider exploratory author result, not a paired replay or
independent artifact audit. The point-in-time checks do not authenticate all
transitive, package or dynamic ancestry and are not continuous filesystem or
whole-process-tree resource monitoring.
