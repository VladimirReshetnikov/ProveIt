# Independent source review: positive 84/87 unscaling

This is a bounded source/mathematical review of
`research/ordinary13-positive84-to87-unscale-model-draft/`, not a Lean or
provider replay. The receipt independently regenerates both exact graph
literals, checks all JSON rows and coordinate positions, reproduces the
author's and earlier graph-audit receipts, and proves the scaling identities
in a free integer polynomial ring.

With h=q³, an 87 valuation has `Y=h*s`. The source's forward update changes
position 7 to s and position 8 from `r_old` to `r_old+s`; all other positions
are unchanged. Under that exact relation, its proposed `first_scale` states
`Z87=h*Z84` at the root level and `A87=h²*A84` at the residual level. The
checker verifies those identities without sampling. The source's `shared`
claims equality of the other three residual fields for any target r. The
outputs are not pointwise equal: their first squared terms differ by h⁴.
The theorem quantifies s as a model-natural element without requiring it
positive; the graph ports are arbitrary signed integers.

`ForwardGraphCut` is correctly oriented from a positive **87** zero to a
positive model-natural s with `Y=q³*s` and nonzero q. The assembled
87→84 witness is `update v s (v8+s)`, and q nonzero justifies cancelling
q⁶ from the first residual. `ReverseRootCut` is correctly oriented from a
positive **84** zero to positive Y and a possibly fresh positive r giving
an actual **87** first residual zero, with `Y=q³*s`. The 84→87 proof uses
that cut and the shared non-first fields; it does not assume the naive
predecessor `r84−s` is positive. Both cuts are explicit assumptions of the
proposed `positive_zero_iff`.

`ForwardNormBinding` is a separate open source obligation: for each positive
87 zero it asks for a model-natural beta representing the signed first port
and an n satisfying `ScaledFirstCut`. The latter binds the actual 87 root and
Bt to the signed root equation and scaled square norm. Given those premises
and positive Y, the proposed `quotient_of_cut` calls the matching conditional
`Ordinary13QCube93ArithmeticDraft.positive_quotient_of_signed_norm`; its
existing source proof uses signed-square divisibility and reflection into the
same model naturals. `forward_of_norm_binding` then derives positive q from
`q=1+v0*beta`. Neither the graph norm binding nor the reverse-root cut is
discharged here.

The source's natural and difference-ring casts, positive-coordinate maps,
`simp`/`rw`/`ring` scripts and all imported providers remain unelaborated.
No `PolynomialBridge`, actual compact port/file/PDF binding, axiom report or
internal iPRA/ZFC equivalence is established by this packet or its receipts.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive84-to87-unscale-source-independent/check.py
```
