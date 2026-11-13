# Independent source review: generic auxiliary-root model draft

**Source review passes; not elaborated.** Under the explicit assumptions
`1<Q` and `1<z*z` in the ordered difference ring, the proposed auxiliary
norm `y²−Q(y²−z²)=1` rearranges to
`(Q−1)(y²−z²)=z²−1>0`, so `y²>z²`. If `y=z+ι u>z`, that strict square
inequality forces y positive. Conversely, a positive y with larger square
must exceed z, so y−z is positive. The cited difference-ring `nonneg_iff`
represents each positive ring quantity by an embedded natural element, and
`ι_lt_ι` transfers the required positivity back to the model. This supplies
the two proposed fixed-other-residual coordinate maps, conditional on the
separately uncompiled five-square lemma.

The two strict assumptions are essential to this fact-level argument and are
not derived from the 78/79 graph in this packet. For example, `Q=4,z=y=1`
satisfies the norm but gives no strictly positive old difference; with
`Q=0,z=2,y=1` the strict-square conclusion itself fails. The independent
checker verifies these controls, checks the old/direct auxiliary identity in
a sparse integer polynomial ring, pins the source interfaces, replays the
author's inventory and the separate generic-root review receipt, and tests
finite integer norms and both sign-sensitive witness implications.

These are source and finite checks, not Lean elaboration or an arbitrary-model
theorem. In particular `nlinarith`, ordered-ring instances, cone extraction,
casts and provider ancestry are untested. The graph-specific derivation of
`1<Q` and `1<z²`, valuation updates, graph binding, other parent bridges,
and the iPRA endpoint remain open. No Lean process is run.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary14-aux-root-model-draft-independent/check.py
```

Compare stdout with `result.json`.
