# AQ20/104 residual-map source draft

This packet proposes Lean proofs of the two model graph-zero obligations in
[the AQ20 conditional transfer](../adaptive-aq20-substituted104-model-draft/).
**Everything here is unelaborated source**; no Lean kernel, tactic, axiom or
provider-ancestry verification is claimed.

Eleven proposed residual identities compare the AQ20 residuals to those of
AQ22/110 after inserting the two scale formulas. Two further identities make
the parent scale-binding residuals zero. They explicitly assume that the
cast of signed port zero in `DiffRing V` equals `ι beta`. `extend_zero` uses
these 13 identities. `parent_scales` proposes to recover the two positive-model
scale equalities from the parent zero via the two binding residuals and
injectivity of `ι`; this establishes `extend_project` and `project_zero`.
The final declaration proposes a proof of AQ20 `GraphZeroObligations`. The
AQ22 quotient graph obligations and historical parent bridge remain separate;
this packet does not establish an unconditional fixed-port endpoint.

The AQ20 graph checker verifies the 11 polynomial identities, both vanishing
bindings and all sum wiring independently over arbitrary signed ports. That
check does not verify these Lean proofs, model interpretation or the precise
port cast. Strict positivity of represented beta is used in the earlier
transfer to preserve positive witnesses; the algebraic graph identities here
need only its exact representation. The 124-operation natural JSON remains
unconnected in Lean to the positive shift. See the [conditional transfer](../adaptive-aq20-substituted104-model-draft/README.md)
for the inherited endpoint and provider boundary.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B research/adaptive-aq20-substituted104-residual-maps-draft/check.py | cmp - research/adaptive-aq20-substituted104-residual-maps-draft/receipt.json
```

The check is read-only and bounded to pinned sources, case coverage and the
existing graph checker; it runs neither Lean nor staging.
