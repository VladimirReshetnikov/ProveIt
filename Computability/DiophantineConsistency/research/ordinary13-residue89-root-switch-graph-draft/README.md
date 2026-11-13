# Residue-89 graph root-switch model draft

This packet proposes a graph-level existential positive-r replacement for the
13/89 natural graph, then composes it with the weaker 89→90 model transport.
**Every Lean source and imported provider here is unelaborated.** This is not
an internal iPRA proof or a verified endpoint.

The source proposes that a graph zero makes all four squared residuals zero,
extracts the graph's own signed first root and norm, and verifies that changing
coordinate 8 leaves the main, auxiliary and strong residuals unchanged. If
original r is zero and its natural first scale `b=J*beta` is positive, the
separate signed-to-natural extraction draft proposes a positive replacement
`r'=2*tau` that flips the first root and preserves its square. If original r
is already positive, the valuation is retained. The conclusion is an
**existential replacement**, not a claim that every original r is positive.

For the symbolic compact tuple, the draft separately proposes `J>0` from
the first norm and uses `CompactFixedBeta.bounds` for positive beta. K is an
arbitrary standard natural, and this root-switch path assumes no upper bound
on K. The composed conditional parent bridge still depends on the source-only
90→positive-82 forcing and gamma chain. Its positive-82 `PolynomialBridge`
is an explicit external Lean hypothesis. Compact fixed-kernel identification,
physical port bytes/PDF binding, earlier parent equivalence, all provider
ancestry and model-to-iPRA proof remain separate obligations.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue89-root-switch-graph-draft/check.py | cmp - research/ordinary13-residue89-root-switch-graph-draft/receipt.json
```

The read-only check pins graph and draft sources, reruns inherited receipts,
verifies that the three nonfirst residuals do not depend on r, and tests the
signed first-root/update identities on finite tuples. It does not execute Lean,
stage artifacts or validate a nonstandard-model proof.
