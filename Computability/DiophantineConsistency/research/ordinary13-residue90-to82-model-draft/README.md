# Direct residue-90 ↔ positive-82 model transport draft

This packet proposes a direct no-zero bridge from the 13-natural-input,
90-operation residue graph to the positive-shifted version of its 82-row
positive parent. **All Lean source and imported provider chains are
unelaborated.** The source is a proof proposal, not a Lean theorem or an
internal iPRA endpoint.

The 90 graph leaves coordinates `J,f,X,y,gamma` (indices `0,3,6,11,12`)
unshifted and adds one to the other eight. The draft's mixed valuation applies
exactly that substitution. It proposes four all-ring residual comparisons
and their pointwise output equality at arbitrary signed ports. The reverse
map sends a positive parent valuation to its natural predecessors on the
eight shifted coordinates; from a 90 zero, the forward map needs all five
unshifted coordinates positive.

`forced_pos` composes the separate, source-only J, X, f/y and gamma forcing
drafts for the compact-symbolic tuple. K remains an **arbitrary standard
natural**. Their graph norm, divisibility, Pell, rank, compact-port and
provider assumptions and proof status are inherited. The endpoint client
explicitly assumes a Lean-level `PolynomialBridge` for the positive-shifted
82-row parent; it does not construct that bridge, authenticate a specific
fixed K and compact port bytes, relate them to the current-2011 PDF, or prove
an iPRA endpoint for the new expression.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue90-to82-model-draft/check.py | cmp - research/ordinary13-residue90-to82-model-draft/receipt.json
```

The read-only checker pins the graph and draft sources, checks the exact
eight mixed-shift row substitutions and residual vector arity, replays the
parent graph and inherited source checks, and tests signed tuples. It does not
run Lean, stage artifacts or authenticate compiled providers.
