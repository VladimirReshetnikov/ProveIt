# Proposed reverse model witness for the 72/46 shear

This source-only draft proposes a **complete reverse witness map** from a
positive-shifted 72/46 candidate zero to a positive-shifted 71/60 parent
zero at the same current2011 ports. It composes unelaborated literal,
nonzero and magnitude drafts. It is **not a checked Lean theorem**, final
zero-equivalence, or iPRA endpoint; its materialized import names, tactics,
types and providers have not been tested.

The distinct preceding [graph-bounds client](../current2011-shear72-reverse-graph-bounds-draft/README.md)
proposes, from an actual candidate ring zero and positive shifted inputs,
a positive model-natural m with

```
(ι m)² = (V + y_child)².
```

Here `V` and `y_child` are the fields at the **same child valuation**. The
signed ordinate need not itself be positive. Define the natural parent
valuation by replacing only coordinate 12 with `m−1`. Since m>0, its
positive shift is m, so the proposed full valuation identity is

```
ringValuation (update v 12 (m−1))
  = update (ringValuation v) 12 (ι m).
```

The parent graph uses coordinate `y` only through the row `y2=y*y`.
Consequently its **entire output** is unchanged by replacing y with any
ring element of the same square; the draft states a generic all-ring
`parent_eval_update_same_square`. The separate literal-evaluator draft
relates the child ring value to the parent value at the signed shear
`update u 12 (V+u 12)`. Combining that identity with the square equality
and the shifted update gives the parent ring zero and hence its internal
positive-shifted zero. The source exposes this as `reverse_zero_of_magnitude`
with the positive m and its square equality explicit, then proposes
`reverse_zero` by invoking the graph-bounds client and current beta/shift
positivity.

[`ReverseCoordinateMap.lean.src`](ReverseCoordinateMap.lean.src) uses the
prospective qualified import `DiophantineConsistency.Shear72ReverseGraphBounds`;
that predecessor itself imports other inert source snapshots. A later
coherent materialization must assign one logical module name to each
predecessor: some separate forward draft examples currently use unqualified
local names. `simp` for finite-index updates, equality of the full parent
outputs, `tsub_add_cancel_of_le`, source types, and casts are unverified.

The [checker](check.py) pins direct source/graph inputs, checks that `y` has
exactly the one squared-row use in the literal parent, and checks selected
coordinate/successor interfaces. This is finite structural evidence, not a
Lean proof of the source/JSON correspondence, the all-model magnitude
claim, provider closure, or either direction of the final equivalence.
The forward map, joint no-zero statement, native/standard/iPRA/Gödel–Gentzen
clients, and PDF/document semantics remain separate.

```
python3 -I -S -B research/current2011-shear-reverse-coordinate-map-draft/check.py > /tmp/shear-reverse-map.json
cmp /tmp/shear-reverse-map.json research/current2011-shear-reverse-coordinate-map-draft/result.json
```

No Lean/build/staging operation is performed.
