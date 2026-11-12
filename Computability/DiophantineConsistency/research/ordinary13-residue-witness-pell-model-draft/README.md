# Witness-preserving 13/90 Pell coordinates

This packet is a **source-only, unelaborated draft**. It refines the existing
conditional graph proof without asserting any iPRA endpoint.

The original `ResidueExactIndexModelDraft.exact_indices_of_actual_graph`
obtains `hny : 2*ycoord n (2*(m−1)+1)=k` from its actual early-index
witness, uses it to invoke `P72Exact.indices_ordinary`, and then drops it from
the result. `ResidueExactIndexWitness` is an exact copy with a new namespace
and that same hny appended to its conclusion. Its graph adapter likewise
retains hny for the **same n and quotient w**, and retains the main ordinate
`ycoord R a=c` by rewriting its actual main index equality `mainIndex=R`.
The generator records these minimal source changes and does not edit any
predecessor source.

For the actual oriented main root, `DirectMainNorm.direct_main_orientation`
returns both the balance and the norm for **that very main**. The independent
natural main root used to construct the main index need not be equal by
assumption. Instead, `main_coordinate_of_norm` applies the source theorem
`ArithmeticPellClassification.solution_index` to the oriented main and c.
If it yields time t, then `ycoord t a=c=ycoord R a` and the existing
`ArithmeticPellCongruences.y_strictMono` implies `t=R`. Its x-coordinate
therefore equals the **oriented main**. Classification assumes precisely the
natural norm; no unproved root-uniqueness or Bézout axiom is imported.

`graph_coordinates_and_balance` uses the orientation's same main and the
preserved w to derive the q-balance with `W=4*X*q*(v7+1)*w`. The first
coordinate is the same n returned by the exact-index proof. The final
conditional `graph_power` combines these with the prior sign-free proof,
including an explicit model-natural `46≤q` premise. It does not supply the
fixed compact port cast/bound, graph-to-parent endpoint, iPRA proof, provider
provenance, `#print axioms` results, or an eta-zero extension. All earlier
graph-zero, positivity, gap, rank-window and model-provider obligations are
inherited, and no Lean elaboration is claimed.

`generate.py` deterministically writes the two local witness-preserving source
copies from the pinned predecessors. `check.py` pins the relevant inputs and
outputs, checks exact source transformations and elementary Pell uniqueness
controls, and never runs Lean. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue-witness-pell-model-draft/check.py | cmp - research/ordinary13-residue-witness-pell-model-draft/receipt.json
```
