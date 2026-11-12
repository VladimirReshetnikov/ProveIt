# Residue model rank lower bound: source-only draft

This standalone source proposes the stronger bound `R≥40` from
`F>0`, `alpha>0` and `F+alpha<q`, with the exact natural rank

```
R = ((q-1)*(q-F)+alpha)*(q*q-1) + (MC+q*MF)*J.
```

The proof sketch is `q≥3`, `q-1≥2`, `q-F≥2`, so the first coefficient is
at least 5 and `q²-1≥8`. Their product is at least 40; the remaining rank term
is nonnegative. A separate specialization uses the actual 90-row model rank
and keeps its positive-C gap as an explicit hypothesis. It may eventually
supply the `R≥26` input of the [exact-index client](../ordinary13-residue-exact-index-model-draft/),
which retains that premise independently.

All source, model subtraction tactics and provider imports are **unelaborated**.
The literal graph's C-gap, exact-index client, compact port binding and model
to iPRA endpoint remain separate obligations. No eta-zero generalization is
assumed or asserted.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue-rank-lower-model-draft/check.py | cmp - research/ordinary13-residue-rank-lower-model-draft/receipt.json
```

The read-only check pins sources, replays the graph-norm receipt and tests the
scalar lower bound on a finite natural box. It never runs Lean or stages.
