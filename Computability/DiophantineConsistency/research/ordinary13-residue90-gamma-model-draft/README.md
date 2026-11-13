# Residue-adjusted 13/90 gamma: fact-level model draft

This source-only client proposes to force `gamma>0` in an ordered IΣ₁ model
from **explicit arithmetic facts**. It is not yet connected to a graph zero,
and neither this source nor its imported overlay drafts has been elaborated
or provider-replayed by Lean.

The new lemma `enlarged_rank_gap` assumes `q≥2`, `X≥1`, `Y≥q³`, the existing
first-Pell lower bound `k≥8XY²+4`, and `R+q³+q+1≤q⁴`. It proposes both

```
R + X*Y*q + 1 < k,       X < eta + Y*k.
```

It does **not** assume `q≤X`. The proof uses `q≤Y`, hence
`q⁴≤Y²≤XY²`, `XYq≤XY²`, and `R+1≤q⁴`; then the left side is at most
`2XY²`, strictly below the supplied Pell bound. The extra `XYq` is essential:
the pinned actual residue-adjusted graph has `g55=E*q`, `E=X*Y`, and its
main expression at gamma zero must be matched with `R'=R+XYq`.

`gamma_pos_of_fact_cut` proposes composing that new bound with the existing
unelaborated `FirstMainLargeKDraft.first_main_large_k` and
`GammaZeroNarrowDraft.gamma_zero_impossible`, instantiating the latter with
`R'`. It explicitly assumes positive parameters, both **natural** first and
main norms, the main discriminant identity, the model rank bound and the
actual signed-pair magnitude equation for the gamma-zero branch. Its
conclusion is fact-level positivity, not an unconditional graph theorem.

A full graph client must still extract those facts and signed magnitudes from
the literal 90-row zero, including nonzero scale and positive quotient witnesses;
prove `C>0`, the forcing and size premises, and the fixed compact-port casts
and bounds in every intended model; connect the graph to the parent and its
historical endpoint; and check all source, transitive providers and axioms in
Lean. The retained current-2011 PDF ports are different from these compact
ports. No result here proves an iPRA endpoint or a global equation minimum.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue90-gamma-model-draft/check.py | cmp - research/ordinary13-residue90-gamma-model-draft/receipt.json
```

The check pins source and graph bytes, rechecks the external route audit and
the graph's unshifted gamma and `E*q` wiring, and tests bounded numerical size
cases. It does not invoke Lean, validate tactics, or authenticate compiled
providers.
