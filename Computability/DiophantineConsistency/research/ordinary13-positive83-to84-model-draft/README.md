# Conditional positive 83 to positive 84 model transport

This is an unelaborated source draft, not a Lean-checked equivalence, provider
replay, or iPRA endpoint. `PositiveUnscaled84Graph.lean.src` transcribes the
exact 84-operation graph, with the same compact port order as the 83 graph.
The receipt checks its full generated body against the pinned JSON.

The proposed model maps use `q=1+J*beta` in the model naturals. Given a
positive 83 valuation with `w<gamma`, the 84 coordinates replace w by
`X=q*w` and gamma by `gamma-w`. Given a positive 84 valuation with `q | X`,
the other map chooses a positive natural quotient `w` and replaces gamma by
`gamma+w`. The difference-ring equality underlying both maps is

```
U*(gamma-w)+(X*Y)*q = U*gamma,
X=q*w,   U=Y*q².
```

`Positive83To84Transport.lean.src` proposes the exact graph output identity,
positive-domain maps, and zero transports. Its `GammaCalibration` records
all the actual same-witness facts required by the existing
`ModifiedCarrierGammaDraft.gamma_gt_from_modified_balance`: natural rank R,
Pell coordinates c and d at that same index, the k decomposition, and the
oriented subtraction-free balance. It is deliberately an explicit input;
this packet does not claim that an 83 graph zero supplies those facts. It
also does not use a hypothetical 83→81 map to obtain them.

`Positive83To84Bridge.lean.src` makes separate all-model cuts for gamma
positivity and 84-side `q | X`. It gives a source composition for `SameNoZero`
and the 83 bridge conditional on those cuts and the exact 84 parent bridge.
The optional native85 client additionally retains the 81/83 CrossRootCut as
an explicit input. The graph-specific exact-index, actual oriented main root,
rank and `q | X` recovery, plus all source/model/provider and axiom checks,
remain open. No claim about the current displayed PDF follows.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-positive83-to84-model-draft/check.py
```

The check pins source bytes, verifies exact graph edits and the generated
84 graph body, proves the small carrier identity by formal integer polynomial
normalization, and samples full integer graph evaluations. It does not
elaborate Lean, validate tactic execution, prove the positive-model cuts, or
check the endpoint's provider ancestry.
