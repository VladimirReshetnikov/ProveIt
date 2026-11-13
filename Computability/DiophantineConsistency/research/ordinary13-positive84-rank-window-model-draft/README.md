# Proposed direct positive-84 rank gap and compact window

This is a **source-only, unelaborated** draft. It proposes the previously
explicit `RankWindowGraphCut` from the actual positive 84 graph; it is not a
Lean-checked graph theorem, provider replay, or iPRA endpoint. The separate
same-main-root, strong and auxiliary graph-witness cut remains open.

For the exact first residual, `carrier_positive` uses the graph's own signed
root and norm with positive J, beta, eta and zeta. The general positive-r
first-norm source proposes strict positivity of its signed carrier

```
P=(q-F-alpha)*(X+K0*q)-F*q,  q=1+J*beta.
```

The input ports are natural before their casts. If the signed `q-F-alpha`
were nonpositive, natural X, K0, q and F make P nonpositive, so P>0 gives
`F+alpha<q`. This directly concerns the 84 carrier and does not assume
`q | X`, a 83 graph zero, or a positive sign for the first root.

The proposed `rank_representation` uses that gap to justify casting each
truncated natural subtraction, then matches the actual signed main-rank
field to

```
R=((q-1)*(q-F)+alpha)*(q²-1)+(MC+q*MF)*J.
```

For the compact tuple the draft uses the existing compact beta and mask
bounds and the fourth port **once** as `beta+highNat`, obtaining
`R+q³+q+1≤q⁴`. It separately proposes `R≥26` from q≥6 and positive alpha;
this elementary lower bound uses explicit ordered model arithmetic. Compact
beta and positive J give q≥46. The final source composition yields a
conditional q-divisibility client with only the explicit
`MainStrongAuxGraphCut` among the previously separated 84 graph cuts. That
cut must still bind the actual oriented main root, same Pell index,
strong equation and direct auxiliary witness. The underlying arithmetic,
first-norm, early-index, P72 exact-index, power and port source chains all
remain unvalidated.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-positive84-rank-window-model-draft/check.py
```

The read-only receipt pins sources and actual graph rows, and checks bounded
integer carrier, rank and window controls. Those controls do not prove the
claims for all models, execute Lean, validate provider ancestry or establish
a physical PDF connection.
