# Independent source review: positive-84 divisibility and Mersenne condition

This is a bounded source/mathematical review of
`research/ordinary13-positive84-division-model-draft/`. No Lean, builds,
staging or provider replay was performed. The receipt pins the exact 84
graph, cited arithmetic and endpoint interfaces, and reproduces the author's
checker.

The graph's main carrier includes the actual extra `X*Y*q` term.
`OrientedIndexCut` explicitly asks for a same-model R, main and quotient w
satisfying both its exact index decomposition and its extra-term oriented
balance. It does not assume `q∣X`, an 83 zero, or the no-extra-term carrier.
The separate `PowerGraphCut` asks for some exponent with `X=Exp.exp R`;
that exponent need not equal the one in the index cut for the final
cancellation. Both are assumptions of the proposed graph client.

The cited `ResidueThreeProjectionDraft.q_dvd_threeX` has the matching
extra-term balance and `Y=q³*s` inputs, and proposes `q∣3X` without a
Bézout or `q∣X` premise. The receipt checks the underlying exact polynomial
step: if `H=3+4Y*(X+1)` and `Y=q³*s`, then

```
H*X−3*X = q*(4*q²*s*(X+1)*X).
```

This identity alone does not extract the oriented balance or establish the
graph cut; the cited proof also needs its same-model positivity, cancellation
and signed-to-natural divisibility reflection.

The final source calls `ModifiedCarrierFactsDraft.compact_beta_divides_X`
with the separate power witness and `q∣3X`. Its cited Mersenne theorem
requires `d≥4` and the represented equation `q=(Exp.exp d−1)*J+1`; the
compact source specializes `d=67*8807` via `CompactFixedBeta.beta_identity`.
The receipt checks these source signatures and the identical q definitions
in the division and 83/84 transport clients. It does not authenticate the
model cast or external fixed-beta bytes.

The simple scalar `q=3,X=8` has `X=2³` and `q∣3X` but not `q∣X`; it is not
an 84 graph zero and does not meet the specific compact Mersenne condition.
It shows why the exact cancellation hypothesis matters. The inspected cuts
and projection do not obtain `q∣X` by first using 84→83, but their actual
positive-84 graph witnesses, source tactics, transitive providers, axiom
reports, parent bridge and iPRA/ZFC/PDF binding remain open.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive84-division-mersenne-independent/check.py
```
