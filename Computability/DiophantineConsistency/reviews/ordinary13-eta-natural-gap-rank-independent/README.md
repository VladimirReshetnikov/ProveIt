# Independent review: eta-natural positive gap and rank

The proposed first-norm, positive-gap, signed-rank representation and compact
window interfaces match their pinned sources at the statement level. The
positive-gap arithmetic remains strict at `k=1,r=0`; no eta-positive or
X-positive hypothesis is needed for that scalar argument. No mathematical
mismatch was found in the reviewed interfaces. Lean elaboration, model
provider closure, graph-to-port calibration and the iPRA endpoint remain
unchecked.

The pinned prototype uses `r=n_r` without a shift and
`k=n_eta+n_zeta+1`, hence `r≥0` and `k≥1`, including eta zero. With
natural ports and the proposed signed unit/norm bridge, its first carrier
matches

```
Z=b*(ell+k+r−k*Bt)−Bt, ell=(X*Y²)*k,
Z²=b²*(1+(X*Y²)*(X*Y²+1)*k²).
```

The graph-source binding is proposed by `first_norm`; this review's finite
controls do not elaborate its model casts or `simp` proof. Assuming
`b>0` and `C=q−F−alpha≤0`, natural `X,K0≥0` and `F>0` give
`Bt=C*(X+K0)−F<0`. Therefore
`Z−b*(ell+k)=b*(r−k*Bt)−Bt>0` even when `r=0` and `k=1`.
The exact polynomial identity

```
(ell+k)²−(1+m*(m+1)*k²) = ell*k+k²−1, m=X*Y²
```

is nonnegative for `m≥0,k≥1`, giving a strict contradiction to the first
norm. At the boundary `m=0,k=1,r=0`, the square-gap comparison can be an
equality; strictness comes from `−Bt>0`, not from claiming the square gap is
strict. The independent checker verifies both polynomial identities and
7,488 finite nonpositive-C cases, including 624 with `k=1,r=0`.

The signed-to-natural rank step is conditional on `F≤q`. This is sufficient
for the only potentially negative truncated subtraction `q−F`; `q≥1`
and `q²≥1` handle the other subtractions. Under that premise the pinned
`Residue90GraphNormsDraft.rank_representation` is a fact-level identity for
the same q, F, alpha, J and port tuple. Its source does not need a
residue-90 graph-zero hypothesis. The eta-natural client still must elaborate
the definitional/cast rewriting and obtain `F≤q` from its own gap theorem.

For the compact window, `ports K` is the pinned symbolic tuple
`[betaNat,K,lowNat,betaNat+highNat]`: the low-digit recipe agrees with the
pinned concrete-mask definition, and the last component requires the natural
addition cast. `CompactFixedBeta.bounds` supplies positivity and mask bounds
conditional on J positive. The separately pinned compact rank-window client
requires exactly J/F/alpha positivity, `q=beta*J+1`, and `F+alpha<q`.
The proposed graph client supplies those via its own J/gap sources, but does
not identify a chosen K with physical compact bytes or the user's PDF. It
concludes a rank window only, not `R≥26`, exact Pell witnesses, graph-zero
maps or an internal consistency equivalence.

From this directory run

```
python3 -I -S -B check.py > /tmp/eta-gap-rank-independent.json
cmp result.json /tmp/eta-gap-rank-independent.json
```

The receipt pins key sources, checks two free polynomial identities, 300
finite prototype valuations and the scalar controls above. These do not
establish any all-model source proof or provider build. No reviewed source
was modified.
