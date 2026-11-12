# Residue-89 forced-r model arithmetic draft

This source-only packet proposes fact-level lemmas for the 13/89 graph's
first-root coordinate. **No Lean declaration has been elaborated.** It does
not extract the displayed facts from a graph zero or establish a parent bridge.

`r_positive_of_branches` takes natural `r,k,P,t,m,ell,tau`, with `k≥2`,
`P>0`, `P<m`, `0<t≤P`, `ell=m*k`, `tau>ell` and the two possible natural
additive equations that would follow if `r=0`. The plus branch contradicts
`tau>ell`. In the minus branch the crucial **correct** strict estimates are

```
k*(P-1) < ell,    t < m ≤ ell,
k*(P-1)+t < 2*ell < ell+tau.
```

It does not use the false stronger claim `k*(P-1)+t≤k*P`.
`branches_of_signed_root` proposes deriving the two additive alternatives
from positive model-natural b, `P=b*t`, the exact signed root at r=0 and its
`±b*tau` signs. `tau_gt_ell` proposes the elementary first-norm square
comparison. `P_below_m` proposes the graph's size cut under the explicit
model assumptions `q≥2`, `X≥1`, `Y≥q³`, `K+1≤q²`, `C<q`, `F>0`,
`P+F=C*(X+K)` and `m=X*Y²`.

The graph client still has to derive positive J/X, the first root norm and
sign/quotient witnesses, positive represented P/C, and the represented
compact kernel inequality. The author's separate root-switch argument may
avoid forcing r and this K upper bound entirely, but that alternative has its
own unsigned/signed reflection and witness-transport obligations. The gamma
forcing, 90/82 parent bridge, fixed compact kernel/byte binding, provider
ancestry and internal iPRA endpoint are also separate and remain open.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue89-r-model-draft/check.py | cmp - research/ordinary13-residue89-r-model-draft/receipt.json
```

The bounded read-only check pins the source and graph, validates the two
signed branch algebra identities, and tests finite size implications. It
does not execute Lean, stage artifacts or authenticate providers.
