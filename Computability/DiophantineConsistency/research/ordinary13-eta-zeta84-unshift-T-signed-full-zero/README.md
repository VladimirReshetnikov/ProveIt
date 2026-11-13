# Signed-port full zero after deleting the T shift

Deleting `T=n_T+1` from the pinned [eta/zeta-natural 85-row graph](../ordinary13-eta85-zeta-zero-boundary-audit/probe.json) and using `n_T` directly gives this 84-row probe. At ports `(-1,K0,2,MF)`, for arbitrary integers K0 and MF, it has a complete natural-input zero with `n_T=0`:

```
(n_J,n_F,n_alpha,n_f,n_i,n_T,n_w,n_s,n_r,n_eta,n_zeta,n_y,n_gamma)
= (1,0,0,2,2,0,0,0,0,1,0,1,0).
```

The probe's actual fields satisfy `q=Y=U=0`, `c=k=1`, `R=0`, `Z=-1`, and its first, main and strong residuals vanish. Its auxiliary ordinate is `V=-1`, its auxiliary factor is +1 and its complete output is zero. At the same tuple and ports the shifted parent has `T=1`, `V=3`, auxiliary factor 73 and output 72.

The example uses **beta=-1**, outside the positive compact tuple. It does not establish a compact-port zero, disprove an existential witness map that changes coordinates, or provide a smaller consistency equation or iPRA theorem. K0 and MF may be chosen natural, but beta is necessarily negative in this example.

The checker constructs the exact one-row deletion and evaluates every row of both graphs over `Z[K0,MF]`; no numerical sampling is used for the stated identities. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-eta-zeta84-unshift-T-signed-full-zero/check.py | cmp - research/ordinary13-eta-zeta84-unshift-T-signed-full-zero/receipt.json
```
