# Signed-port full zero after deleting the i shift

Deleting the single operation `i=n_i+1` from the [eta/zeta-natural 85-row graph](../ordinary13-eta85-zeta-zero-boundary-audit/probe.json) and using `n_i` directly produces the pinned 84-row probe. It has a complete natural-input zero with `n_i=0` for every integer K0 and MF at ports `(-1,K0,2,MF)`. The parent output at the **same** inputs and ports is 1. Thus arbitrary signed ports do not force the unshifted i coordinate positive.

The input tuple, in the graph's original order, is

```
(n_J,n_F,n_alpha,n_f,n_i,n_T,n_w,n_s,n_r,n_eta,n_zeta,n_y,n_gamma)
= (1,0,0,1,0,0,0,0,0,1,0,1,0).
```

The probe has `q=Y=U=0`, `eta=c=k=1`, `R=0` and first root `Z=-1`. Its first and main residuals vanish. Since `f=1` and `i=0`, its strong residual is zero and its auxiliary factor is one. All four product factors are +1, so the output is zero. The parent instead has shifted `i=1`, strong residual 1 and output 1. K0 and MF cancel in these identities; in particular they may be chosen natural.

This result uses **beta=-1**, which is not the compact tuple's positive beta. It does not exhibit a compact-port zero, prove or disprove an existential witness map that changes coordinates, or establish a smaller consistency equation or an iPRA theorem. The modified graph is a boundary probe, not a proposed equivalent endpoint.

The checker derives the child by the exact one-row deletion, verifies the i field's uses, and evaluates every graph row for both child and parent in the exact ring `Z[K0,MF]`. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-eta-zeta84-unshift-i-signed-full-zero/check.py | cmp - research/ordinary13-eta-zeta84-unshift-i-signed-full-zero/receipt.json
```
