# Independent review: thirteen-input q-cubed unscaled first carrier

**PASS, external standard-integer mathematics.** For arbitrary integer ports
with `beta > 0`, the proposed 84-operation graph has a positive zero exactly
when its 87/36 parent does. The authenticated compact44 graph has 13 live
inputs and exact degree 56. The local comparison does not assume a sign or
bound on `K0`. It does not establish a Lean/iPRA theorem, provider replay,
PDF/JSON semantics, or a global minimum; the parent endpoint qualifications
are inherited.

For related assignments with `Y=q³s` and `r_old=r−s`, direct expansion gives
`Zold=q³Z` and `Aold=q⁶A`. From an old positive zero, the first norm gives
`q³ | Y` because `M | Zold` and `gcd(q,b)=1`; take positive `s=Y/q³` and
`r=r_old+s`. Conversely a new zero gives `b | Bt`, `t=Bt/b` and a positive
integer `tau` from `Z²=b²(1+ell(ell+k))`. The norm gives `tau<ell+k`.
Since the new `r` is positive, its displayed root equation rules out
`Bt≤0`, independent of the sign of `K0`. Thus `Bt,t≥1`. The unchanged main
norm rules out `k=2`; the independently reviewed first-Pell descent gives
`tau−ell>k/4>2XY²≥2s`. Choosing
`r_old=k(Bt−1)+t−s+(tau−ell)>0` realizes the positive root and restores a
parent zero. This is an existence map and may switch the root branch.

The checker independently reconstructs the full 87-to-84 source delta,
checks topology, all-gate/input/port liveness and the exact unscaling identity
in a sparse integer polynomial ring, and reruns the author's finite checker.
It authenticates the compressed and raw P72/P115 port bytes and computes a
different weighted affine degree ray modulo 1,000,000,009. The upper degree
bound is 56: `deg Z≤11`, the unscaled first residual is at most 22, the
strong residual at most 22, and the direct auxiliary residual at most 28;
in the main residual the `U²a²c²` terms cancel, leaving degree at most 28.
The nonzero ray coefficient supplies the matching specialized lower bound.
Finite checks do not replace the displayed unbounded witness argument.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-qcube-unscale84-independent/check.py
```

Compare stdout byte-for-byte with `result.json`; no Lean run is performed.
