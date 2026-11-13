# Independent-k: an actual-rank scalar slice and its first-root obstruction

At the fixed symbolic compact tuple, the exact independent-k graph rank and both **natural** Pell norms can be matched with `eta>k` and the same index relation `R=2n-1`. However, the actual first signed root rules out the particular coordinate slice used here. This is not a full graph zero, nor a proof of `k≥eta` for other slices.

Let `rho=2^67`, `beta=rho^8807-1`, `q=beta+1`, `K0=paramKernel rho`, and use the exact compact `MC=lowNat`, `MF=beta+highNat`. Set graph coordinates `J=1, F=1, alpha=2, w=1, s=1`; their natural inputs are respectively `1,0,1,1,0`. Then `X=q`, `Y=q³`, and the **actual graph rank** is

```
R=(beta²+2)*(q²-1)+MC+q*MF.
```

Here beta is odd, q is even, and MC is even (its least base-rho digit is `rho-2`); thus R is odd. Its size gives `n=(R+1)/2≥14`. The compact digit bounds `MC<beta` and `MF<2beta` yield

```
R ≤ q⁴-2q³+4q²-5,
q⁴-(R+q³+q+1) ≥ (q-4)*(q²-1) ≥ 0.
```

The graph's `F+alpha=3<q`, so this is the same scalar rank-window shape used by the early-index arguments.

Put `M=X*Y²`, take `k=2*ycoord(n,2M-1)`, and take the main coordinate `c=ycoord(R, X*Y+Y)`. With `eta=c-Y*k`, the exact Pell-growth proof in the [shared-index boundary audit](../ordinary13-independent-k-shared-index-norm-audit/) applies because q≥24 and n≥14: it gives `eta>k`. The two natural Pell norms, `k=2n+4M*sFirst`, `R=2n-1`, `(2n) mod q⁴=R+1`, and the scalar window all hold. No gigantic fixed number or Pell ordinate is materialized.

The actual signed first root is an additional, decisive condition. Let `B=(q-F-alpha)*(X+K0)-F` and `b=J*beta=beta`. If its squared first residual were zero, `b² | Z²` would imply `b | Z`, and the actual root expression `Z=b*(ell+k+r-k*B)-B` would give `b | B`. On this slice,

```
B=(beta-2)*(beta+1+K0)-1
 = beta*(beta+K0-1) - (2*K0+3).
```

Thus the first norm would require `beta | (2*K0+3)`. The fixed kernel recipe rules this out. Let `K′=K0-rho^42*beta`. The `rho^8807*rho^42` summand becomes `rho^42*(beta+1)`, so `K′=rho^42` plus the other nonnegative summands. Every remaining exponent is at most 5495; each selector is at most `1+2^51`, each copy coefficient at most `2^50`, and there are 943 and 41 terms with two powers each. Therefore

```
0<K′ ≤ T*rho^5495 < rho^5496,
T=5+2*943*(1+2^51)+2*41*2^50 < rho.
```

Since `rho^8807≥8*rho^5496`, `0<2K′+3<beta`. But `2K0+3=2*rho^42*beta+(2K′+3)`, so it is not divisible by beta. This establishes, over standard integers, that **no assignment on this coordinate slice can make even A0 vanish**. It does not establish an obstruction for other F, alpha, w or J, or an arbitrary-model proof.

The checker pins the candidate and compact recipes, verifies the exact rank-cap and carrier identities as integer polynomials, and verifies the finite coefficient bound without expanding rho powers. The source's retained `low_even` and compact tuple declarations are pinned; the mathematical digit argument above supplies the standard-integer parity/bounds, not a new Lean validation. The two-norm growth proof and the root obstruction do not settle the full zero-map or iPRA goal.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-independent-k-actual-rank-boundary-audit/check.py | cmp - research/ordinary13-independent-k-actual-rank-boundary-audit/receipt.json
```
