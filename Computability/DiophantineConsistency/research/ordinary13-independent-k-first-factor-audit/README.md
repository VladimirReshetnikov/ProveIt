# Independent-k first factor: gap and k=0 exception

This is an arithmetic/source audit of the [84-row independent-k candidate](../ordinary13-eta-zeta84-independent-k-candidate/), not a full-zero proof or a Lean theorem. Write `b=J*beta>0`, `q=1+b`, `F=n_F+1>0`, `alpha=n_alpha+1>0`, `d=X+K0≥0`, `C=q-F-alpha`, `B=C*d-F`, `ell=X*Y²*k`, and `r=n_r≥0`. In the graph's signed integer expressions, the first root and residual are exactly

```
Z = b*(ell+k+r-k*B)-B,
A0 = Z²-b²*(1+ell*(ell+k)).
```

Assume **separately** that this first residual vanishes. For `k≥1`, it forces `F+alpha<q`, without assuming `eta≤k`: otherwise `C≤0`, so `B<0` and `Z>b*(ell+k)>0`. But `(ell+k)²≥1+ell*(ell+k)`, since the difference is `ell*k+k²-1≥0`. This contradicts `A0=0`.

At `k=0`, the norm becomes `(b*r-B)²=b²`, so `B=b*(r-1)` or `B=b*(r+1)`. Either `B≥0`, which forces the same gap, or the sole negative case is `r=0, B=-b`. In that exceptional case, writing signed `qF=q-F` gives the further exact relation

```
qF*(d+1)=alpha*d+1.
```

This split is valid in ordinary integer arithmetic and is a candidate for ordered-model formalization. It relies only on the first residual, not on an established graph-zero-to-unit extraction for this new literal.

The exception is real at the first factor, including the compact ports: for arbitrary `beta≥1` and natural `K0,MC,MF`, choose `J=1`, `F=beta`, `alpha=1`, `w=k=r=0` and any natural eta. Then `q=beta+1`, `C=0`, `B=-b`, `Z=b` and `A0=0`. The checker verifies these as exact symbolic identities in the candidate's actual rows. This is a **partial-factor assignment**, not a graph zero.

The main factor rules out completing that particular family when `1≤eta≤q`. Indeed, with `a=Y>0`, `U=a*q²`, `H=3+4a`, and natural MC,MF, its actual signed rank and main root are

```
R=q*(q²-1)+MC+q*MF,
Dstar=U*a*eta+H*(U*gamma+R+1).
```

For `q≥2`, `2*(q²-1)≥q²`, hence `H*(R+1)>2*U*q≥2*U*eta`. Thus `Dstar>U*(a+2)*eta>0`. Since `Delta=(a+2)²-1` and `eta≥1`, this makes `Dstar²>U²*(1+Delta*eta²)`, contradicting the main residual. This excludes only the displayed partial family and eta range. Other k=0 exceptions, eta>q, the strong and auxiliary equations, all compact full zeros and the unrestricted zero map remain open.

The checker verifies the pinned row wiring and exact exceptional first/main expressions in an integer polynomial ring, with no huge fixed constants materialized. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-independent-k-first-factor-audit/check.py | cmp - research/ordinary13-independent-k-first-factor-audit/receipt.json
```

No Lean build, provider selection or iPRA endpoint is claimed.
