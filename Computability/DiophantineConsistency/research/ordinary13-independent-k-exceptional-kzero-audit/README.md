# Fixed compact independent-k graph: first-factor gap over the integers

For the exact [84-row independent-k candidate](../ordinary13-eta-zeta84-independent-k-candidate/candidate.json), a natural zero at the **fixed symbolic compact tuple** must satisfy `F+alpha<q`, in ordinary integer arithmetic. This is stronger than the preceding first-factor-only split: it rules out its exceptional k=0, gap-failure branch using the actual main residual and fixed-port bounds. It does **not** show that k=0 is impossible in the remaining positive-gap branch, that `k≥eta`, or that the child has the parent's unrestricted zero set. No Lean or iPRA theorem is claimed.

The checker verifies exact expression syntax of all four factors and exhausts their residue patterns modulo four. The output is their product minus one; at an integer zero all four factors are integer units, and none can be −1 modulo four. Thus all four are +1, in particular the first and main residuals vanish. This is a standard-integer argument; the separate model-internal unit extraction and provider binding remain unelaborated.

Write `b=J*beta`, `q=1+b`, `F=n_F+1`, `alpha=n_alpha+1`, `d=X+K0`, `C=q-F-alpha` and `B=C*d-F`. The first residual already excludes `J=0`: then q=1, `C≤−1`, `B<0`, b=0 and its root `Z=−B>0`. Hence J>0 and b>0 at a putative zero. The separate [first-factor audit](../ordinary13-independent-k-first-factor-audit/) proves `C>0` whenever `k≥1`; for `k=0`, failure of that gap implies the exceptional branch `r=0, B=-b`.

In that branch put signed `qF=q-F`. Its exact first-root equation yields

```
qF*(d+1)=alpha*d+1.
```

Since d≥K0≥7, this gives `qF≥1` and `alpha=qF+t` for a natural t with `d*t=qF-1`. The shifted F is positive, so `qF≤q-1=beta*J`, and consequently `7t≤beta*J-1`.

The actual compact low-mask recipe has `0≤MC<beta` and `6MC>5beta`. To see the second bound without expanding the constants, set `B0=2^67` and `L=8807`. The top low-mask digit, at 8806, is `B0-1`: it is neither the special index nor in the pinned finite support. Hence `MC≥(B0-1)*B0^(L-1)`, while `beta=B0^L-1`, and

```
6MC-5beta ≥ (B0-6)*B0^(L-1)+5 > 0.
```

The strict upper bound follows from the same digit recipe because the special digit is below `B0-1`. The fixed `K0=paramKernel rho` has a nonnegative `rho^30` summand with `rho=2^67`, so K0≥7. These fixed-port facts are specific to the symbolic tuple; this argument is not asserted for arbitrary compact K.

The exact graph main root is `U*(X+a*c)+H*(U*gamma+R+1-k)`, with `U=Y*q²` and `H=3+4a≡3 (mod q)`. Its norm and positive q imply `q | Dstar`, hence `q | 3*(R+1)`. This uses standard integer square divisibility; it does **not** cancel 3 modulo q, which may be divisible by 3 when J is unrestricted.

The pinned rank polynomial and exceptional relation give

```
R+1 ≡ u = J*MC+1-t  (mod q).
```

Since `7t<beta*J` and `6MC>5beta`, we have `3t<J*(3MC-2beta)` and hence `3u>2q`. Since `MC<beta` and J≥1, `u<q`, so `3u<3q`. Therefore `2q<3u<3q`, contradicting `q | 3u`. This proves the claimed gap for standard natural tuples at the fixed symbolic ports, conditional only on the displayed graph and exact fixed recipes.

For the intended arbitrary IΣ₁ models, each step still needs an authenticated model construction and actual Lean elaboration: graph-unit factorization, positive J, signed/natural divisibility and order, fixed K and mask bounds, and provider/axiom closure. The cited `ModelRelationCombining.sq_dvd_sq` is a potentially relevant source interface, not a checked application here. The checker verifies the graph factor syntax and all finite mod-four cases, the polynomial rank-residue identity, the precise top-digit source recipe and bounded inequality controls. It does not execute the full proof in Lean or establish an iPRA endpoint.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-independent-k-exceptional-kzero-audit/check.py | cmp - research/ordinary13-independent-k-exceptional-kzero-audit/receipt.json
```
