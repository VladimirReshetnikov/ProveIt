# Independent review: forced gamma in the natural C-fold graph

The [candidate](../../research/ordinary13-natural-cfold-forced-gamma96-degree28/README.md) has the stated external natural-zero equivalence to its [97-operation parent](../../research/ordinary13-natural-cfold97-degree28/README.md), conditional on the cited rank-window theorem and positive-Pell descent and under `beta>=46`, `K0>=0`, `0<MC<beta`, and `0<MF<2*beta`. Its 13-input graph has 96 live operations and exact specialized degree 28 at the authenticated compact ports. The inherited connection to the earlier positive C-fold graph also retains its sign-free calibration assumptions. This is not a Lean/iPRA theorem, physical-file/PDF binding, provider replay, or minimality claim.

The complete graph edit removes `gamma=n_gamma+1` and redirects its consumer to `n_gamma`, giving exact polynomial equality under the affine coordinate change. All 96 gates, 13 inputs and four ports remain live. A parent zero maps forward by incrementing gamma; the reverse map takes a predecessor after gamma positivity is proved. The output is a sum of four integer squares, so a zero makes all four residuals vanish.

The shifted `F,alpha,X,Y,eta,zeta` are positive. The parent's J-positivity argument applies without gamma positivity: if `J=0`, then `b=0`, `q=1`, `C=1−F−alpha<0` and `Bt=C*(X+K0*q)−F*q<0`, while `M=q³*b=0` and `Z=−Bt>0`, contradicting the first norm. Likewise, `f=0` would give `Q=−Delta<0` while the strong residual gives `Q=I²>=0`. Thus `J,f>0`, `q=b+1>=2`, `M=q³*b>0`, `U=Y*q²>0`, `k=eta+zeta>=2` and `m=X*Y²>=1`. If `C<=0`, then `Bt<0` and `Z>M*(ell+k)` even when the direct natural root coordinate is zero, whereas the norm and `ell>0`, `k>=2` imply `Z²<M²*(ell+k)²`; contradiction. Hence `C>0` and `F+alpha<q`.

The first norm yields `M|Z` by integer square divisibility. In `Z=M*(ell+k+r−k*C)+Y*b−q³*Bt`, reduction modulo `q³` gives `q³|Y*b`; since `gcd(q³,b)=1`, this gives `q³|Y`, so the positive `Y` satisfies `Y>=q³`. The cited rank theorem's positive-input, upper-port, `q=beta*J+1` and `F+alpha<q` premises hold, and its rank expression equals the graph's `R` after natural-subtraction cancellation. It yields `R+1<q⁴`; the port and gap conditions also give `R>=0`.

The main norm gives `U|Dstar` and an integer absolute quotient with square `1+Delta*c²`. If `k=2`, then `eta=zeta=1`, `c=2Y+1` and `1<c<2(a+2)` because `a=XY+Y>=2Y`; the main norm lies strictly between consecutive squares, contradiction. Hence `k>2`. The first norm yields `tau²−m(m+1)k²=1`, and the cited positive-Pell descent yields `k>=8m+4`. With `E=X*Y`, `X>=1` and `Y>=q³`,

```
k−E*q >= X*Y*(8Y−q)+4 >= 8q^6−q^4+4 > q^4 > R+1.
```

At `gamma=0`, the exact graph expression has the **additional** `E*q` term: `Dstar=U*(X+a*c)+H*(E*q+R+1−k)`. It is positive because `c>Y*k`, `R>=0`, `E*q>=0`, and `U*a*Y=Y²*q²*a>H=3+4a` (use `Y²*q²>=q^8>=256` and `a>=1`). Set `d=Dstar/U>0`; the main norm implies `d²−((a+1)c)²=(2a+2)c²+1>0`, so `d>(a+1)c>X+a*c`. Yet the displayed expression says `U*(d−X−a*c)=H*(E*q+R+1−k)<0`, contradiction. Gamma is therefore positive and has a natural predecessor. The receipt verifies the square gaps and Pell-transform identities as formal sparse polynomials; the unbounded descent, divisibility and rank theorem are mathematical premises, not consequences of finite controls.

The receipt authenticates all four P72/P115 port payloads and checks the stated bounds. The 28th finite difference of the all-inputs-equal ray modulo 1,000,000,007 has nonzero leading coefficient 59132194; the matching upper bound is inherited from the reviewed parent under affine substitution. No Lean elaboration or iPRA endpoint is established.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary13-natural-cfold-forced-gamma96-degree28-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary13-natural-cfold-forced-gamma96-degree28-independent/result.json
```
