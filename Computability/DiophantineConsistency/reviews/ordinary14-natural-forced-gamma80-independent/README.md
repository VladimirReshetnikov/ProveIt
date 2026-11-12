# Independent review: 14-natural-input forced gamma, 80 operations

The [candidate](../../research/ordinary14-natural-forced-gamma80/README.md) has the stated external natural-zero equivalence to its [81-operation parent](../../research/ordinary14-natural-forcedj81/README.md), conditional on the cited negative-Pell exclusion, rank-window theorem and positive-Pell descent under `beta>=46`, `K0>0`, `0<MC<beta` and `0<MF<2*beta`. It has 14 natural inputs and exact specialized degree 107 at the authenticated compact ports. This is not a Lean or iPRA theorem, physical-file/PDF binding, provider replay or minimum claim.

The receipt independently verifies the complete one-gate edit: delete `gamma=n_gamma+1` and redirect its consumer to `n_gamma`. The resulting affine input substitution is an exact integer-polynomial identity. All 80 gates, inputs and ports remain live. A parent zero maps to the new graph by incrementing gamma; the reverse map takes a predecessor once gamma positivity is established.

At a new zero the five integer factors multiply to one. The reviewed strict-K0 guard argument forces `J>0` without using gamma positivity. Then `b=J*beta>0`, `q=b+1>=2`, `X=q*w>=q`, `Y=q³*s>=q³`, `m=X*Y²>=q^7>=2`, `k=eta+zeta>=2`, and `ell=m*k`. The first factor is `r²−ell*(ell+k)` for natural `r`. Its positive-unit equation forces `r>0`. In either case the reviewed negative-Pell exclusion rules out first factor `−1` for `m>=2`; the main, auxiliary and strong factors exclude `−1` modulo four for arbitrary integer inputs. The receipt exhausts those three residue cases. All four restricted factors and then the guard are therefore +1. The graph identity `qF=b−n_F=q−(n_F+1)` identifies `F=n_F+1`; guard=1 gives `C*(X+K0)−F=b*n_h>=0`. Since `F>0` and `X+K0>0`, this forces `C=q−F−alpha>0` and `F+alpha<q`.

The rank-window source assumes positive `beta,J,F,alpha`, the two upper port bounds, `q=beta*J+1`, and `F+alpha<q`; those hold. Its rank expression matches this graph after natural-subtraction cancellation and commutation, giving `R+q³+q+1<=q⁴`, so `R+1<q⁴`; the port and gap hypotheses also give `R>=0`. The main unit gives `Dstar²=U²*(1+Delta*c²)`, and `U>0` implies an integer `d_abs=|Dstar|/U`. If `k=2`, then `eta=zeta=1`, `c=2Y+1`, and `1<c<2(a+2)` since `a=XY+Y>=2Y`. The norm lies strictly between `((a+2)c−1)²` and `((a+2)c)²`, impossible. Thus `k>2`.

The first positive unit gives the positive-Pell equation `tau²−m(m+1)k²=1`, with `tau=r` in the unshifted graph and `tau=ell+t` in the shifted graph. The reviewed descent uses only `m>=1`, `k>2` and that equation: its smaller positive solution has `k'>=2` and `tau'>=2m+1`, so inversion yields `k>=8m+4`. The receipt verifies the Pell-transform identity and main-norm square-gap identities as exact sparse polynomials; it does not replace the unbounded descent. Since `m>=q^7`, this gives `k>=8q^7+4>q⁴>R+1`, and `c=eta+Y*k>X`.

At `gamma=0`, `Dstar=U*(X+a*c)+H*(R+1−k)`. The graph gives `c>Y*k`, `U*a*Y=Y²*q²*a>H=3+4a` because `Y²*q²>=q^8>=256` and `a>=1`. With `R>=0`, this shows `Dstar>0`. Its norm and `U>0` give positive integer `d=Dstar/U`; the exact square identity `d²−((a+1)c)²=(2a+2)c²+1>0` implies `d>(a+1)c>X+a*c`. Therefore `U*(d−X−a*c)>0`, while the same main expression equals `H*(R+1−k)<0`, contradiction. This establishes the gamma predecessor without presupposing gamma positivity.

The receipt authenticates the P72/P115 bytes and checks the stated port bounds. Its 107th finite difference on the ray with all inputs equal to x gives nonzero leading coefficient 419359493 modulo 1,000,000,007. Combined with the independently reviewed parent's degree upper bound and affine substitution, this gives exact degree 107. Finite checks do not replace the unbounded rank/Pell arguments or establish the inherited endpoint.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural-forced-gamma80-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural-forced-gamma80-independent/result.json
```
