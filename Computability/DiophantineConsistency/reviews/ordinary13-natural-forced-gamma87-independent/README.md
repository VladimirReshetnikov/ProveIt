# Independent review: forced gamma for the 13-natural graph

The [87-operation candidate](../../research/ordinary13-natural-forced-gamma87/README.md) has the stated natural-zero equivalence to its 88-operation parent under `beta>=46`, `K0>=0`, `0<MC<beta`, and `0<MF<2*beta`, conditional on the cited rank-window theorem and the independently reviewed all-integer unit and Pell-descent arguments. Its 13-input specialized degree is exactly 99 at the authenticated compact ports. This is external standard-integer mathematics, not a Lean/iPRA result, PDF or file-binding theorem, provider replay, or minimality claim.

The independent receipt verifies the exact one-node graph edit: remove `gamma=n_gamma+1` and replace its consumer by `n_gamma`. Thus the new polynomial at `gamma=g` is the parent polynomial at `n_gamma=g−1` over arbitrary signed inputs and ports. It also checks topology and liveness and the graph rows for all factors used below. The parent unit exclusions apply to arbitrary integers, so an 87 zero has all four factors equal to one even if `gamma=0`. The earlier forced-J argument uses the first residual, positive `F,alpha,w` and `K0>=0`, but not gamma positivity, so `J>0` here as well.

Let `b=J*beta`, `q=b+1`, `X=q*w`, `Y=q^3*s`, `m=X*Y²`, `k=eta+zeta`, `ell=m*k`, and `B=(q−F−alpha)*(X+K0)−F`. All shifted variables in these expressions are positive, giving `q>=2`, `X>=q`, `Y>=q^3`, `m>=q^7` and `k>=2`. If `B<=0`, the first expression `Z=b*(ell+k+r−k*B)−B` is at least `b*(ell+k)` even for `r=0`; its norm requires `Z²=b²*(1+ell*(ell+k))`, contradicting `(ell+k)²−(1+ell*(ell+k))=ell*k+k²−1>0`. Hence `B>0`, which forces `C=q−F−alpha>0` and `F+alpha<q`.

The cited `scalar_rank_window` source assumes positive `beta,J,F,alpha`, `MC<beta`, `MF<2*beta`, `q=beta*J+1` and `F+alpha<q`; these hold here. Its rank expression is the graph's `R` after commutation and the justified natural subtractions `q−1=b` and `q−F>0`. Its conclusion gives `R+q^3+q+1<=q^4`, hence `R+1<q^4`; the asserted port bounds and `C>0` also make `R>=0`. The theorem is used as a cited source-level mathematical input; this review does not replay its Lean provider.

From the main norm and `U>0`, square divisibility gives an integer `d_abs` with `d_abs²=1+Delta*c²`. If `k=2`, then `eta=zeta=1`, so `c=2Y+1` and `1<c<2(a+2)` because `a=XY+Y>=2Y`. The norm quantity lies strictly between `((a+2)c−1)²` and `((a+2)c)²`, impossible. Thus `k>2`. From the first norm, square divisibility gives natural `tau` with `tau²−m(m+1)k²=1`. The cited descent applies without any gamma or present-root sign assumption: `tau'=(2m+1)tau−2m(m+1)k` and `k'=(2m+1)k−2tau` are positive, `k'<k`, and satisfy the same Pell equation. `k'` cannot be 1 by the strict gap between consecutive squares, so `k'>=2` and `tau'>=2m+1`; inversion yields `k=(2m+1)k'+2tau'>=8m+4`. Consequently `k>=8q^7+4>q^4>R+1`, and `c=eta+Y*k>X`.

If `gamma=0`, the graph gives `Dstar=U*(X+a*c)+H*(R+1−k)`. Here `c>Y*k` and `U*a*Y=Y²*q²*a>H=3+4a`: indeed `Y²*q²>=q^8>=256` and `a>=1`. Since `R>=0`, it follows that `Dstar>0`. Put `d=Dstar/U>0`. The exact identity `d²−((a+1)c)²=(2a+2)c²+1>0` gives `d>(a+1)c>X+a*c`. Therefore the same main-expression equality says both `U*(d−X−a*c)>0` and `H*(R+1−k)<0`, a contradiction. This forces gamma positive and supplies its natural predecessor; incrementing the parent coordinate gives the reverse map.

The receipt verifies the relevant square-gap and Pell-transform identities as exact sparse multivariate polynomials, authenticates all four P72/P115 payloads and port bounds, and obtains the 99th finite-difference leading coefficient 663418019 modulo 1,000,000,007. The matching degree upper bound is inherited under affine substitution from the reviewed parent. Finite controls do not replace the unbounded inequalities, rank theorem, descent or inherited endpoint proof.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary13-natural-forced-gamma87-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary13-natural-forced-gamma87-independent/result.json
```
