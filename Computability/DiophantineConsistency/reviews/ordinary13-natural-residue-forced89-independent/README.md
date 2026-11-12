# Independent review of the 13/89 mixed graph

The pinned 89-operation graph has 13 natural inputs and exactly the parent 82-operation polynomial at the documented mixed substitution. Six coordinates are unshifted; the other seven receive one. The checker reconstructs every row, checks liveness, pins and reads the compact P72/P115 ports, verifies `K0+1 <= (beta+1)^2`, and independently proves exact degree 56 using a second modular ray and a residual degree bound. The candidate's own receipt also reproduces. These are finite checks, not Lean elaboration or formal PDF semantics.

For the newly unshifted `r`, let `b=J*beta>0`, `q=1+b`, `m=X*Y^2`, `k=eta+zeta>=2`, `ell=m*k`, `P=(q-F-alpha)*(X+K0)-F`, and `Z=b*(ell+k+r-k*P)-P`. The graph's first norm yields `Z²=b²*(1+ell*(ell+k))`. If `P<=0`, its left side is too large because `Z>=b*(ell+k)` and the squared difference is `ell*k+k²-1>0`. Thus `P>0`, giving `0<C=q-F-alpha<q`. Square divisibility and the literal Z identity give `b|P`; writing `P=b*t` gives `1<=t<=P`. The same norm gives the signed square root `tau>ell`, and the represented bound `K0+1<=q²`, together with `X>=1` and `Y>=q³`, gives `P<m`.

At `r=0`, the two signed branches are `0=k*(P-1)+t-ell ± tau`. The plus branch is positive. For the minus branch, `k*(P-1)<ell` and `t<=P<m<=ell`, so `k*(P-1)+t<2*ell<ell+tau`; it is negative. This corrects the earlier proposed stronger bound `k*(P-1)+t<=k*P`, which does not follow from the hypotheses: `k=2`, `P=t=99`, `m=100` is an arithmetic counterexample. It is not asserted to be a graph zero. The deterministic finite controls exercise the corrected bound but do not replace its order argument.

The local forcing argument is intended for discretely ordered IΣ₁ models with positive represented beta, represented natural K0, and the represented inequality `K0+1<=q²`; it uses signed magnitude, square divisibility, and natural quotient reflection. The verified compact byte inequality is an external calculation and does not itself supply the represented inequality in Lean. The first four forced coordinates use the previous 91 argument. The gamma forcing inherited from the 90 graph is **standard-integer only**, and its first-norm contradiction remains valid with natural `r`. Thus the complete 89-to-positive82 zero-map argument currently has the same standard-integer boundary. The model gamma bridge, represented compact-port bound, positive82 calibration in arbitrary models, provider build and iPRA endpoint remain open.

Reproduce from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-natural-residue-forced89-independent/check.py | cmp - reviews/ordinary13-natural-residue-forced89-independent/result.json
python3 -I -S -B research/ordinary13-natural-residue-forced89-degree56/check.py | cmp - research/ordinary13-natural-residue-forced89-degree56/receipt.json
```
