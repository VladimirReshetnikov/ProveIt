# Independent review: forced w and X in three 13-variable graphs

The three candidate packets give sound external zero-existence maps to their respective reviewed parents under the stated local hypotheses `beta > 0` and `K0 >= 0`, conditional on those parents' unit-factor and graph facts:

* [Forced w, 86 operations, degree 99](../../research/ordinary13-natural-forced-w86/README.md).
* [C-fold forced X, 95 operations, degree 28](../../research/ordinary13-natural-cfold-forced-x95-degree28/README.md).
* [C-fold product forced X, 94 operations, degree 50](../../research/ordinary13-natural-cfold-forced-x94-degree50/README.md).

At a zero of the first graph, the reviewed arbitrary-integer residue exclusions make its four product factors `+1`. If `w=0`, then `X=0` and the first norm holds. If also `J=0`, `q=1` and `B=(1-F-alpha)K0-F<0` since `F,alpha>=1` and `K0>=0`. This makes `Z=-B>0`, contradicting the first norm with its coefficient `b=0`. Therefore `J>0`, `q>=2`, and the retained `s` shift gives `Y>=q^3`.

For the C-fold square graph, all four squares vanish at a zero. For the C-fold product graph, the reviewed all-integer unit exclusions imply the same four residual equations. If `X=0` and `J=0`, then `q=1`, `M=0`, and `Bt=(1-F-alpha)K0-F<0`, so `Z=-Bt>0` contradicts the first norm. Hence `J>0`; the same first norm gives `M=q^3*b | Z` by the integer fact `M^2 | Z^2 => M | Z`. The checked graph formula for `Z` then implies `q^3 | Y*b`; since `gcd(q,b)=gcd(b+1,b)=1`, it follows that `q^3 | Y`. The retained increment gives `Y>0`, hence `Y>=q^3`.

In all three cases, at `X=0` the checked main-norm graph has `a=Y`, `H=4Y+3`, `U=Y*q^2>0`, and `Dstar=U*a*c+H*shift`. The main norm says `Dstar^2=U^2*(1+(a^2+H)c^2)`, so the integer divisibility fact gives `U|Dstar`. Write `Dstar=U*d`, allowing signed `d`. Then `H|U*(d-a*c)`, while `(d-a*c)(d+a*c)=1+H*c^2`; multiplying by `U` shows `H|U`. Consequently `H|4U=(H-3)q^2`, and hence `H|3q^2`. But `0<3q^2<4q^3+3<=H`, a contradiction. Thus `w>0` or `X>0`, respectively. The maps increment or decrement the changed coordinate and are inverse on zeros. No positivity of gamma, sign of the main root, or bound on MC/MF is used locally.

The receipt independently checks every parent-to-child graph row, input and port order, topological order, liveness, selected arithmetic cuts, all four payload hashes, modulo-four controls for the three common restricted factors, and modular finite-difference rays of degrees 99, 28 and 50. These nonzero rays provide the lower bounds; matching upper bounds are inherited from the respective reviewed parents under affine substitution. The universal arithmetic argument above is not proved by finite tests. In particular, the compact consistency endpoint inherits the parents' stronger rank/calibration and provider qualifications. These are external checks, not Lean elaboration, an iPRA theorem, physical-file/PDF binding, or minimality results.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary13-forced-w-x-independent-aggregate/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary13-forced-w-x-independent-aggregate/result.json
```
