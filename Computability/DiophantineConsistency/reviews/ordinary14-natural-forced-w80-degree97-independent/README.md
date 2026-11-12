# Independent review: forced-w shifted-root natural 80-operation graph

The [candidate](../../research/ordinary14-natural-forced-w80-degree97/README.md) has the stated external zero-existence equivalence to its 81-operation shifted-root parent under `beta>0` and `K0>=0`, with arbitrary integer MC and MF, conditional on the reviewed parent results. It has 14 natural inputs, 80 live binary operations, and exact specialized degree 97. The operation count is an explicit upper bound, not a minimality claim or a Lean/iPRA theorem.

The independent checker verifies every graph row after deleting the single w increment, all input/port/gate liveness and the precise shifted first-factor, guard and main-factor shapes. In particular, when `w=0`, `X=ell=0` and `F0=t²`; integer-unit extraction therefore gives `F0=1` even when the new root coordinate is initially allowed to be zero. The three other restricted factors cannot be `-1` modulo four, which forces the guard to `+1`. The unchanged J=0 branch then gives guard `C*K0-n_F<=0`, a contradiction, hence `q>=2`.

The remainder is the independently reviewed [79-operation forced-w argument](../ordinary14-natural-forced-w79-independent/README.md): `Y=q³*s>=q³`, `a=Y`, `H=4Y+3` and `U=Yq²`; the main norm implies `H | U`, then `H | 3q²`, impossible since `0<3q²<H`. It uses neither positivity of the shifted root nor a sign choice for the main root. Thus `w>0` and the explicit affine predecessor/increment maps establish both zero-existence directions. The inherited 81-to-consistency chain retains its stronger port and rank assumptions. These are mathematical arguments, not Lean checks.

The checker independently authenticates the fixed P72/P115 raw and gzip port bytes, exhausts relevant residue controls, and computes the `n_t=2x`, other inputs `x` ray by finite differences modulo 1,000,000,007; its nonzero degree-97 coefficient is `979034495`. The degree upper bound is inherited from the parent and is not rederived in this packet. No claim is made about iPRA derivability, provider closure, physical PDF binding, or global optimality.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural-forced-w80-degree97-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural-forced-w80-degree97-independent/result.json
```
