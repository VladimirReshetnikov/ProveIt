# Five forced inputs: 13 naturals, 90 operations, degree 56

This is a mixed shift of the [13/82/56 positive residue-adjusted graph](../ordinary13-residue-first82/).
It leaves `J`, `X`, `f`, `y`, and `gamma` unshifted, and shifts the other
eight positive coordinates. The result has 13 natural inputs, 90 live
operations, and exact degree 56 at the authenticated compact44 ports. Its
positive-zero equivalence below is an **external standard-integer argument**;
no arbitrary-model or iPRA transfer for this graph is claimed.

## Four elementary inputs

The [13/91 predecessor packet](../ordinary13-natural-residue-forced91-degree56/)
proves that `J,X,f,y` are positive at a mixed zero when beta and K0 are
nonnegative, independently of gamma's sign. That local argument also gives
an intended-model proof outline. The parent graph and all other coordinates
are the same here, so it applies with gamma merely natural. In particular,
for the authenticated positive beta, at a zero

```
b=J*beta>0, q=1+b>=2, Y=q³*s>=q³,
X,F,alpha,s,r,eta,zeta>0.
```

Let `m=X*Y²`, `k=eta+zeta`, `ell=m*k`, `C=q-F-alpha`,
`Bt=C*(X+K0)-F`, `a=Y*(X+1)`, `H=3+4*a`, `c=eta+Y*k`,
`U=Y*q²`, and `Delta=a²+H=(a+2)²-1`. All norm residuals vanish.

## Gamma is forced in the residue-adjusted carrier

The first carrier is **this graph's** `Z=b*(ell+k+r-k*Bt)-Bt`. If `C<=0`,
then `Bt<0` since `K0>=0` and `F>0`; therefore `Z>b*(ell+k)`. Its first
norm says `Z²=b²*(1+ell*(ell+k))`, but
`(ell+k)²-(1+ell*(ell+k))=ell*k+k²-1>0`. Contradiction. Thus `C>0` and
`F+alpha<q`.

The first norm and integer square divisibility give a positive integer tau with
`tau²=1+m*(m+1)*k²`. The main norm similarly gives an integer d_abs with
`d_abs²=1+((a+2)²-1)*c²`. If `k=2`, then `eta=zeta=1`, `c=2Y+1`,
and `1<c<2*(a+2)`; the latter square lies strictly between the squares of
`(a+2)*c-1` and `(a+2)*c`. Hence `k>2`. The elementary Pell descent in the
[independently reviewed first-norm argument](../ordinary13-folded-root86-negated-positive-bt/)
uses exactly `m>=1`, `k>2` and the displayed tau equation, and yields
`k>=8m+4`. This is a standard-integer use of that argument, not an asserted
Lean or nonstandard-model theorem.

The compact tuple satisfies `0<MC<beta` and `0<MF<2*beta`; together with
`C>0`, the source theorem
[`ArithmeticAdaptiveRankWindow2011.scalar_rank_window`](../../Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean)
applies to the literal R expression and gives `R+1<q⁴`. Since `X>=1`,
`Y>=q³`, and `q>=2`, the Pell bound gives

```
k - X*Y*q > q⁴ > R+1,       c>X.
```

Suppose `gamma=0`. With `E=X*Y`, the **actual residue-adjusted graph** has

```
shift = E*q+R+1-k,
Dstar = U*(X+a*c)+H*shift.
```

The first displayed inequality makes `shift<0`. Nevertheless `Dstar>0`:
`c>Y*k` and `U*a*Y=Y²*q²*a>H`, so the positive term `U*a*c` exceeds
`H*k`, while `E*q+R+1>=0`. Square divisibility gives a positive integer
`d=Dstar/U`. Its main norm yields

```
d² - ((a+1)*c)² = (2*a+2)*c²+1 > 0,
```

so `d>(a+1)*c>X+a*c`. Therefore
`U*(d-X-a*c)=H*shift` is simultaneously positive and negative. This rules out
`gamma=0`.

Thus all five unshifted inputs are positive at every standard mixed zero under
the stated compact bounds. For a positive parent zero, use its five positive
values directly and use predecessors of the other eight inputs. Conversely,
a mixed zero supplies its five values directly and adds one to the other eight
inputs to obtain a positive parent zero. Equivalently, relative to the fully
shifted natural parent, subtract one from the five forced values in the mixed
zero and keep the other eight natural coordinates. The graph is **pointwise**
the positive-parent polynomial at this mixed substitution; equivalence to
the fully shifted natural graph is via these zero maps, not identity at the
same tuple.

## Degree, provenance, and reproduction

The checker pins the 82-row parent and verifies all 90 mixed rows, the precise
norm and gamma wiring, liveness, authenticated P72/P115 ports, and the A1
cancellation identity. Its residual degree bounds are 22, 28, 28, 22; the
complete polynomial's all-inputs-equal ray at the compact ports has degree 56
modulo 1,000,000,007 with nonzero leading coefficient 58796952. Thus degree is
exactly 56 at this tuple. These are external finite checks, not a proof of the
unbounded gamma argument.

The parent has an [independent standard-integer review](../../reviews/ordinary13-residue-first82-independent/)
using the cited calibration with documented inherited provenance. This packet
adds no Lean theorem, nonstandard-model equivalence, iPRA endpoint, or
current-2011 PDF binding. It numerically improves the separate 13/91/56 and
13/93/56 natural graphs in operation count but has a stronger standard-integer
argument for gamma; these comparisons are not global minimality claims.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-natural-residue-forced90-degree56/build.py
python3 -I -S -B research/ordinary13-natural-residue-forced90-degree56/check.py
```

The deterministic checker output is [receipt.json](receipt.json); no Lean is run.
