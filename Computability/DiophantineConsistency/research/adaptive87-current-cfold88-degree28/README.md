# Current-port C-fold candidate: 13 variables, 88 operations, degree 28

**Later status:** The calibration premise isolated below has since been
derived in the standard integers using the cited Pell and rank theorems; see
the [fact-level replay](../adaptive87-current-cfold-cal-fact-replay/README.md)
and its [independent review](../../reviews/adaptive87-current-cfold-cal-fact-replay-second-independent/README.md).
Together with the witness maps below, this gives both directions of the
ordinary positive-integer zero-existence comparison under the stated port
assumptions. The discussion below records the original conditional cut;
no all-model Lean or iPRA bridge has been checked.

This is a **conditional standard-integer candidate**, not a checked Lean, all-model, iPRA, or unconditional no-zero equivalence. The literal [graph](graph.json) changes exactly one gate of the current2011 [13/88/30 four-square parent](../adaptive87-four-square-current88-30/README.md): `root_skew = k*Bt` becomes `root_skew = k*C`. It has the same thirteen strictly positive integer inputs, four fixed ports, zero-output convention and 88 live binary operations. Its exact degree at the authenticated current2011 ports is 28. The degree improvement is unconditional as a polynomial calculation; the zero-existence comparison in one direction depends on the explicit calibration cut below.

The complete current2011 port bytes are checked by `check.py`; they satisfy `beta>=46`, `K0>=0`, `0<MC<beta`, and `0<MF<2*beta`. The checker pins the parent graph, the port binding, the earlier compact C-fold and sign-free calibration documents and reviews, and the specific source files whose fact-level statements are relevant. It does **not** establish that those source theorems have been applied to this new graph or that their provider closure is current.

## Definitions and calibration cut

For either graph write

```
b=J*beta, q=b+1, C=q−F−alpha, Bt=C*(X+K0*q)−F*q,
M=q³*b, U=Y*q², E=X*Y, m=X*Y², k=eta+zeta, ell=m*k,
c=eta+Y*k, a=E+Y, H=3+4*a, Delta=(a+2)²−1,
R=(alpha+b*(q−F))*(q²−1)+J*(MC+q*MF),
Dstar=U*(X+a*c)+H*(U*gamma+E*q+R+1−k),
I=i*c², V=f²*(T*c−R)−c, y=V+u.
```

The common strong and auxiliary factors are `I²−Delta*(f²−1)` and `y²−Delta*(f²−1)*(y²−V²)−1`. For a fixed port tuple satisfying the displayed bounds, define **Cal** to be the following statement in ordinary positive integers: whenever `C>0`, `Y=q³*s` for a positive integer s, and there exists a positive integer tau such that

```
tau²=1+ell*(ell+k),
Dstar²=U²*(1+Delta*c²),
I²=Delta*(f²−1),
y²−Delta*(f²−1)*(y²−V²)=1,
```

then `X>=q²`. All thirteen inputs are positive; the other quantities are as displayed, with signed `Dstar`, `V` and `y` allowed. This definition avoids assuming the old first carrier, the guard variable of a different graph, a positive old root coordinate, or a decoder identity.

The pinned [sign-free calibration replay](../ordinary14-shifted-guard87-calibration/README.md) and its [independent mathematical review](../../reviews/ordinary14-shifted-guard87-calibration-math-independent/README.md) explain why a closely matching fact-level statement gives `X=2^R>=q²`: `C>0` supplies the rank gap; the scalar rank-window source uses only the above inequalities on beta, MC and MF; and the exact-index and power-growth source statements take q, R and the Pell data as parameters. The actual current2011 port bounds above match the stated inequalities. **The present packet has not independently completed the new literal-to-Cal source binding**, so the application to the current tuple remains an explicit obligation, not an unconditional claim.

In particular, any completion must verify the following on the actual C-fold valuation:

1. Derive positive orientation `Dstar=U*d` for the positive main Pell root d from the common main norm and `Y=q³*s`; the `H*k` term must be dominated without an old first-coordinate or Bt-sign assumption.
2. Derive `q⁴ | R+1−k` from the oriented main equality, including the possible common factor 3 between `H` and q; use the `q⁵` scale and show the cancellation leaves q⁴.
3. Bind the same first Pell index, main Pell index, signed auxiliary magnitude and rank to `P72Exact.indices_ordinary`, then bind the resulting indices to `ArithmeticPellPowerRecovery.power_bound` and the cited projection step. The source files and theorem headers are pinned, but no new Lean application is supplied.
4. Derive `X>=q²` from the resulting `X=2^R` and rank lower bound, and verify all representation, natural subtraction and fixed-port casts at the chosen source/provider boundary.

## Conditional candidate-to-parent map

Suppose a positive candidate zero. Since its output is a sum of four integer squares, all four residuals vanish. Its first expression is

```
Znew=M*(ell+k+rho−k*C)+Y*b−q³*Bt.
```

If `C<=0`, then `Bt<0` because `X>0`, `K0>=0` and `F>0`, so `Znew>M*(ell+k)>0`. But the first norm says `Znew²=M²*(1+ell*(ell+k))`, whose positive square root is strictly less than `M*(ell+k)`: `(ell+k)²−(1+ell*(ell+k))=ell*k+k²−1>0`. Thus `C>0`.

Square divisibility gives `M|Znew`, with a positive quotient tau satisfying the first equation in Cal. Reducing the first expression modulo q³ and b, and using `gcd(q,b)=1`, gives `q³|Y` and `b|Bt`. The other three equations in Cal are precisely the remaining zero residuals. **Assuming Cal**, `X>=q²`; since `C>=1`, `F<=q−2` and `K0>=0`,

```
Bt−C = C*(X+K0*q−1)−F*q >= 2*q−1 > 0.
```

Set `r_old=rho+k*(Bt−C)>0` and retain all other inputs and ports. Direct ring expansion gives `Zold=Znew`, and the three other residuals are unchanged. Thus every candidate zero gives a parent zero under Cal. This is an existence map, not identity at the same first coordinate.

## Parent-to-candidate map

For a positive parent zero with `beta>0`, `K0>=0`, the first norm and positive root input give `Bt>0`, `q³|Y`, `b|Bt` and `tau²=1+m*(m+1)*k²`. Write `Y=q³*s` and `Bt=b*t` with positive integers s and t. The unchanged main norm excludes `k=2` by a consecutive-square gap; elementary first-Pell descent then gives `k>=8*m+4` and `tau−ell>k/4>2*s`. These are the port-parametric facts proved in the pinned [positive-Bt argument](../ordinary13-folded-root86-negated-positive-bt/README.md), with the parent's `Bt>0` derivation in the pinned [forward argument](../ordinary13-folded-root86-negated-forward/README.md). Because `Bt>0`, the displayed definition of Bt and `K0>=0` also imply `C>0`.

Set

```
rho=(C−1)*k+(tau−ell)−s+t > 0.
```

Then `Znew=M*tau`; this explicitly chooses the positive first-root branch. The other three residuals do not depend on the first coordinate and remain zero. Thus this direction gives a candidate zero without Cal, although the old and new first coordinates need not correspond directly before the root switch.

## Count and exact degree

All 88 rows, thirteen inputs and four fixed leaves are live: 48 multiplications, 22 additions and 18 subtractions. The exact ring identity for the direct coordinate substitution is checked independently of integer samples. For the degree upper bound write `Znew=M*ell+delta`, where

```
delta=M*(k+rho−k*C)+Y*b−q³*Bt.
```

At fixed ports, `deg(M*ell)<=8` and `deg(delta)<=6`, so

```
A0 = 2*(M*ell)*delta+delta²−M²*(1+ell*k)
```

has degree at most 14. The unchanged main, auxiliary and strong residuals have degree at most 13, 13 and 10 by the pinned [parent factor certificate](../adaptive-direct-ordinate86/DEGREE-87-PARENT.md). Therefore the sum of squares has degree at most 28. With every witness set to the same indeterminate and the four authenticated current ports fixed, the output has degree 28 and leading coefficient `437565601` modulo `1000000007`, proving exact specialized degree 28.

Reproduce from the DiophantineConsistency directory:

```sh
python3 research/adaptive87-current-cfold88-degree28/check.py > /tmp/adaptive87-current-cfold-current.json
cmp research/adaptive87-current-cfold88-degree28/result.json /tmp/adaptive87-current-cfold-current.json
```

The finite wiring controls and source-header pins do not prove Cal. No Lean/build/staging was performed, and no provider, historical evidence, or existing display was modified.
