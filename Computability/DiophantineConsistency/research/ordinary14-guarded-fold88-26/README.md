# Quotient-guarded 14-positive-variable, 88-operation, degree-26 graph

This packet proposes a 14-positive-input equation with **88 live arithmetic
operations and exact degree 26** at the authenticated compact44 ports. Under
the explicit parameter bound below, its positive-zero existence is equivalent
to that of the reviewed 13-input 88/30 free-J parent. The proof and finite
graph/degree checks are submitted for independent review. This is a separate
equation from the displayed PDF and does not add a Lean or iPRA theorem,
JSON/PDF interpretation, foundational replay, or global minimality claim.

Relative to the signed-fold 86/26 graph, replace its first expression

```
Z=M*(ell+k−sigma)+Y*b−q³*Bt
```

by `Z=M*(ell+k−sigma_prime)+Y*b`, and add one positive input `t` with a
squared guard `(Bt−b*t)²`. The old four-square output plus this guard square
is the new equation. Here `b=J*beta`, `q=b+1`, and `M=q³*b`. On `Bt=b*t`,
the first expressions agree under the shift `sigma_prime=sigma+t`.

## Fixed-port hypotheses

Assume

```
beta>0, 0<=K0<(beta+1)².
```

The checker authenticates the P72/P115 compact44 port bytes and verifies
these hypotheses. Every positive J then gives `b>=1`, `q>=2` and `K0<q²`.
The source endpoint and its ancestry limitations are inherited from the
88/30 parent; this packet proves an external positive-zero comparison.

## From the 88/30 parent to this graph

The independently reviewed 89/26 guarded construction in
`../ordinary14-guarded-fold89-26/` turns any parent zero into a positive
signed-fold zero with `Bt>0`, preserving the other twelve inputs. The
reviewed signed first norm gives `b|Bt`, so `t=Bt/b` is a positive integer.
Set `sigma_prime=sigma+t`, which is positive. The displayed equality of Z
preserves the first residual; the other three residuals are unchanged and
`Bt−b*t=0`. Thus every positive parent zero gives a positive quotient-guarded
zero.

## From this graph to the 88/30 parent

Take a positive quotient-guarded zero. Its output is a sum of five integer
squares, so all four signed-fold residuals and the guard vanish. The guard
implies `Bt=b*t>0` and `b|Bt`. The first norm and `M|Z` imply `q³|Y`:
indeed, `M=q³*b` and `Z=M*(ell+k−sigma_prime)+Y*b`. Thus put

```
s=Y/q³ >= 1, m=X*Y², k=eta+zeta, ell=m*k,
tau=|Z|/M > 0, tau²=1+m*(m+1)*k².
```

The A1-based exclusion of `k=2` and the first-Pell descent in the
independently reviewed `../ordinary13-folded-root86-negated-positive-bt/`
apply here: they use these two norms and the displayed divisibilities, and
give `k>=8*X*Y²+4`. In particular `k>2` and

```
tau < ell+k/2,
Bt < b*(X+K0*q) < q*X+q^4 < 2*X*q^6 < k/4,
t=Bt/b <= Bt < k/4.
```

For the bound on Bt use `C=q−F−alpha<=b−1`, while the last comparison uses
`Y>=q³`, `q>=2`, and `X>=1`. The norm equation and first expression give

```
sigma_prime=ell+k+s±tau > k/2+s > t.
```

Hence `sigma=sigma_prime−t` is a positive integer. Keeping all other inputs
fixed and using `Bt=b*t` makes the original signed-fold expression exactly
the new Z. All signed-fold residuals vanish with `Bt>0`. The independently
reviewed positive-Bt repair then supplies a positive first-root coordinate
for the 88/30 parent. Thus both positive-zero existence implications hold.

## Gate count and degree

The checker reconstructs the graph from the 86-gate signed-fold source:
renaming the old pre-subtraction sum as Z deletes `q³*Bt` and one subtraction,
then the four gates for `b*t`, its difference from Bt, its square and the
final sum are added. Thus `86−2+4=88`; all gates, 14 inputs and all four
fixed leaves are live.

The first residual has degree at most 13: write `Z=M*ell+delta` with
`delta=M*(k−sigma_prime)+Y*b`, of degree at most 5, and use

```
A0 = 2*(M*ell)*delta + delta² − M²*(1+ell*k).
```

The other three residuals have degree at most 13, 13 and 10 by the same
exact cancellation and bounds as in the reviewed signed-fold packet; the
guard has degree at most 2. The complete sum of squares has degree at most
26. A direct modular ray at authenticated actual ports has degree 26 with
leading coefficient 85432412 modulo 1000000007, so its specialized integer
degree is exactly 26.

Numerically this improves the separate 14-input 89/26 guarded graph by one
operation, and trades an extra input for lower degree at the same operation
count versus the 13-input 88/30 parent. The 14-variable PDF equation uses
fewer operations and higher degree. These are comparisons to named records,
not global optimality or a new PDF/Lean correspondence claim.

```
python3 -I -S -B research/ordinary14-guarded-fold88-26/check.py > /tmp/guarded-fold88.json
cmp /tmp/guarded-fold88.json research/ordinary14-guarded-fold88-26/result.json
```

The finite checker does not replace the unbounded proof above.

Independent external review is recorded in
`../../reviews/ordinary14-guarded-fold88-26-independent/`.
