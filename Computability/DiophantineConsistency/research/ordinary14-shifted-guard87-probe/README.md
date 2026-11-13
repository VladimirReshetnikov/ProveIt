# A conditional 87-operation shifted-guard probe

This is a **probe, not a replacement equation**: it has 14 positive inputs,
87 live operations and degree 26 at the authenticated compact44 ports, but
its reverse positive-zero implication to the 88/26 quotient-guarded graph is
open. The graph and unbounded claims are submitted for independent review.
No new Lean/iPRA theorem, PDF correspondence or global minimality claim is
made.

Let the reviewed 88/26 guard input be t and set `omega=t+F`. Its guard
`Bt=b*t`, with `Bt=C*(X+K0*q)−F*q` and `b=q−1`, becomes

```
C*(X+K0*q)−F−b*omega = 0.                 (1)
```

This uses one fewer operation in the literal graph: it replaces `F*q` and
`Bt` by `C*(X+K0*q)−F`, and uses `b*omega` in the guard. The first
expression and other four residuals are the same as in 88/26. Every 88/26
zero maps to a probe zero by `omega=t+F>F`. Conversely any probe zero with
`omega>F` maps back by `t=omega−F>0`. The branch `omega<=F` has no such
positive t and remains unresolved; no same-witness failure implies an
unrestricted nonequivalence.

## Bounds on the unresolved branch

Assume `beta>0`, `K0>=0` and (1). As `omega>0` and F>0,
`C*(X+K0*q)=b*omega+F>0`, hence C>0 and `F<=b−1`. If `b<=K0`,

```
Bt=C*(X+K0*q)−F*q >= X+(K0−F)*q > 0,
omega=F+Bt/b>F.
```

Thus an unresolved positive zero must have `b>K0`. Moreover, when
`omega<=F`, equation (1) gives

```
C*(X+K0*q)=b*omega+F <= q*F < q²,
```

so `X<q²`. It would suffice to prove a suitable unconditional bound
`X>=q²` for the modified graph. The known rank-window applications of
`P72Exact.indices_ordinary` and `P72Power.power_of_mod` have additional
hypotheses including `X>=q` and `R+1<XY`; they do not immediately provide
this bound here. Neither it nor a complete zero on the unresolved branch is
claimed.

## An actual-port partial seed that fails the main norm

The following shows that the unresolved scalar branch and first norm are
consistent with the actual port integers, but it is **not** a full zero.
At the authenticated compact44 ports `beta>1` and `K0>0`, put

```
J=K0+2, b=J*beta, q=b+1, F=K0+1,
alpha=b−F, C=1, omega=K0, X=1, Y=q³.
```

All named inputs are positive and `omega=F−1`. The guard vanishes and
`Bt=−b<0`. Let `m=Y²`, `s=1` and consider first-Pell index one:

```
k=2, tau=2m+1, ell=m*k, sigma_prime=2.
```

Then `Z=M*tau` and the first residual is zero. Nevertheless `k=2` forces
`eta=zeta=1` and `c=2Y+1`. Since `a=2Y` and
`1<c<2(a+2)`, the number `1+((a+2)²−1)c²` lies strictly between consecutive
squares; the main residual A1 can never vanish, whatever the remaining
inputs. This is the reviewed consecutive-square exclusion.

For the second first-Pell index, put

```
k=8m+4, tau=8m²+8m+1, sigma_prime=4m+4.
```

The guard and first norm again vanish for any positive `eta,zeta` summing to
k. Here the main norm also cannot vanish: `c=kY+eta` would have to be a
Pell ordinate `psi_A(n)` with `A=2Y+2` and
`kY<c<k(Y+1)`. For `Y>=8`, the increasing sequence has

```
psi_A(3)=16*(Y+1)²−1 < kY,
psi_A(4)=64*(Y+1)³−8*(Y+1) > k*(Y+1),
```

so no such ordinate exists. This excludes these two explicit Pell seeds,
not every higher-index choice or every unresolved scalar assignment.

## Graph and degree checks

The checker reconstructs the exact graph delta from the reviewed 88/26
candidate, checks 87 live gates, 14 distinct inputs and four fixed leaves,
authenticates the port bytes and verifies the port inequalities. On the
all-inputs-equal modular ray the guarded output has degree 26, with the
leader in `result.json`; the same cancellation and guard-degree bounds as
in 88/26 give degree at most 26. The checker is a finite graph/degree check,
not an unbounded proof, full-zero witness, or source/provider replay.

```
python3 -I -S -B research/ordinary14-shifted-guard87-probe/check.py > /tmp/shifted-guard87.json
cmp /tmp/shifted-guard87.json research/ordinary14-shifted-guard87-probe/result.json
```

Independent external review is recorded in
`../../reviews/ordinary14-shifted-guard87-probe-independent/`.
