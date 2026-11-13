# Proposed direct-X zero at odd-beta, even-q toy ports

This packet proposes a full positive zero of the
[`14/73` direct-X probe](../ordinary14-universal-trace-bound/) at toy ports

```
beta=3, K0=5, MC=2, MF=2.
```

The proposed witness has `q=10`, `X=2^8283` and `10∤X`. Thus beta is
**odd** and q **even**, unlike the reviewed `beta=4, q=5` toy. The toy
ports satisfy the usual strict scalar box but do not equal compact44 and
have `beta<46`. The finite modular computation below passes; the unexpanded
Pell completion and the separate fixed-q parent exclusion require
independent review. This is not an actual-port solution, unrestricted
zero-existence separation, new Lean/iPRA theorem, PDF/JSON binding or fresh
provider replay.

## Exact scalar and modular-binomial seed

Take

```
J=3, b=J*beta=9, q=b+1=10,
F=1, alpha=2, qF=q−F=9, C=q−F−alpha=7,
G=b*qF+alpha=83,
R=G*(q²−1)+J*(MC+q*MF)=8283,
N=(R−1)/2=4141, X=2^R.
```

All listed witness inputs are positive. The scalar rank window is satisfied:
`R>=26`, `R≡3 (mod 4)`, and `R+q³+q+1=9294<=10000=q⁴`. Define

```
Bprime=C*(X+K0)−F=7X+34,
h=1+Bprime/b.
```

Because `R≡3 (mod 6)`, `X≡8 (mod 9)` and `9|Bprime`, so h is a positive
integer. The shifted guard factor is exactly
`C*(X+K0)+qF−b*h=1`. Also `X≡8 (mod 10)`, so no integer w satisfies
`X=q*w`.

Let

```
Y=(1/2)*sum_{j=0}^N binom(2N,j)*X^(N−j).
```

The checker evaluates the **numerator modulo `2*q³=2000`** by Horner's
rule, using exact integer updates for the binomial coefficients, and obtains
zero. The numerator is therefore divisible by 2000 and Y is a positive
integer divisible by 1000; write `s=Y/q³>0`. This establishes the stated
divisibility without materializing the approximately 34-million-bit Y.

## Proposed aligned Pell completion

Put

```
E=X*Y, m=E*Y, a=E+Y, H=4*a+3,
Delta=(a+2)²−1, U=Y*q²,
k=2*psi_(2m+1)(N+1), r=chi_(2m+1)(N+1),
c=psi_(a+2)(R), d=chi_(a+2)(R),
eta=c−Y*k, zeta=k−eta,
gamma0=(d−X−a*c)/H,
gamma=gamma0+(k−R−1)/U.
```

Pell notation means
`(p+sqrt(p²−1))^j=chi_p(j)+psi_p(j)*sqrt(p²−1)`, and the completion is
exactly that in the reviewed
[`q=5` toy](../ordinary14-direct-x73-q5-toy/). Here `X=2^(2N+1)>144N`
and the prescribed binomial Y satisfies `Y>X^N/2`, so the reviewed floor
argument gives `Y<c/k<Y+1`; eta and zeta are positive. The first Pell norm
is exact. Its recurrence gives `4m|(k−R−1)`; because `q²|Y`, `U|m` even
though **q does not divide X**. The trace identity gives integral positive
`gamma0>=2^(R−2)` and `k>=R+1`, so gamma is positive and the modified main
carrier gives `Dstar=U*d`.

For the remaining positive inputs define

```
f+L0*sqrt(Delta)=(d+c*sqrt(Delta))^c,
i=Delta*L0/c²,  S0=Delta*L0,
V=chi_S0(R)/S0,  y=psi_S0(R),
T=(V+c+f²*R)/(c*f²).
```

The cited aligned-index Pell and Chebyshev reasoning, with R=8283 in both
indices and `R≡3 mod 4`, gives positive integers f, i, T, y, `g72=0` and
`Fa=1`. Together with the two norms and guard factor, this **purports** to
make the five-unit output zero. These enormous finite Pell expressions are
not evaluated by the checker; the unbounded proof remains under review.

## Fixed-q parent exclusion is conditional

At the same toy ports, a positive 74-parent input with q=10 has J=3 and
syntactically satisfies `10|X`. The reviewed scalar window and P72Exact
source statements, together with the independently reviewed universal trace
bound, would give `X=2^R` for any parent zero without requiring beta>=46.
No power of 2 is divisible by 10, so the parent would have no zero with
q=10. This inference is conditional on the documented fact-level source
replay and is not a proof about a parent zero at other q. It is not a
compact44 or unrestricted zero-existence conclusion.

```
python3 -I -S -B research/ordinary14-direct-x73-q10-toy/check.py > /tmp/direct-x73-q10.json
cmp /tmp/direct-x73-q10.json research/ordinary14-direct-x73-q10-toy/result.json
```

The finite checker pins the direct-X graph and cited source files. It checks
only scalar identities, port bounds, guard, X modulo 10 and the exact
modular binomial computation; it neither evaluates the Pell witnesses nor
replays the source providers or runs Lean.

Independent source review is recorded in
`../../reviews/ordinary14-direct-x73-q10-toy-independent/`.
