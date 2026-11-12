# Proposed full positive toy zero for the direct-X 73-gate probe

This packet proposes a **full positive zero** of the
[`14/73` direct-X graph](../ordinary14-universal-trace-bound/) at the toy
ports

```
beta=4, K0=1, MC=2, MF=5.
```

It has `q=5`, `R=339` and `5 ∤ X`, so it cannot be mapped back by the
parent's direct coordinate condition `X=q*w`. The toy ports satisfy
`beta>0`, `K0>=0`, `0<MC<beta` and `0<MF<2*beta`, but **are not the
actual compact44 ports** and have `beta<46`. The symbolic Pell completion
below is submitted for independent review. It does not prove a full zero at
the actual ports, unrestricted positive-zero nonequivalence, a Lean/iPRA
theorem or a PDF/JSON binding.

## Exact finite scalar data

Choose

```
J=1, q=5, b=4, F=2, alpha=1, C=q−F−alpha=2,
qF=q−F=3, G=b*qF+alpha=13,
R=G*(q²−1)+MC+q*MF=339, N=(R−1)/2=169,
X=2^R, h=1+X/2.
```

All named inputs are positive and the guard factor is

```
C*(X+K0)+qF−b*h = 2*(X+1)+3−4*(1+X/2) = 1.
```

The finite checker constructs

```
Y=(1/2)*sum_{j=0}^N binom(2N,j)*X^(N−j)
```

exactly. It verifies `5³|Y`, `2^339 mod 5=3`, `R=3 mod 4`,
`R>=26`, and `R+q³+q+1<=q⁴`. Y has 57,291 bits and SHA-256
`bfc970beead6d20dd6e1b1d0f95025dd1c6d337474f380025c3c0390a0381f3c`
in its minimal little-endian representation. Put `s=Y/125>0`.

## Proposed remaining witnesses

Let

```
E=X*Y, m=E*Y, a=E+Y, H=4*a+3,
Delta=(a+2)²−1, U=Y*q².
```

Use `(p+sqrt(p²−1))^j=chi_p(j)+psi_p(j)*sqrt(p²−1)` and define

```
k=2*psi_(2m+1)(N+1), r=chi_(2m+1)(N+1),
c=psi_(a+2)(R), d=chi_(a+2)(R),
eta=c−Y*k, zeta=k−eta,
gamma0=(d−X−a*c)/H,
gamma=gamma0+(k−R−1)/U.
```

The prescribed binomial Y has `Y>X^N/2`, and `X=2^(2N+1)>144N`.
The reviewed floor calculation in
[`current14-carrier64-pell-floor`](../current14-carrier64-pell-floor/)
therefore gives `Y<c/k<Y+1`, so eta and zeta are positive. The first Pell
norm gives `r²=1+m*(m+1)*k²`. The first Pell congruence gives
`4*m|(k−R−1)`, and `U|m` because `25|Y`; hence gamma is integral.
The trace identity gives `gamma0>=2^(R−2)>0`, and `k>=R+1`, so gamma
is positive. The modified main carrier then satisfies `Dstar=U*d`, and the
main Pell norm vanishes.

For the strong and auxiliary inputs use the aligned-index completion from the
reviewed [`compact44 signed-fold witness`](../ordinary13-folded-root86-negated-compact44-seed/):

```
f+L0*sqrt(Delta)=(d+c*sqrt(Delta))^c,
i=Delta*L0/c², S0=Delta*L0,
V=chi_S0(R)/S0, y=psi_S0(R),
T=(V+c+f²*R)/(c*f²).
```

The cited binomial/Pell and Chebyshev arguments for the same index R and
`R=3 mod 4` give positive integers f, i, T, y, `g72=0` and `Fa=1`.
Together with the first/main norms and guard factor above, these expressions
**purport** to set all five unit factors to 1. The enormous Pell expressions
are exact finite definitions, not expanded values; the inherited unbounded
argument is the subject of independent review, not of the finite checker.

## Optional stronger fixed-q exclusion, conditional on source replay

At these fixed toy ports, any parent input with q=5 has J=1 and its rank
obeys `R≡MC+q*MF≡3 (mod 4)`, since `q²−1` is divisible by 4. The parent
has `X=q*w`, so `5|X`. If the cited fact-level exact-index replay and the
reviewed [universal trace bound](../ordinary14-universal-trace-bound/)
are applied to such a parent zero, they give `X=2^R`, contradicting
`2^R≡3 (mod 5)`. The replay needs the parent's positive scalar gap, the
source theorem hypotheses, and the displayed scalar-box/window conditions;
it has **not** been freshly checked for this toy parent. Thus this is a
conditional fixed-q exclusion, not an unrestricted parent nonexistence or
actual-port result.

```
python3 -I -S -B research/ordinary14-direct-x73-q5-toy/check.py > /tmp/direct-x73-q5.json
cmp /tmp/direct-x73-q5.json research/ordinary14-direct-x73-q5-toy/result.json
```

The checker pins the graph and relevant source files and verifies only the
finite scalar, guard, modular and binomial statements. It does not evaluate
the enormous Pell witness, replay the cited source providers, or run Lean.

Independent source review is recorded in
`../../reviews/ordinary14-direct-x73-q5-toy-independent/`.
