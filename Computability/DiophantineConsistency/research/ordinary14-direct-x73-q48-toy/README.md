# Proposed direct-X zero at beta=47, q=48 toy ports

This packet proposes a full positive zero of the
[`14/73` direct-X probe](../ordinary14-universal-trace-bound/) at toy ports

```
beta=47, K0=29, MC=6, MF=7.
```

The proposed witness has odd `beta>=46`, even q=48 and `48∤X`. It therefore
passes the simple beta and q parity filters and the scalar port box, while
remaining a **toy**: beta is not the actual compact44 Mersenne numeral.
The finite modular-binomial calculation below passes; the unexpanded Pell
completion and fixed-q parent exclusion are submitted for independent review.
No actual-port zero, unrestricted positive-zero separation, Lean/iPRA
theorem, PDF/JSON binding or fresh provider replay is claimed.

## Exact scalar data

Take

```
J=1, b=47, q=48, F=46, alpha=1, qF=q−F=2,
C=qF−alpha=1, G=b*qF+alpha=95,
R=G*(q²−1)+MC+q*MF=219127,
N=(R−1)/2=109563, X=2^R.
```

All listed inputs are positive. The scalar box and rank window hold:
`0<MC<beta`, `0<MF<2beta`, `R>=26`, `R≡3 (mod 4)`, and
`R+q³+q+1=329768<=q⁴=5308416`. Exact modular arithmetic gives
`X≡17 (mod 47)` and `X≡32 (mod 48)`. Thus

```
Bprime=C*(X+K0)−F=X−17,
h=1+Bprime/b > 0,
C*(X+K0)+qF−b*h = 1.
```

The guard factor is 1 but no integer w satisfies `X=q*w`, because q has
an odd factor 3.

## Exact divisibility of the symbolic binomial Y

Define the enormous positive integer

```
Y=(1/2)*sum_{j=0}^N binom(2N,j)*X^(N−j),   s=Y/q³.
```

The checker evaluates the numerator modulo 27 by Horner's rule with exact
integer binomial updates and obtains zero. Since 2 is invertible modulo 27,
`27|Y`. It also checks `popcount(N)=13`. Every noncentral summand of Y is
divisible by `X/2=2^(R−1)`; the central summand has
`v2(binomial(2N,N)/2)=popcount(N)−1=12` by the reviewed central-binomial
valuation. Therefore `v2(Y)=12`. As `q³=48³=2^12*27`, it follows that
`q³|Y` and s is a positive integer. The approximately 24-billion-bit Y is
not materialized or stored.

## Proposed aligned Pell completion

Let `(p+sqrt(p²−1))^j=chi_p(j)+psi_p(j)*sqrt(p²−1)` and put

```
E=X*Y, m=E*Y, a=E+Y, H=4*a+3,
Delta=(a+2)²−1, U=Y*q²,
k=2*psi_(2m+1)(N+1), r=chi_(2m+1)(N+1),
c=psi_(a+2)(R), d=chi_(a+2)(R),
eta=c−Y*k, zeta=k−eta,
gamma0=(d−X−a*c)/H,
gamma=gamma0+(k−R−1)/U.
```

`X=2^(2N+1)>144N` and the binomial Y satisfies `Y>X^N/2`, so the
reviewed Pell-floor argument cited in the [`q=5` toy](../ordinary14-direct-x73-q5-toy/)
gives `Y<c/k<Y+1`; eta and zeta are positive. The first Pell norm is
exact. Its recurrence gives `4m|(k−R−1)`; `q²|Y` implies `U|m`,
**without** assuming q|X. The trace identity gives integral positive
`gamma0>=2^(R−2)` and `k>=R+1`, so gamma is positive and the modified main
carrier equals `U*d`.

For the remaining coordinates use the same aligned-index completion:

```
f+L0*sqrt(Delta)=(d+c*sqrt(Delta))^c,
i=Delta*L0/c², S0=Delta*L0,
V=chi_S0(R)/S0, y=psi_S0(R),
T=(V+c+f²*R)/(c*f²).
```

The cited Pell and Chebyshev reasoning, with the **same** index R in the
main and auxiliary terms and `R≡3 mod 4`, gives positive integers f, i, T, y,
`g72=0` and `Fa=1`. Together with the two norms and the guard factor, this
**purports** to make the product output zero. These unbounded deductions are
not finite-checker output and require independent review.

## Conditional fixed-q parent exclusion

At these toy ports, a positive 74-parent with q=48 has J=1 and syntactically
requires `48|X`. The source rank/index replay plus the reviewed universal
trace bound would force `X=2^R` for any such parent zero; 48 has an odd
factor 3 and cannot divide a power of 2. This is a **conditional fixed-q**
exclusion subject to the cited source replay. It does not rule out parent
zeros with other q, or show any nonequivalence at the actual compact44 ports.

```
python3 -I -S -B research/ordinary14-direct-x73-q48-toy/check.py > /tmp/direct-x73-q48.json
cmp /tmp/direct-x73-q48.json research/ordinary14-direct-x73-q48-toy/result.json
```

The checker pins the direct-X graph and cited source files, verifies the
scalar/guard facts and computes the modular binomial numerator exactly. It
does not materialize Y or the much larger Pell witnesses, replay source
providers, or run Lean.

Independent source review is recorded in
`../../reviews/ordinary14-direct-x73-q48-toy-independent/`.
