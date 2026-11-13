# Withdrawn full-zero attempt at alternate carrier65 ports

**This attempt is withdrawn.** Independent review found two material errors:
the payloads used below are the alternate maintained carrier65 ports with
`beta=2^94517−1`, not the free-J compact44 ports with `beta=2^590069−1`; and
the claimed auxiliary congruence is not justified because its Pell index `R`
differs from the main index `rX`. A full positive zero is not established,
even for the alternate ports. The draft reasoning is retained below as a
conditional research record; every downstream assertion depends on resolving
that missing auxiliary completion. The original compact44 claim was false.
No Lean or unrestricted existential conclusion is claimed.

## Previously reviewed alternate-port seed

Use the scalar, strict Pell-ratio and first/main construction of
`../current14-free-gap-current-full-zero/`, including its four pinned port
payloads. In its notation, put `B=94517`, `q=2^B=beta+1`, `J=1`, `C=1`,
`e=28633`, `F=(K0+2^e) mod beta`, `alpha=q−F−1`, and let

```
R=(beta*(q−F)+alpha)*(q²−1)+MC+q*MF,
d=(R+1)/3,   rX=2d,   h=3d/2,   lambda=d−1,
X=2^rX,  Y=2^lambda,  E=X*Y=2^R,  w=2^(rX−B),
s=Y/q³,  z=1+(K0+w−F)/beta,
m=E*Y,  a=E+Y,  A=a+2,  Delta=A²−1,  H=4a+3,
k=2*psi_(2m+1)(h),  tau=chi_(2m+1)(h),
c=psi_A(rX),  D0=chi_A(rX),
eta=c−Y*k,  zeta=k−eta,
gamma0=(D0−X−a*c)/H.
```

The inherited reviewed results give all these as positive integers,
`R=3 mod 4`, `2h=R+1`, `Y<c/k<Y+1`, `tau²−m(m+1)k²=1`,
`D0²−Delta*c²=1`, `k≡R+1 (mod E)` and the transport congruence. The finite
checker rechecks the alternate payloads and scalar/exponent facts. In particular
`rX>bit_length(K0)+B+10`, so `E>K0+w`, and `lambda>=3B+2`, so `Y>=4`.

## Positive 88-graph first and main inputs

Set `b=beta`, `U=Y*q²`, `M=q³*b`, and

```
Bt=X+K0*q−F*q = q*(K0+w−F),  t=Bt/b=q*(z−1),
ell=m*k,  rho_plus=tau−ell−k−s+t,
r=k*Bt+rho_plus,
gamma=gamma0−w+(k−R−1)/U.
```

Here `U|E`, because `E/U=2^(rX−2B)` is a positive integer; consequently
`(k−R−1)/U` is an integer. It is positive, since `k>R+1`; the trace formula
gives `gamma0>=2^(rX−2)>w`, so gamma is positive. Also `Bt>=q` because
`w>q>F`. Since `tau>ell`, `k>=4*(2m+1)>s` and `Bt>=2`, we have
`r>k*(Bt−1)−s+t>0`.

In the literal 88 graph the first expression has `Z=M*tau`, since
`Y*b=M*s` and `q³*Bt=M*t`. For the second expression, `E*q=U*w` and the
chosen gamma make `shift=U*gamma0`, hence `Dstar=U*D0`. The first two
four-square residuals are therefore zero.

## Both 86-graph first-root choices are negative

First `t<2*(K0+w)<2E` because `q/beta<2`, F>0 and `E>K0+w`.
Since `h>=2`, `k>=4*(2m+1)>8*E*Y>=32E`, and hence `t<k/4`.
The Pell identity with m>=1 and k>=2 yields

```
(ell+3k/4)²−tau² = (m/2+9/16)*k²−1 > 0,
```

so `tau<ell+3k/4`. It follows that

```
rho_plus=tau−ell−k−s+t < −k/4−s+t < 0,
rho_minus=−tau−ell−k−s+t < rho_plus < 0.
```

The 86 first residual fixes the corresponding first-root value to `+tau`
or `−tau`; therefore these are the only two possible rho values with the
other twelve coordinates fixed. Both are negative although the constructed
88-graph input r is positive.

## Ordinary strong and auxiliary completion

As in the independently reviewed toy full-zero packet
`../ordinary13-folded-root86-toy-full-zero/`, take
`f+L*sqrt(Delta)=(D0+c*sqrt(Delta))^c`. Binomial expansion gives `c²|L`;
set `i=Delta*L/c²`, `I=i*c²=Delta*L` and `S=I`. Then
`I²=Delta*(f²−1)`, so the strong residual is zero. Put
`V=chi_S(R)/S`, `y=psi_S(R)`, `u=y−V` and
`T=(V+c+f²*R)/(c*f²)`. **Rejected step:** the Chebyshev congruence gives `V≡−psi_A(R) (mod f²)`,
not the required `V≡−c (mod f²)`, because `c=psi_A(rX)` and `rX<R`.
Put `cR=psi_A(R)`. Then `0<cR−c<f²`: indeed `c>=rX`, `rX²>2R`,
`D0>=A^rX`, and hence `f>D0^c>A^(2R)>(2A)^(R−1)>=cR`. Thus
`V+c` is not divisible by `f²`, so the displayed T is nonintegral. This
particular completion fails; a different completion remains open. The auxiliary Pell identity would give the last residual zero provided the
literal V equation holds; `V>1` implies `y>V` and hence u>0.

Conditional on an independently justified completion, the obstruction
is **same-other-coordinates only**: it neither rules out another 86 witness
with changed coordinates nor settles unrestricted existence equivalence.
The scalar/Pell/trace results have historical reviewed ancestry; this packet
is not a fresh transitive provider audit or an in-Lean theorem. Its small
checker verifies port/source pins and finite exponent inequalities; it does
not itself prove the symbolic Pell identities.

Independent review of the withdrawn attempt is recorded in
`../../reviews/ordinary13-folded-root86-current-full-zero-independent/`.
