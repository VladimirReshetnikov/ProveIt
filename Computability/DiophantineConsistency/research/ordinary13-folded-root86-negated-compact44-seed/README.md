# A proposed actual-port symbolic signed-fold zero

This packet gives an explicit CRT/binomial/Pell construction intended to be a
positive zero of the **sign-reversed 86/26 candidate** at the actual
compact44 P72/P115 ports. It is submitted for independent review: the checker
confirms the exact port hashes and finite scalar prerequisites but does not
materialize the huge Pell inputs or prove the unbounded identities. No Lean,
iPRA, PDF binding, parent zero, or unrestricted equivalence conclusion is
claimed. In particular, this is not a zero of the maintained 14-variable PDF
equation.

Unlike the withdrawn `R=3d−1` seed, this construction uses the main Pell
coordinate `c=psi_(a+2)(R)` and has `R=0 mod 3`, as required by the reviewed
actual-port mod-3 observation.

## Explicit scalar seed

Let the four integer ports be the little-endian raw integers authenticated by
P72 `ACTIVE_BINDING.json` and P115 `BINDING.json`, as loaded by `check.py`.
Write

```
B=590069, beta=2^B−1, q=beta+1, J=F=1, Q=q²−1.
```

Let `K=K0`, and let `alpha0` be the representative specified by the CRT
algorithm in the checker, adjusted by at most one positive period so that
`alpha0>beta`. Explicitly, it satisfies

```
alpha0*(K+1) = −1 (mod beta),
R0=(beta²+alpha0)*Q+MC+q*MF = 0 (mod B),
alpha0 = MC (mod 4),  hence R0 = 3 (mod 4).
```

The checker verifies `gcd(K+1,beta)=gcd(Q,B)=gcd(beta,B)=1`, and computes the
specific inverses and CRT representative. Set

```
P=4*B*beta, W=P*Q,
L=bit_length(R0)+1, S=bit_length(W)+1,
alpha=alpha0+P*sum_{j=0}^3 2^(L+j*S),
R=(beta²+alpha)*Q+MC+q*MF, N=(R−1)/2.
```

The checker computes these finite integers exactly. It finds

```
bit_length(R)=9441197, R=0 (mod B), R=3 (mod 4), R=0 (mod 3),
popcount(N)=5379471 >= 3*B+1.
```

Define `X=2^R`, `C=q−F−alpha=beta−alpha<0`, and
`Bt=C*(X+K*q)−F*q<0`. Since `R=0 mod B`, `X=1 mod beta`; hence the CRT
congruence gives `Bt=0 mod beta`. Put `t=Bt/beta`, a negative integer.

## Proposed full witness

Define the positive integer

```
Y=(1/2)*sum_{j=0}^N binom(2N,j)*X^(N−j),
s=Y/q³, E=X*Y, m=E*Y, a=E+Y, H=4*a+3,
Delta=(a+2)²−1, U=Y*q², w=X/q.
```

The reviewed central-binomial identity gives
`v2(Y)=popcount(N)−1=5379470 >= 3*B`, so `s` is a positive integer.
Write `(p+sqrt(p²−1))^j=chi_p(j)+psi_p(j)*sqrt(p²−1)`, and define

```
k=2*psi_(2m+1)(N+1), tau=chi_(2m+1)(N+1),
c=psi_(a+2)(R), D0=chi_(a+2)(R),
eta=c−Y*k, zeta=k−eta, ell=m*k,
gamma0=(D0−X−a*c)/H,
gamma=gamma0−w+(k−R−1)/U,
sigma=ell+k+s−t−tau.
```

The general estimates from `../current14-carrier64-pell-floor/`, applied to
this prescribed binomial Y, give `Y<c/k<Y+1`, making eta and zeta positive.
The first Pell congruence gives `E|(k−R−1)`; `U|E` because `q²|X`.
Also `k>=R+1`, and the trace formula gives `gamma0>=2^(R−2)>w`, so gamma is
positive. Since `tau<ell+k` and `t<0`, sigma is positive. Putting
`M=q³*beta`, the candidate's first expression satisfies

```
Z=M*(ell+k−sigma)+Y*beta−q³*Bt=M*tau,
```

so `A0=0`; the shift gives `Dstar=U*D0`, so `A1=0`.

Define the remaining witnesses with the reviewed construction from
`../ordinary13-folded-root86-toy-full-zero/`:

```
f+L0*sqrt(Delta)=(D0+c*sqrt(Delta))^c,
i=Delta*L0/c²,
S0=Delta*L0, V=chi_S0(R)/S0, y=psi_S0(R),
T=(V+c+f²*R)/(c*f²), u=y−V.
```

The cited binomial/Pell and Chebyshev arguments, using `R=3 mod 4`, give
positive integers `f,i,T,u`, `g72=0` and `Fa=1`. The construction therefore
purports to make all four residuals zero with thirteen positive inputs.
The exact witness is unexpanded; these unbounded deductions are the subject
of independent review, not finite checker output.

```
python3 -I -S -B research/ordinary13-folded-root86-negated-compact44-seed/check.py > /tmp/compact44-seed.json
cmp /tmp/compact44-seed.json research/ordinary13-folded-root86-negated-compact44-seed/result.json
```

Independent external review is recorded in
`../../reviews/ordinary13-folded-root86-negated-compact44-seed-independent/`.
It independently reconstructs the scalar seed and checks the symbolic Pell
steps. Its same-q, same-R parent obstruction does not exclude parent zeros
at other q or R.
