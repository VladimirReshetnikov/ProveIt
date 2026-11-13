# A full signed-fold zero with boxed toy ports

The sign-reversed 86/26 candidate has a symbolic positive zero at toy ports

```
beta=31, K0=9, MC=13, MF=55,    0<MC<beta<MF<2*beta.
```

At this zero, `Bt<0`, and **no positive parent zero can preserve the other
ten inputs and the rank R**, even when F, alpha, and the first coordinate are
allowed to change arbitrarily. This is a stronger obstruction than failure of
the restricted scalar-shift window. These are toy ports, not the compact44
ports; this does not settle unrestricted positive zero-existence equivalence,
prove a zero at the actual ports, or give a Lean/iPRA theorem. The symbolic
construction is submitted for independent review.

## Scalar and Pell data

Use

```
J=F=1, alpha=45, q=32, b=31, C=q−F−alpha=−14,
G=b*(q−F)+alpha=1006,
R=G*(q²−1)+J*(MC+q*MF)=1030911,
X=2^R, N=(R−1)/2,
Y=(1/2)*sum_{j=0}^N binom(2N,j)*X^(N−j),
s=Y/q³, E=X*Y, m=E*Y, a=E+Y, H=4*a+3,
Delta=(a+2)²−1, U=Y*q², w=X/q,
Bt=C*(X+K0*q)−F*q, t=Bt/b.
```

The finite checker verifies `R=3 mod 4`, `v2(Y)=popcount(N)−1=15`,
`X=2 mod 31`, and `Bt=−14*(X+288)−32=0 mod 31`. Thus `s` and `t` are
integers, with `s>0` and `t<0`. The valuation is the reviewed
central-binomial identity used in
`../current14-carrier64-current-full-zero/`.

Write `(p+sqrt(p²−1))^j=chi_p(j)+psi_p(j)*sqrt(p²−1)`. Set

```
k=2*psi_(2m+1)(N+1), tau=chi_(2m+1)(N+1),
c=psi_(a+2)(R), D0=chi_(a+2)(R),
eta=c−Y*k, zeta=k−eta, ell=m*k,
gamma0=(D0−X−a*c)/H,
gamma=gamma0−w+(k−R−1)/U,
sigma=ell+k+s−t−tau.
```

The reviewed general floor argument in
`../current14-carrier64-pell-floor/` gives `Y<c/k<Y+1`, hence positive
integers eta and zeta. It also gives the two relevant Pell identities. The
first Pell congruence gives `E|(k−R−1)`; because `X/q²` is integral,
`U|E`. Also `psi_p(j)>=j` for `p>=1`, hence `k>=R+1`. The trace formula
gives `gamma0>=2^(R−2)>w`, so gamma is a positive integer. Since `tau<ell+k` and `t<0`, sigma is positive. With `M=q³*b`,
`Z=M*(ell+k−sigma)+Y*b−q³*Bt=M*tau`, so `A0=0`. Substitution into the
literal shift gives `Dstar=U*D0`, so `A1=0`.

Choose the strong and auxiliary inputs using the same construction as the
independently reviewed `../ordinary13-folded-root86-toy-full-zero/`:

```
f+L*sqrt(Delta)=(D0+c*sqrt(Delta))^c,
i=Delta*L/c²,
S=Delta*L, V=chi_S(R)/S, y=psi_S(R),
T=(V+c+f²*R)/(c*f²), u=y−V.
```

The binomial and Chebyshev arguments cited there give positive integers
`f,i,T,u`, and make the remaining residuals `g72` and `Fa−1` zero. Hence the
four-square candidate is zero at thirteen positive integer inputs. These
witnesses are specified by exact finite sums and powers; their enormous
values are not expanded or numerically evaluated.

## No fixed-rank scalar repair

For any positive F′ and alpha′, the fixed J and ports and the same rank R
force the same `G=1006`. The identities `G=b*(q−F′)+alpha′` and `q=b+1`
give

```
C′=q−F′−alpha′=q*(q−F′)−G <= 32*31−1006 = −14,
Bt′=C′*(X+K0*q)−F′*q < 0.
```

A positive parent zero cannot have `Bt′<=0`: its literal first expression
would be strictly greater than `M*(ell+k)`, but its norm equation gives
`|Z|=M*tau<M*(ell+k)`. Therefore varying F′, alpha′ and the parent first
coordinate cannot repair this zero while retaining rank and the other ten
inputs. In particular the limited scalar-shift criterion also fails, since
`F=1` and `Bt<0`. This is not a proof that the parent has no zero with other
inputs or rank.

```
python3 -I -S -B research/ordinary13-folded-root86-negated-boxed-full-zero/check.py > /tmp/boxed-full-zero.json
cmp /tmp/boxed-full-zero.json research/ordinary13-folded-root86-negated-boxed-full-zero/result.json
```

The checker pins the graph and checks finite scalar, residue and rank data.
The unbounded Pell/floor argument is inherited from the cited reviewed
sources and is not replaced by these finite checks.

Independent external review is recorded in
`../../reviews/ordinary13-folded-root86-negated-boxed-full-zero-independent/`.
