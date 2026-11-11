# A full toy-port zero obstructing folded-root positivity

This is a symbolic positive zero of the reviewed **88/30 free-J graph** at
explicit toy ports

```
beta=31, K0=9, MC=14, MF=46.
```

For its fixed other twelve coordinates, neither first-root branch gives a
positive absorbed coordinate `rho=r−k*Bt` in the conditional 86/26 graph.
It is not a zero at the compact44 ports and does not disprove unrestricted
positive zero-existence equivalence. Its huge witnesses are unexpanded. No
new Lean/iPRA, PDF or file-semantics theorem is claimed. The construction is
submitted for independent review.

## Scalar and Pell seed

Reuse the independently reviewed scalar/binomial/first/main construction
from `../current14-carrier64-free-s-toy-zero/`:

```
q=32, beta=31, J=1, F=1, alpha=14, C=17,
R=998911, X=2^R, w=2^(R−5), N=(R−1)/2,
Y=(1/2)*sum_{j=0}^N binom(2N,j)*X^(N−j),
s=Y/q³, E=X*Y, m=E*Y, a=E+Y, A=a+2,
Delta=A²−1, H=4a+3,
k=2*psi_(2m+1)(N+1), tau=chi_(2m+1)(N+1),
c=psi_A(R), D0=chi_A(R),
eta=c−Y*k, zeta=k−eta,
gamma0=(D0−X−a*c)/H,
z=1+((K0+w)*C−F)/beta.
```

Pell notation and the general floor/trace arguments are those in the
inherited packet. They give positive integer `s,eta,zeta,gamma0,z`,
`Y<c/k<Y+1`, the first Pell identity
`tau²−m(m+1)k²=1`, and the main identity `D0²−Delta*c²=1`. The finite
checker independently reproduces the scalar rank, popcount, port-box and
transport residues. In particular `R=3 mod 4`, `v2(Y)=15` and `q³|Y`.

In the 88 graph let `b=qm=beta`, `U=Y*q²`, `M=q³*b` and

```
Bt=C*(X+K0*q)−F*q,    t=Bt/b=q*(z−1),
ell=E*k*Y=m*k,
rho_plus=tau−ell−k−s+t,
r=k*Bt+rho_plus,
gamma=gamma0−w+(k−R−1)/U.
```

All are integers. Indeed the transport congruence makes t integral;
`k−R−1` is divisible by E by the first Pell congruence, and
`U|E` since `E/U=w/q` is an integer. The quotient is positive, and
`gamma0>=2^(R−2)=8w`, so gamma is positive. Substitution gives
`Dstar=U*D0`, hence the second residual A1 is zero.

Also `Z=M*tau`, because `Y*b=M*s` and `q³*Bt=M*t`. Thus the first
residual A0 is zero. The first Pell equation gives
`ell<tau<ell+k`.

## Both absorbed roots are negative

The binomial sum gives `Y>X^N/2`, with N>=3. Therefore

```
s > X³/(2q³) > 34*(X+9) > t,
```

where `t=q*((K0+w)*17−1)/31 < 34*(9+X)`; the checker verifies a
sufficient numerical lower bound using only `X>=2^20`. Hence

```
rho_plus=tau−ell−k−s+t < 0.
```

The other first-root branch has
`rho_minus=−tau−ell−k−s+t<rho_plus<0`. Nevertheless the **old** input r is
positive: `tau>ell`, `Bt>=31`, and `k>s` (already `k>=4*(2E*Y+1)>s`),
so `r>k*(Bt−1)−s+t>0`.

## Strong and auxiliary factors

Choose the c-th power `f+L*sqrt(Delta)` of `D0+c*sqrt(Delta)`.
The binomial expansion gives `c²|L`. Set `i=Delta*L/c²>0`, so
`I=i*c²=Delta*L` and

```
Q=Delta*(f²−1)=I².
```

Thus `Fs=1`. Put `S=I`, `V=chi_S(R)/S` and `y=psi_S(R)`. Since
`R=3 mod 4`, the reviewed odd-index Chebyshev congruences give
`V=−c mod f²` and `V=−R mod c`. With `f²=1 mod c`,
`T=(V+c+f²*R)/(c*f²)` is a positive integer and the literal V definition
holds. The auxiliary Pell identity gives `Fa=1`. Also `V>1` and the same
identity implies `y>V`, so the free-J input `u=y−V` is positive.

All four residuals of the 88/30 graph vanish at this positive tuple. With
all other coordinates fixed, the 86/26 graph's only possible first-root
choices are the two displayed negative rho values. This is a full toy-port
same-other-coordinates obstruction, not a claim about actual compact44 ports
or the two graphs' unrestricted existence equivalence.

The checker pins the literal 88 graph, checks the scalar data and the stated
sufficient bounds. It does not expand the huge binomial/Pell values or prove
the unbounded inherited arguments; the whole construction is submitted for
independent review.

```
python3 -I -S -B research/ordinary13-folded-root86-toy-full-zero/check.py > /tmp/folded-root86-toy-zero.json
cmp /tmp/folded-root86-toy-zero.json research/ordinary13-folded-root86-toy-full-zero/result.json
```

Independent external review is recorded in
`../../reviews/ordinary13-folded-root86-toy-full-zero-independent/`.
