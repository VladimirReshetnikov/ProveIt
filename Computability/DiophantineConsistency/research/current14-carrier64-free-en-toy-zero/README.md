# A toy-port zero after freeing En

Consider the maintained 65-gate source with `En=E*n` replaced by a fresh
positive input `N` and `tau=N+k−R`. This deletes one live multiplication and
leaves 14 positive inputs and 64 live operations. Every original zero maps
forward using `N=E*n`. The reverse map requires a positive original n and is
not automatic. The symbolic construction below is a full positive zero at
the **toy ports**

```
beta=31, K=29, MC=30, MF=33.
```

They obey `beta>=31`, `K>0`, and `0<MC<beta<MF<2*beta`, but they are not
the current four fixed ports. All huge Pell quantities are specified
symbolically, not expanded. The construction has passed independent external review; no Lean, PDF,
current-port zero, or unrestricted existential
nonequivalence is claimed.

## Scalars and first/main Pell data

Use

```
q=32, J=1, F=30, alpha=1, C=1, gap=63,
R=65535, X=2^R, w=2^(R−5),
Y=2^256, s=2^241, E=X*Y, h=65280.
```

The literal rank is `R=63*(32²−1)+30+32*33`. Define
`z=(K+w+1)/31`. Since `w=1 mod 31`, z is a positive integer, and the
transport factor is 1. Put

```
m=E*Y, P=2*m+1, a=E+Y, A=a+2, H=4*a+3,
Delta=A²−1,
k=2*psi_P(h), tau=chi_P(h),
c=psi_A(R), D=chi_A(R),
eta=c−Y*k, zeta=k−eta, N=tau−k+R,
gamma=(D−X−a*c)/H.
```

Pell notation is `(u+sqrt(u²−1))^j=chi_u(j)+psi_u(j)*sqrt(u²−1)`.
The first factor is 1 because `ell=E*k*Y=m*k` and
`chi_P(h)²−m*(m+1)*(2*psi_P(h))²=1`; the main factor is 1 by definition.
The known trace recurrence with `X=2^R` gives
`D−X−a*c=H*sum_{j=1}^{R−1} 2^(R−1−j)*psi_A(j)`, so gamma is a
positive integer. Also `tau>k` and N is positive.

The only size condition needed for eta and zeta is

```
Y < c/k < Y+1.                                    (1)
```

It follows without evaluating the Pell numbers. Write `r=R−1`, `s0=h−1`.
The finite checker verifies the exact dominant-power identity

```
(2*Y*X)^r / (2*(4*X*Y²)^s0) = Y.
```

The standard bounds `(2u−1)^(n−1) <= psi_u(n) <= (2u)^(n−1)` give a
lower ratio with relative factors `(1+u)^r/(1+v)^s0`, where
`u=(2Y+3)/(2YX)` and `v=1/(2XY²)`. Here `r*u>2*s0*v` and
`s0*v<1/2`, so `(1+u)^r>=1+r*u>1+2*s0*v>(1+v)^s0`.
For the upper ratio, `2A/(2YX)<1+2/X`, while `2P−1>4XY²`;
`(1+2/X)^r<1+4r/X`, and the checker verifies `4Yr<X`.
Thus the ratio lies strictly between Y and Y+1, proving `eta,zeta>0`.

Modulo E, `P=1` and `P²−1=0`, so `tau=1` and `k=2h`. Consequently

```
N = R−(2h−1) = −65024 mod E,
```

which is nonzero since E is much larger than 65024.

## Strong and auxiliary factors

Choose a positive Pell-unit power `f+L*sqrt(Delta)` of
`D+c*sqrt(Delta)` whose ordinate L is divisible by `c²`; an order in the
finite quadratic ring modulo c² provides such a power. Put `i=L/c²>0` and
`S=Delta*L`. The strong factor is 1.

Since R is 3 modulo 4, the reviewed odd-index Chebyshev congruences for

```
V=chi_S(R)/S,  y=psi_S(R)
```

give `V=−c mod f²` and `V=−R mod c`. The first uses
`S²=−Delta mod f²`, the second uses `c|S`; `f²=1 mod c`. Hence
`T=(V+c+f²*R)/(c*f²)` is a positive integer, the literal V definition
holds, and the auxiliary factor is 1. All 14 shifted inputs are positive,
and all five normalized factors are 1, giving a full zero of the 64-gate
toy-port candidate.

For the same other coordinates, the original 65-gate equation would require
its first factor to be 1, hence its first trace to be `+tau` or `−tau`.
The positive trace would require `E*n=N`, impossible because `E` does not
divide N. The negative trace would require `E*n=−tau−k+R<0`, impossible
for positive n. This rules out the natural same-other-coordinates repair;
it does not settle unrestricted existential equivalence.

The standalone checker pins and edits the original graph, verifies liveness,
scalar identities, residue and dominant-exponent arithmetic. It does not
expand the enormous Pell values or independently prove the unbounded Pell
facts. Independent external review is recorded in
`../../reviews/current14-carrier64-free-en-toy-zero-independent/`.

```
python3 -I -S -B research/current14-carrier64-free-en-toy-zero/check.py > /tmp/free-en-toy.json
cmp /tmp/free-en-toy.json research/current14-carrier64-free-en-toy-zero/result.json
```
