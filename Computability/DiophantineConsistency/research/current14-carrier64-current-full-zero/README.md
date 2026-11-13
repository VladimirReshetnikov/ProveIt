# Symbolic 64-candidate zero at the current ports

The independently reviewed external construction below specifies a positive
integer zero of the conditional 64-gate candidate at the
four current symbolic port integers. Its enormous witness is not expanded or
numerically evaluated. It does not exhibit a zero of the maintained 65-gate
equation, prove that equation has no zero, or by itself decide whether the two
equations have equivalent zero *existence*. No new Lean proof, PDF-byte
interpretation, native proof replay, or closed provider ancestry is claimed.

The proof uses the independently reviewed general Pell/floor and Chebyshev
identities in `../current14-carrier64-pell-floor/` and
`../current14-carrier64-toy-full-zero/`. The finite checker here authenticates
the current graph and all four raw/compressed port payloads, reconstructs the
scalar integers below, and verifies the specified modular inverse and bounds.
It does not numerically evaluate the complete symbolic witness.
The independent external review is in
`../../reviews/current14-carrier64-current-full-zero-independent/`.

## Fixed scalar coordinates

Write `beta=2^B-1`, `B=94517`, `q=beta+1`, `lo=MC`, `hi=MF-beta`, and set

```
J=1,
G=q*(hi-1)+lo+1,
R=(G+1)*q²-1,
N=(R-1)/2,
w=2^(R-B),
F0=q-hi,       C0=beta-lo,       alpha0=lo+hi-beta.
```

The actual byte checks establish `lo mod4=2`, `hi mod8=4`,
`popcount(lo)+popcount(hi)=B`, `lo+hi>beta`, and the usual positive port
box. Consequently `popcount(G)=B+2`, `popcount(R)=3B+2`, `R=3 (mod 4)`,
and `popcount(N)=3B+1`. The finite computation confirms these properties;
`R` has bit length 330831. The triple `F0,alpha0,C0` is the unique old
positive scalar representation of `G` at this `q`.

The full `w` is not materialized. Since `beta=2^B-1`, its residue is

```
e=(R-B) mod B = 54265,    w mod beta = 2^e.
```

Put `Mbar=(K+2^e) mod beta`. The checker verifies
`gcd(Mbar+1,beta)=1` and defines the unique residue

```
d = (F0-Mbar*C0) * inverse(Mbar+1) mod beta,
```

using the representative `0<=d<beta`. It verifies `0<d<F0`; `d` has
94514 bits and SHA-256
`57379339931be15b25510d19cbf4b903f5cddd8f2fd9e683372d2e44b0a2487e`
in minimal unsigned big-endian encoding. Now define

```
F=F0-d,   C=C0+q*d,   z=1+((K+w)*C-F)/beta.
```

The modular equation makes `z` an integer. It is positive because
`R>=2B` gives `w>=q>F` and `C>0`. The exact identities

```
q*(q-F)-C=G,                  (K+w)*C+(q-F)-z*beta=1
```

make the candidate gap and transport correct. The direct old coordinate
would be `alpha=q-F-C=alpha0-beta*d<0`: `0<alpha0<beta` and `d>=1`.
The old scalar triple above also has no positive transport repair at this
same `q,R,w`, since the checker verifies `(Mbar*C0-F0) mod beta != 0`.

## The symbolic Pell coordinates

Set `X=2^R` and define the finite integer

```
Y = (1/2) * sum_{i=0}^N binom(2N,i)*X^(N-i),
s=Y/q³, E=XY, m=EY, a=E+Y, H=4a+3, Delta=a²+H.
```

The reviewed central-binomial valuation gives
`v2(Y)=popcount(N)-1=3B`, so `s` is a positive odd integer. The purely
algebraic floor estimates in the reviewed Pell-floor packet apply without
assuming a full zero: the first two head terms give `Y>X^N/2`, while
`Y<(X+1)^(2N)/(2X^N)<X^N`. Define

```
k=2*psi_(2m+1)(N+1),     tau=chi_(2m+1)(N+1),
c=psi_(a+2)(R),           D=chi_(a+2)(R),
eta=c-Y*k, zeta=k-eta,    n=(tau-k+R)/E.
```

Here `chi_p(j)+psi_p(j)*sqrt(p²-1)=(p+sqrt(p²-1))^j`. The floor
estimates give `Y<c/k<Y+1`, so `0<eta<k` and `eta,zeta` are positive. The first Pell
congruences give `tau=1`, `k=R+1 (mod E)` and `tau>k`; thus `n` is a
positive integer and the first norm is 1. The main norm is 1. Its projection
identity gives

```
gamma=(D-X-a*c)/H
     =sum_{j=1}^{R-1} 2^(R-1-j)*psi_(a+2)(j)>0,
```

so the main carrier is exact.

For the remaining witnesses, take the `c`-th main-unit power

```
f+L*sqrt(Delta)=(D+c*sqrt(Delta))^c,
i=L/c²,    S=Delta*L.
```

The binomial expansion gives `c²|L`, and the strong norm equals 1. Take the
`R`-th auxiliary Pell power

```
x_aux+y*sqrt(S²-1)=(S+sqrt(S²-1))^R,    V=x_aux/S.
```

Because `R` is odd, `V` is a positive integer and the auxiliary norm equals
1. Since `R=3 (mod 4)`, the reviewed Chebyshev congruences in the toy packet
give `V=-c (mod f²)` and `V=-R (mod c)`; also `f²=1 (mod c)`. Therefore

```
Q=(V+c)/f²,       T=(R+Q)/c
```

are positive integers and make the graph's auxiliary expression exactly `V`.
All five normalized factors are 1, the unnormalized strong factor is
`Delta`, and the 64-gate candidate output is zero.

## Reproduction and limits

```sh
python3 -I -S -B research/current14-carrier64-current-full-zero/check.py > /tmp/carrier64-current-zero.json
cmp /tmp/carrier64-current-zero.json research/current14-carrier64-current-full-zero/result.json
```

The 64-gate candidate is not the maintained `equation.tex`/PDF: it replaces
`alpha` by a positive `C` coordinate. This external construction does not
establish that the maintained 65-gate equation has or lacks a zero, and it
does not prove any inconsistency of ZFC.
