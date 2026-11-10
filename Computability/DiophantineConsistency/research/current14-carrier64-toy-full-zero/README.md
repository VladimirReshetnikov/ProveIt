# A symbolic full candidate zero at different ports

The 64-gate candidate has a **positive integer zero** at the toy ports
`(beta,K,MC,MF)=(31,1,22,43)`, with no old positive scalar repair preserving
the same `q,R,w`. These are **not the current fixed ports**. The construction
does not disprove fixed-current-port reverse existence, nor rule out an old
zero with different coordinates or rank. Its huge integers are specified
symbolically and are not expanded by the checker. The argument is ordinary
external mathematics, not a new Lean theorem.

## Scalars and the two main Pell factors

Set

```
q=32, J=1, F=2, C=577, G=q(q-F)-C=383,
R=G(q²-1)+MC+q*MF=393207, N=(R-1)/2=196603,
X=2^R, w=2^(R-5), M=K+w,
z=1+(M*C-F)/31.
```

`R=3 (mod 4)` and `popcount(R)=17`. Since `w=4 (mod 31)` and
`C=19 (mod 31)`, the displayed `z` is a positive integer and transport is
exactly 1. All four toy ports meet the usual boxes, parity and complementary
population conditions: `MC mod4=2`, `(MF-beta) mod8=4`,
`popcount(MC)+popcount(MF-beta)=5`, and `MC+(MF-beta)>beta`.

Define the integer

```
Y = (1/2) * sum_{i=0}^N binom(2N,i)*X^(N-i),
s=Y/32³, E=XY, m=EY, a=E+Y, H=4a+3, Delta=a²+H.
```

The central-binomial argument in `../current14-carrier64-pell-floor/` gives
`v2(Y)=popcount(N)-1=15`, so `s` is a positive odd integer. The same
elementary ratio bounds apply to this explicitly chosen `Y`: it lies strictly
between `X^N/2` and `X^N`, and for

```
k=2*psi_(2m+1)(N+1),   tau=chi_(2m+1)(N+1),
c=psi_(a+2)(R),          D=chi_(a+2)(R),
```

they give `Y<c/k<Y+1`. Thus `eta=c-Yk` and `zeta=k-eta` are positive.
The first Pell congruences give `tau=1 (mod E)`,
`k=2(N+1)=R+1 (mod E)`, and `tau>k`; hence
`n=(tau-k+R)/E` is a positive integer and the first norm is 1.

The main norm is 1 by its Pell definition. With `psi_0=0`, `psi_1=1`, and
`T_r=2*psi_r-psi_(r-1)` (using `psi_(-1)=-1`), the main recurrence gives
`T_(r+1)=2*T_r+H*psi_r` and `T_0=1`. Therefore

```
D-a*c = 2^R + H*gamma,
gamma=sum_{j=1}^{R-1} 2^(R-1-j)*psi_(a+2)(j) > 0.
```

Because `X=2^R`, this is exactly the graph's main carrier.

## Strong and auxiliary norms

Let `(f,L)` be the coefficients of the c-th power of the main Pell unit:

```
f+L*sqrt(Delta) = (D+c*sqrt(Delta))^c.
```

Then `f²-Delta*L²=1`, and `c²|L`: the linear binomial term has coefficient
`c*c`, while every higher odd term contains at least `c³`. Put `i=L/c²`
and `S=Delta*L`. Both are positive; the graph's strong factor is `Delta`.

Define `(x_aux,y)` by the R-th Pell power

```
x_aux+y*sqrt(S²-1) = (S+sqrt(S²-1))^R,
V=x_aux/S.
```

`R` is odd, so `x_aux` is divisible by `S` and `V` is a positive integer.
The auxiliary norm is then 1. The following congruences supply its graph
coordinate `T`:

```
V = -c (mod f²),       V = -R (mod c),       f² = 1 (mod c).
```

For the first, `S²=Delta*(f²-1)`, hence
`1-S²=(a+2)² (mod f²)`. The polynomial identity

```
T_(2N+1)(S)/S = (-1)^N U_(2N)(sqrt(1-S²))
```

has an even right-hand polynomial, so it is valid modulo `f²` without
choosing a square root. Here `N` is odd and `U_(2N)(a+2)=c`. The second
congruence follows from `S=0 (mod c)` and the constant coefficient
`T_R(S)/S=(-1)^N R (mod S²)`; the third follows from `c²|L`. Define

```
Q=(V+c)/f²,       T=(R+Q)/c.
```

The congruences make `Q,T` positive integers and give
`f²*(c*T-R)-c=V`. Thus all four normalized norm factors and transport are
1; the literal candidate output is `1*1*1*1*Delta-Delta=0`.

The Chebyshev identity follows from the common recurrence in `v=S²`,
`Q_(n+1)=(4v-2)Q_n-Q_(n-1)`, with `Q_0=1`, `Q_1=4v-3`; its constant
coefficient is `(-1)^n(2n+1)`. The checker validates small exact polynomial
instances and small complete strong/auxiliary Pell instances as controls.

## Why the restricted old repair fails

The direct old coordinate would be `alpha=q-F-C=-547`. The only old
positive scalar tuple with the same `q,R` has, by Euclidean division,
`F0=20`, `alpha0=11`, `C0=1`. Since `M=5 (mod 31)`, its transport
would require `M*C0-F0` divisible by 31, but it is `-15 (mod 31)`.
Thus no old positive zero can share this `q,R,w`; another old zero with
different coordinates is not excluded.

The checker verifies the finite scalar facts, population, modular transport,
the old restricted obstruction, Chebyshev polynomial controls, small Pell
controls, and 50 modular graph-transcription controls. It does **not** expand
or numerically evaluate the full symbolic witness, invoke Lean, or connect
these toy ports to the current PDF or current native certificate.
The independent external review is in
`../../reviews/current14-carrier64-toy-full-zero-independent/`.

```sh
python3 -I -S -B research/current14-carrier64-toy-full-zero/check.py > /tmp/carrier64-toy-zero.json
cmp /tmp/carrier64-toy-zero.json research/current14-carrier64-toy-full-zero/result.json
```
