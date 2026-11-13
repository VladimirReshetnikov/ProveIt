# Proposed completion of the symbolic carrier by a coupled Pell orbit

**Unverified construction strategy.** This note proposes how the scalar
candidate in the [carrier CRT note](../trace74-symbolic-carrier-crt/README.md)
could be extended to satisfy the *full* 74-operation graph equation at the
retained external ports, while violating the reverse guard. It is not yet
an independently accepted proof, a Lean theorem, or a checked full graph
zero. The symbolic witness is far too large for the finite checker here to
materialize. The external fixed-port payload also remains separate from a
Lean binding to symbolic ports. A failure in any of the conditional inputs
or steps below invalidates the proposed construction.

## Starting assumptions and notation

Take the sibling scalar candidate and CRT choice, including all its
explicit Pell interval and exact gcd assumptions:

```text
q=2^590069, h=q−1, J=1, F=1,
X=2^r, Y=q³, r=3056651345 ≡ 1 (mod 4),
k=eta+zeta, c=kY+eta,  eta>0, zeta>0,
R<0, C=q(q−1)−G>0,  Breg=(K0+X/q)C−1>0,
e=k−R−1, D=XY, H=4Y(X+1)−1,
Kreg=X(3c−2X)+2, M=hDH,
D|e, h|Breg, H|Kreg, and R≡−r (mod c).
```

The previous note derives the divisibilities by CRT using the external
hash-pinned `K0` and finite modular gcd checks. It establishes `M|Z` for
the graph carrier expression once the remaining coordinates are chosen;
it does **not** establish the graph equation. All quantities in this note
are ordinary integers, and all introduced witness coordinates must be
positive. Put `z=Y(X+1)+1`, `Delta=z²−1`, and define Pell coordinates
`x_j,y_j` by `(x_j+y_j√Delta)=(z+√Delta)^j`.

The already chosen first ordinate makes the graph's `E=1+XY²(XY²+1)k²`
a positive square; let its positive root be `tau`. The main ordinate is
`c=y_r` for this same base `z`.

## Selecting the strong Pell factor

Let `m=c² tau` and take `t0=(m²)!`. The Pell recurrence matrix has
determinant one modulo `m`; its orbit of `(1,0)` has a positive period
at most `m²`, which divides `t0`. Thus `m | y_t0`. Put `t=c t0`.
The Pell addition formula gives
`y_t0 | y_t`, so `c|t` and `c² tau|y_t`. Define

```text
i = y_t/(c² tau) > 0,  phi=x_t,
f=x_(2t)=2 phi²−1,  I=y_(2t),  S=Delta I.
```

Since `E=tau²` and `y_t=i c² tau`, the actual graph registers satisfy

```text
a=Delta i² c⁴ E = phi²−1,  F0=a+1=phi²,
f=1+2a,                    Q=Delta(f²−1)=S².
```

Also `f≡1 (mod c)` because `c|y_t`, and hence `gcd(f,c)=1`.

## Odd auxiliary orbit and congruences

Choose any positive odd integer `s`, set `u=r+4ts`, and put

```text
V0 = T_u(S)/S,     yaux = U_(u−1)(S),
```

where `T` and `U` are the Chebyshev polynomials defined over the integers
by `T_0=1,T_1=S,T_(j+1)=2S T_j−T_(j−1)` and
`U_0=1,U_1=2S,U_(j+1)=2S U_j−U_(j−1)`. Since `u` is odd, `T_u(S)` is
divisible by `S`; `V0,yaux` are positive. The Pell norm identity gives

```text
S² V0² − (S²−1)yaux² = 1.                              (1)
```

The following two congruences are the critical proposed bridge:

```text
V0 ≡ −c (mod f),        V0 ≡ r (mod c).                (2)
```

For the first, `S²+z²−1=Delta f²`, so `S²+z²≡1 (mod f)`. For every
odd `u=2j+1`, the polynomial identity modulo `S²+z²−1` is

```text
T_(2j+1)(S)/S ≡ (−1)^j U_(2j)(z).                      (3)
```

It follows by induction on `j`: both sides satisfy the same recurrence
modulo `S²+z²−1`, and their first two terms agree. More explicitly, the
odd `T` quotients obey `P_(j+2)=(4S²−2)P_(j+1)−P_j`; the signed odd
`U` ordinates obey the same recurrence after substituting `z²≡1−S²`.
Their initial values are `1` and `4S²−3`, respectively.

The main Pell addition formula gives
`x_(4t)=2f²−1≡−1 (mod f)` and `y_(4t)=2fI≡0 (mod f)`, hence
`y_u≡(−1)^s y_r≡−c (mod f)` for odd `s`. Because `r≡1 (mod 4)`,
also `(u−1)/2` is even, so (3) gives `V0≡−c (mod f)`.

For the second congruence, `c|t` makes `c|I=y_(2t)` and therefore
`c|S`. The linear coefficient of `T_u(S)/S` is
`(−1)^((u−1)/2)u`; with the same even parity and `u≡r (mod c)` this
gives `V0≡r (mod c)`.

## Choosing the two remaining coordinates

Since `R≡−r (mod c)` and `f≡1 (mod c)`, (2) gives
`V0+c+fR≡0` modulo both coprime integers `f,c`. Thus

```text
T = (V0+c+fR)/(f c)
```

is an integer and satisfies the actual graph identity
`V=f(cT−R)−c=V0`. With all earlier parameters fixed, increasing odd
`s` makes `u` and `V0` unbounded, so `T>0` eventually.

Define the integral constant

```text
N0 = [hD Kreg − H(DBreg+h e)]/M.
```

Its integrality follows from `H|Kreg`, `h|Breg`, and `D|e` as in the
carrier CRT note. Choose the graph's eighth witness (index 7) to be

```text
v7 = V0² Breg − N0 + tau phi yaux.
```

One explicit sufficient choice is the odd integer
`s=2(f|R|+|N0|+1)+1`. Since `S≥2`, the odd Pell quotient satisfies
`V0≥2^(u−1)≥u≥s`: its abscissa `T_u(S)` is at least `S^u` by the
positive Pell recurrence. This makes `T>0` and, using `Breg≥1`, makes `v7>0`.
The actual carrier formula then gives
`Z=M tau phi yaux`. Substitution into the exact graph identity

```text
value74 = (Q−1)Z² − M²(E F0)(QV²−1)
```

would give zero by `Q=S²`, `E F0=tau² phi²`, `V=V0`, and (1). Together
with the earlier positive `J,F,C,w,eta,zeta`, the constructed positive
`i,T,v7` would be a full positive witness with `F+C≥q`.

The chart identity is the all-ring `Trace74Mask.coordinate_identity`:
evaluate the 75-register formulas at `alpha=q−F−C`, even though this
synthetic `alpha` is negative here. In those formulas the old `C` register
then equals the new positive `C`, and the old rank factor
`h(q−F)+alpha` equals `q(q−F)−C=G`. Thus the displayed `R`, `Breg`,
`Z`, and `M` are the actual 74-register values. No positive-old-chart
assumption is used in this ring identity. This coordinate transcription
and the correspondence to the separately retained external graph remain
subject to independent checking.

This last paragraph is the **proposed conclusion**, not a certified
result. In particular, the chain from the exact fixed payload and sibling
Pell interval through all displayed identities, divisibility, signs,
coordinate interpretations and the final value needs independent review.
If established, this would refute the universal reverse guard and show
that its guarded coordinate map is not defined on every positive 74 zero.
It would not by itself refute positive-existence equivalence of the 74 and
75 graphs, prove that the 75 graph has no zero, or decide ZFC consistency.

Run `python3 -I -S -B research/trace74-symbolic-coupled-pell-strategy/check.py`
from `Computability/DiophantineConsistency` for a small diagnostic of
the odd-Pell congruence and CRT compatibility. That example uses an
artificial small Pell base; it is **not** a full graph witness or a check
of the huge symbolic instance.
