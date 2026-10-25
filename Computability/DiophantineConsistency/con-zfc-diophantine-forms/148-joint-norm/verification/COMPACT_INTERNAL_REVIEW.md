# Internal mathematical review: staged recovery of the main square

Reviewed construction: `compact_agent/staged_main/equation78_degree454.json`
and the formulas in its `PROOF.md`, 25 October 2026.

This is an independently conducted AI-assisted review within the current
collaboration, not external human peer review. The review checks the new
root-recovery order, its strong-Pell and auxiliary interfaces, the transport
estimates affected by removing doubling, constructive completeness, and the
highest homogeneous component. The entire transitive native/K215 formal
development was not rerun.

## Conclusion

No substantive mathematical defect was found in the new transformation.
The proof correctly delays recovery of the first Pell square until after
the main ordinate has been recognized. It does not silently assume the
coprimality of `E` and `Dm`, and it does not assume that the strong pair has
been doubled.

Two minor explicit inequalities improve the exposition: `Q>c^2` in the
exclusion of `b=0`, and `F2>S`, hence `F2>g`, in the transport estimate.
Both follow at once from the supplied definitions; they are not additional
hypotheses or new constraints.

## 1. Coprimality and the order of recovery

Set `S=E*Dm`, `U=i*A*c^2`, `a=Delta*U^2*S`, `F2=1+a`,
`Q=Delta*a`, and `G=S*F2`. The proposed polynomial zero gives

```
(Q-1)z^2=G(QV^2-1),      z=Z/M in Q.
```

For primes dividing `S`, both factors on the right other than `G` are
units because `Q=0 mod S`. The other coprimality identities are

```
gcd(S,F2)=1,
Q-1=Delta*F2-A^2,
F2=1 mod A,
QV^2-1=-Dm mod F2,
F2=1 mod Dm.
```

Thus `gcd(G,(Q-1)(QV^2-1))=1`. Rational valuations imply that `G` is a
positive integer square. The coprime positive factors `S` and `F2` are
individually squares, say `S=sigma^2` and `F2=f^2`. This inference needs
no statement about `gcd(E,Dm)`.

The integral ordinate `I=U*sigma` now satisfies

```
f^2-Delta*I^2=1,        Q=(Delta*I)^2,        c^2|I.
```

After the adjacent norm has an integral second coordinate, the parent's
all-index folding argument identifies `c=psi_A(p)` for a positive odd
index `p`. Only then is

```
Dm=1+Delta*c^2=chi_A(p)^2
```

known to be a square. The relation `S=E*Dm=sigma^2` makes `E` a rational
square; since `E` is an integer, it is an integer square. This ordered
reasoning is noncircular.

## 2. The rational adjacent-norm descent

For a reduced rational `y=r/m` satisfying

```
Qv^2-(Q-1)y^2=1,      v in Z, |v|>=1,
```

one has `m^2|Q-1`. With `v>1` and `y>0`, the inequalities
`v<y<Qv/(Q-1)` imply that

```
v'=(2Q-1)v-2(Q-1)y,
y'=(2Q-1)y-2Qv
```

has integral, nonzero `v'` with `|v'|<v`. The transformation preserves
the norm. Its second coordinate has the same reduced denominator `m`
because `2Q-1=1 mod m`. Absolute-value descent ends at `v=1,y=1`, so
`m=1`. The supplied proof uses this descent correctly before claiming
that the rational carrier `z` is integral.

## 3. Folding does not need a doubled strong pair

Write `f=chi_A(m)` and `I=psi_A(m)`. Classifying the adjacent norm at
`Delta*I` produces an odd auxiliary index `j`. The quotient identity for
odd traces and `V=-c mod f` give `psi_A(j)=+c or -c mod f`.

Reduction modulo `2m` and reflection give an odd `p` in `[0,m]` with
`psi_A(p)=+c or -c mod f`. Both `psi_A(p)` and `c` are at most
`I<f/2`, so the congruence cannot wrap; its negative case cannot occur,
and `psi_A(p)=c`. The proof needs no parity assumption on `m` and no
identity obtained only after Pell doubling.

## 4. Changed transport estimates

The supplied definition gives

```
a^2/g^2 = Delta*U^2*a/(1+a) > Delta*U^2/2 > 36.
```

Hence `a>6g`. Also `Q>c^2`, `a>2c`, and `F2>S`, all directly from
`U>=A*c^2`, `Delta=A^2-1`, and the positive domain. Therefore the
case `b=0` contradicts integrality of
`y^2-c^2=(c^2-1)/(Q-1)`; otherwise `b` and `V` have the same sign,
`|V|>3g`, and `F2>g`.

The main-index-3 exclusion remains valid. Its exact eta expression
forces `2Y-X` to be either 1 or 2, whereas both `X` and `Y` are multiples
of `q>=32`. Thus the main index is at least 5. The auxiliary index cannot
be 1 or 3, using the unchanged congruence `V=F2*b-c` and the identity
`Q=Delta*(F2-1)`. Its index is therefore at least 5, giving
`|V|>8Q^2`, `|b|>4F2>4g`, and `gy<(3/8)bV`.

These inequalities justify positivity of the transport weight `L=bV`
before the carrier is used to force `B>=0`. No sign of `B,C,R,b,V`, or
the transport quotient is assumed in obtaining that conclusion.

The subsequent normalized-rank and signed auxiliary-index lemmas apply:
their retained hypotheses are `c^2|I`, `c=psi_A(p)`, `c>2p`, `c>2R`,
`V=-c mod f`, and `V=-R mod c`. The copied
`inherited/proof_sources/universal_pell.tex` explicitly states them without
a doubling hypothesis.

## 5. Constructive completeness

After the canonical outer data determine `tau,d,A,c`, choose a positive
power of the Pell matrix `[[A,Delta],[1,A]]` which is the identity modulo
`A*c^2*tau*d`. Such a power exists because the matrix has determinant one
and is invertible in a finite matrix group. Its ordinate `I` is divisible
by that modulus, so `i=I/(A*c^2*tau*d)` is a positive integer.

This realizes the exact new strong pair, not a substituted old pair:
`I=U*tau*d`, `F2=f^2`, and `G=(tau*d*f)^2`.

The retained positive auxiliary reconstruction lemma assumes only
`R=3 mod 4`, `c=psi_A(R)`, the positive strong norm, and `c|I`. Its
congruences are modulo `f^2`, so it gives the stated positive integer
`T=(Vstar+c+R*f^2)/(c*f^2)` for the undoubled pair. There is no hidden
constraint on the strong index or on an odd multiplier.

The final `n` is positive because the supplied bounds give `g>kappa`,
while the remaining canonical terms are nonnegative. This closes the
positive existential converse.

## 6. Independent highest-degree calculation

Let `q0=beta*J` and `k0=eta+zeta`. The leading pieces are

| Register | Leading homogeneous piece |
|---|---|
| `A` | `w*q0^4*s` |
| `Delta` | `w^2*q0^8*s^2` |
| `c` | `k0*q0^3*s` |
| `E`, `Dm` | `k0^2*w^2*q0^14*s^4` |
| `S` | `k0^4*w^4*q0^28*s^8` |
| `U` | `i*k0^2*w*q0^10*s^3` |
| `a`, `F2` | `i^2*k0^8*w^8*q0^56*s^16` |
| `Q` | `i^2*k0^8*w^10*q0^64*s^18` |
| `G` | `i^2*k0^12*w^12*q0^84*s^24` |
| `V` | `i^2*k0^9*w^8*q0^59*s^17*T` |
| `M` | `4*w^2*q0^9*s^2` |

The unique highest-degree summand of the final polynomial is
`-Q*M^2*G*V^2`. Multiplying the displayed pieces gives exactly

```
[P]_454 = -16*q0^284*w^42*s^80*i^8*k0^38*T^2.
```

Its degree is `284+42+80+8+38+2=454`, and a selected nonzero coefficient
is `-16*beta^284`. Thus degree attainment is independent of the other
fixed ports. The remaining final summands have lower degree, so they
cannot cancel this leading component.

The circuit-cost and coefficient-payload claims still require the separate
finite DAG and byte checks; this mathematical review does not replace them.
