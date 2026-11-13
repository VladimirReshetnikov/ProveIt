# The factors 1, 3 and 9 persist in fixed-mask partial data

At the **actual fixed compact44 beta and masks**, transport, the quartic rank
window and the free-carrier equality do not by themselves force `e=1` or
`U|h`. The three explicit partial assignments below realize
`e=gcd(U,H)=1,3,9`. In the last two, `h=U/e` is positive but `U` does not
divide `h`. This is an external integer argument about partial assignments;
it does not rule out additional constraints imposed by an actual 72-graph
zero. In fact, the displayed assignments are deliberately **not** zeros.

## Fixed ports and assignments

Take exactly

```
beta = 2^590069−1,
MC = CompactSymbolicPorts.lowNat,
MF = beta + CompactSymbolicPorts.highNat.
```

These are the fixed compact44 beta and mask ports. The checked
[`CompactSymbolicMaskData.data`](../../Lean/DiophantineConsistency/Compact44/CompactSymbolicMaskData.lean)
supplies `0≤MC<beta` and `0<MF<2beta` in standard arithmetic. Choose one
row of

| `J` | `s` | `w` | `e` |
| --- | --- | --- | --- |
| 1 | 1 | 1 | 1 |
| 2 | 1 | 1 | 3 |
| 1 | 3 | 3 | 9 |

and define the remaining quantities by

```
q = beta*J+1, K = q−w, F=1, alpha=q−2, z=1,
Y=q³s, X=wq, U=Y², a=XY+Y, H=4a+3,
eta=zeta=t=f=i=T=y=1, k=2, c=2Y+1,
e=gcd(U,H), mu=U/e, h=mu, g=X+a c+H/e.
```

`K` is the arbitrary natural kernel port; all 14 displayed graph coordinates
are positive. In particular, `q>w` and `q≥33` because beta is much larger
than 67. These definitions are symbolic; neither the enormous fixed masks
nor the full graph numbers need be expanded.

## Exact proof

`590069≡5 (mod 6)` and the period of powers of 2 modulo 9 give
`beta≡4 (mod 9)`. The three rows yield the following exact residues:

| Row | `q mod 9` | `Y mod 9` | `H mod 9` |
| --- | --- | --- | --- |
| `e=1` | 5 | 8 | 6 |
| `e=3` | 0 | 0 | 3 |
| `e=9` | 5 | 6 | 0 |

Every common divisor of `U=Y²` and `H=3+4(X+1)Y` divides 9, as in
[`P64Early.gcd_dvd_nine`](../../Lean/DiophantineConsistency/Compact44/P64Early.lean).
Thus the first row has gcd 1; the second has gcd exactly 3 because
`9|Y` but `H≡3 (mod 9)`; and the third has gcd 9 because `3|Y` and
`9|H`. In all three rows `e|U,H`, hence `mu` and `H/e` are positive
integers. The definitions give the free-carrier equation

```
U*g = U*(X+a*c)+H*h.
```

For the `e=3,9` rows, `0<h=U/e<U`, so `U` does not divide `h`.
This algebraic carrier equation does **not** assert the main Pell norm or
that the graph's main residual vanishes.

Transport holds because `C=q−F−alpha=1` and
`(K+w)C = q = F+z(q−1)`. Its rank is

```
R=(q²−q−1)(q²−1)+(MC+q*MF)J.
```

The fixed-mask inequalities give `(MC+q*MF)J<(q−1)(1+2q)`, so
`R+1<q⁴−q³+1<q⁴`. Thus the fixed ports, actual transport, quartic
window and free-carrier equality all hold for these partial assignments.

They are not graph zeros. With `eta=zeta=t=1`, the first graph residual is
`A0=1−(2P)(2P+2)≤−7`, where `P=XY²≥1`. For every integer auxiliary
residual `Na`, the unit factor `A0*Na−1` is nonzero, so the output sum of
squares is positive. The main, strong and auxiliary norm equations have not
been imposed. Therefore these examples cannot decide whether **actual**
positive 72 zeros force `U|h` or whether a different witness establishes the
reverse implication.

[`check.py`](check.py) verifies the modular certificates for the actual beta
without expanding it and exercises 132 complete DAG evaluations at analogous
small betas and mask bounds. Those finite controls are not actual fixed-beta
zeros. The exact symbolic argument above establishes the three partial
fixed-beta cases. Run `python3 -I -S -B check.py`; retained output is
[result.json](result.json). No Lean theorem is asserted.
