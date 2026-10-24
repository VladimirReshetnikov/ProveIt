# Monic transport elimination and a rank register

Comparison/source snapshot:
`cf4a5218a5a4e4358d3f5314151b6b05d4aa384e` of ProveIt.

This component uses the exact calibrated integer source, determinant guard,
residue orientation, rank-adapted CRT and nearest-square pairing proved in
the main report. It supplies only exact integral coordinate changes and
monic eliminations after that source. No further consistency assumption,
native coefficient change or new machine interpretation is introduced.

## 1. Fixed coefficient binding

The native ports `beta,K0,MC,MF` are the complete source-34
`mixed-parity-unrounded-1064921` tuple. In particular beta=2^1064921-1,
and MF is the shifted mask. All four ports must be kept together. The
determinant uses the fixed integers

```
cone_A=2^1113, cone_B=2^666104.
```

All six actual numerals are supplied in `../coefficients/payloads`, with
the binding in `../coefficients/BINDING.json`. They are coefficients,
not six additional unknowns. No number is chosen by waiting for a halt.

## 2. Transport is monic after the right coordinate change

The old coordinates include F,alpha,z and the abbreviation C=q-F-alpha.
Replace alpha by a free integer C, with inverse alpha=q-F-C. For fixed q
and F this is an integral affine bijection. The transport residual is

```
(K0+W)C-F-z(q-1).
```

Consequently one may eliminate F and that residual by

```
F=(K0+W)C-z(q-1).
```

The eliminated coordinates F and alpha are integers for every integer
assignment of the remaining coordinates. Restoring them reconstructs the
original transport equation exactly. Conversely every old zero has exactly
this value of F, so forgetting F is inverse to restoration. All other
residuals, including the determinant guard, are substituted as well.

The old rank expression simplifies by the exact identity

```
((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J
 = (q(q-F)-C)(q^2-1)+(MC+q MF)J,
```

when alpha=q-F-C. This is not division by a parameter or a rational
reconstruction. It is a polynomial identity over the integers.

Applied to the specified source packets, this gives the exact counts
24/10, 22/16, 19/28, 18/32 and 17/88, where each pair means number of
unrestricted integer unknowns / total degree of the single SOS polynomial.
The last two equations have six and five residuals, respectively.

## 3. Complete compact 20-variable degree-20 specification

For ease of reading, rename the twenty independent integer coordinates as

```
j, C, z, f, h, r, v, w, t, eta, y, gamma, T, E, c, s, p1, p2, p3, R.
```

Here t is the centered first Pell root, y the auxiliary root gap, s the
nearest-square witness, and R a native-rank register. The machine-readable
packet uses J3,C_native,v_scale,w3,tau,y_gap,pair_root,pair_pos1/2/3 and
R_register for the corresponding names.

Use only the following finite polynomial abbreviations:

```
J=3j+1, q=beta J+1, W=4(3w+1),
F=(K0+W)C-z(q-1),
X=qW, Y=(2v+1)q^3,
R0=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
a=E+Y, H=4a+3, Delta=a^2+H,
k=R+1+hE,
D=X+ac+H gamma,
I=(2r+1)c^2,
V=fcT-f^2 R-c,
G=cone_A F cone_B C-(q-cone_A F-cone_B C)^2,
Z=eta(k-eta),
Pos(p1,p2,p3)=1+p1^2+p2^2+p3(p3+1).
```

The eight residuals are

```
r1=R-R0,
r2=E-XY,
r3=c-kY-eta,
r4=t^2+(2t-k)E(c-eta)-1,
r5=D^2-Delta c^2-1,
r6=I^2-Delta(f^2-1),
r7=V^2+(1-I^2)y(2V+y)-1,
r8=GZ-(s^2-G-Z+1)^2-Pos(p1,p2,p3).
```

The promised single equation is `r1^2+...+r8^2=0` over unrestricted
integers. Every abbreviation is polynomial, and all powers are fixed
natural exponents. There are exactly twenty unknowns.

## 4. Exact zero-set correspondence for the rank register

Before adding the register, the 19-variable degree-28 source substitutes
R0 everywhere as R. Given any source zero, set the new coordinate R=R0.
Every displayed residual then vanishes. Conversely the first residual of
any new zero forces R=R0, so the remaining residuals are exactly the old
ones, with their previous abbreviations restored. Forgetting R therefore
gives a bijection of integer zero sets.

This use of a register lowers degree because R0 has degree five while R
is a coordinate of degree one. In particular k now has degree two and
V degree three. It does not introduce a hidden constraint or alter the
semantics of the CRT lemma.

Composing this bijection and the transport bijection with the main
report's finitary equivalence gives

```
ZFC proves: (there is no integer zero of this polynomial) iff Con(ZFC).
```

The inherited native/Pell/refutation calibration is explicit in that
composition. The present scripts do not claim a new proof-assistant
certificate of this full theorem.

## 5. Exact degree

With the six fixed numerals assigned degree zero and the twenty unknowns
degree one, the residual degree upper bounds in order are

```
5, 6, 6, 4, 10, 10, 10, 8.
```

Thus the SOS degree is at most twenty. In r7, the term
`8 r^2 c^4 y f^2 R` has degree ten. Squaring produces

```
64 r^4 c^8 y^2 f^4 R^2.
```

No other residual contains y. Within r7, obtaining r^4 in its square
requires choosing the r^2 terms from both factors; obtaining y^2 then
requires the linear-y term from both. The f^4 R^2 coefficient in V^2
is one. Therefore the displayed coefficient in the full SOS is exactly
64, establishing exact degree twenty independently of all fixed ports.

For the other five packets, the included certificates prove the listed
upper bounds and a nonzero leading coefficient after the actual six-port
specialization. The independent checker calculates that coefficient by
finite differences, using `Delta^d p(0)=d! [t^d]p(t)` modulo a prime.
This is exact coefficient verification under a proved degree bound, not
random sampling. The absence of cancellation among highest real
homogeneous squares then gives the exact SOS degree.

## 6. Proof scope and reproducibility

The paired positivity guard is the explicitly reused nearest-square lemma
of package 68. The determinant is the package-71 guard on the source-34
canonical witness family. The residue orientation is package 70's signed
power-recovery construction. The new CRT compression uses the preliminary
strong-rank fact p|m, before the auxiliary theorem identifies p=R; this
order is explained in the main mathematical audit and avoids circularity.

The complete packet is an ordinary fixed polynomial even though its
degree-88 sibling is kept as a finite factored DAG. Expansion is not a
mathematical requirement. The six variable counts, all definitions and
residuals, coefficient hashes, parent hashes, exact degree certificates,
builder and independent checker are supplied. No global minimality or
worldwide priority claim is made.
