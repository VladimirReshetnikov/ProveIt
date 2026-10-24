# Independent audit of the simple saturated nine-positive finalizer

## Scope and inherited interface

This note verifies the new arithmetic finalizer for any inherited packing
prefix satisfying the same contract as package 66's H2082 source, or package
71's compatible source. It does not reprove the native Wang/Pell calibration.
The exact data defining `R`, `N`, and `cap` must be authenticated as a whole
and accompanied by that prefix's own bit-mask/carry proof.

The retained numerical ratio theorem has these properties. For the standard
registers below, a source zero gives positive witnesses `h,s,w,C` for which

```
a0 is a square,       C = psi_A(2R+1),       J divides Q,       m>0.
```

Conversely these conditions imply the appropriate binary-base and central
binomial divisibility conditions; combined with the prefix's carry test,
they yield a source zero. The published ratio theorem may formulate the
second condition by its older ProductPell certificate. Its equivalence with
`C=psi_A(2R+1)` under the recovered carrier range is exactly Jones's
ProductPell theorem. This note states explicitly where that conversion is
used; it does not silently alter a premise of `ratio_sound`.

Assume the prefix proves unconditionally, on positive inputs,

```
R,N >= 8,       b <= R,N,       cap>0,
```

and supplies the margin in the following normalization. All variables
`b,g,h,s,w,C,i,j,n` range over the positive integers. Every other symbol is
a polynomial abbreviation:

```
U=N^2 w,       Y=N^2 s,       M=R Y,
P=2 M^2 U,     K=R+1+h(P-1),  A=M(U+1),
B1=2R+1,       W=bw,          J=4A-5,
Q=3WC-2(W^2-1),
m=K^2(4cap-g)-16cap(C-KY)^2,
a0=(P^2-1)K^2+1,
D=(A^2-1)C^2+1,
r=i J C^2,
F=(A^2-1)D r^2+1,
L=CD+1-A,
G=A+F L,
H=C+F(B1+(j-1)C),
I=(G^2-1)H^2+1,
a1=D F I,
T=A D r,
V0=P K,        V1=T G H,
Omega=J m,     E0=J(n+W^2)+Q,
Theta=E0-Omega(V0+V1).
```

Define the ordinary polynomial

```
P9=(Theta^2-Omega^2(a0+a1))^2-4 Omega^4 a0 a1.
```

The claim audited here is that `P9=0` has a positive solution exactly when
the inherited source has one. No extra radicand scaling is needed.

## Unconditional bounds

First, `A` is large (`A>=33280` in the stated prefix range), `A>W`, and
`J>3A>0`. Also

```
A^2-P = M^2(U^2+1) >= 1.
```

Since `C>=1`, `D>=A^2`, `D>C^2`, and `D>A`. Thus `L>=C`, `F>D`,
`G>A`, and `H>1`. Both radicands `a0,a1` are strictly positive. We have

```
V0^2-a0 = K^2-1 > 0.
```

The exact new majorant identity is

```
T^2-D F = D(D r^2-1)>0.
```

Consequently

```
V1^2-a1 = D(D r^2-1)G^2H^2+D F(H^2-1)>0.
```

In particular `V0>sqrt(a0)` and `V1>sqrt(a1)` unconditionally. These
inequalities are established before recovering a positive margin or Pell
indices. Also `V1=A D r G H>4D`, using only `A>=2`, `r>=1`, `G>A`,
and `H>1`.

The linear final register is positive regardless of the sign of `Q`:

```
E0=Jn+(J-2)W^2+3WC+2>0.
```

## Soundness: recover the margin first

Suppose `P9=0`. If `m=0`, then `Omega=0` and `P9=E0^4>0`, a
contradiction. Over the reals the two-root norm factors into its four linear
factors. Therefore there are choices of signs for which

```
E0/J = m (V0+V1 +/- sqrt(a0) +/- sqrt(a1)).
```

The parenthesis is positive for every sign pair, by the unconditional
strict majorants. The left side is positive as well. Hence `m>0`.

The margin equation now implies both `g<4cap` and

```
|C-KY| < K/2.
```

As `Y=N^2 s>=64`, we obtain `C>2K`. Since
`K>=R+P` and `P>W`, this yields

```
C>2K>2R+1+W>B1.
```

Thus all required carrier-range premises of the inherited ratio theorem
and the saturated ProductPell theorem are available, without assuming them
at the start.

## Soundness: separate the roots and recover divisibility

Because `A^2-1>=P`, we have `D>P C^2`. With `F>D`, `I>=1`, and
`C>K>=1`, it follows that

```
a1 = D F I > D^2 > P^2 K^2 >= a0.
```

The signed radical sum

```
Theta/Omega = epsilon0 sqrt(a0)+epsilon1 sqrt(a1)
```

is rational and nonzero. Squaring and isolating one root therefore makes
both roots rational. A rational square root of an integer is an integer.
Thus `a0` and `a1` are integer squares.

The displayed norm-factor identity now reads

```
E0 = Jm(V0+V1+an integer),
```

so `J|E0` and hence `J|Q`. The saturated positive ProductPell theorem
from `SATURATED_POSITIVE_PELL_AUDIT.md` applies to the unchanged positive
`J`, odd `B1=2R+1`, and `C>B1`, yielding `C=psi_A(B1)`.

To apply a ratio theorem still phrased with the *old* certificate, use its
ProductPell completeness theorem to choose old positive `i_old,j_old` for
this same `A,B1,C,J`. The other ratio coordinates, margin and `Q` are
unchanged. Its combined congruence follows from `J|Q` and the old
`F_old|(H_old-C)`. The original numerical ratio-soundness theorem and the
prefix's carry proof therefore give a source zero. This reconstruction is
essential: division of the new `i` by `sqrt(D)` need not be integral.

## Completeness

Given a source zero, the inherited packing and ratio-completeness argument
supplies positive `b,g,h,s,w,C` with the four ratio conditions at the start.
Apply the saturated ProductPell completeness theorem to choose positive
`i,j` with `a1` a square. Let `z0,z1` be the positive integer square
roots of `a0,a1`. Define

```
n = m(V0+V1+z0+z1)-W^2-Q/J.
```

This is an integer because `J|Q`. It is strictly positive: since `A>W`,
`J>3A`, and `C>=1`,

```
W^2+Q/J
 = (1-2/J)W^2+(3WC+2)/J
 < D+(C+1)
 <= 2D.
```

Together with `m>=1` and `V1>4D`, this gives `n>0`. The definition
makes `Theta=Omega(z0+z1)`, so one norm factor vanishes and `P9=0`.

This proves equivalence of existence of positive zeros with the inherited
source. Composing with its already-stated arithmetic/logical calibration
and negating existential solvability gives the desired ordinary mathematical
theorem formalizable in ZFC. It does not produce an exported checked
object-language ZFC derivation.

## Degree caution

The simple majorant has fewer operations and lower degree than the old
majorant itself, but that alone does not establish a lower degree for the
complete norm polynomial. Leading cancellations in
`V1^2-a1`, followed by the outer norm, must be measured exactly. Its local
defect is explicitly available above, so a cancellation-aware degree proof
can use the identity rather than a naive gate-degree upper bound.
