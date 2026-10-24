# Integer arithmetic after the bounded-forall interface

This document proves the arithmetic backend transformation. The local
ten-coordinate Horn relation, its heterogeneous bounds, proof padding,
fixed-height accumulator, and inherited C222/ZFC calibration are separate
source obligations. They are stated and proved in the accompanying source
preprocessing documentation. No proof assistant was run for this backend.

## 1. Keep the nonnegative local majorant

The local row is originally represented by a pair `(e,f)` of polynomials
with nonnegative coefficients. Its semantic value is `e-f`. Both members
are retained, unchanged, when the bounded-forall certificate evaluates its
upper bound and its encoded row. In particular, no signed expression is
substituted for a nonnegative monotone majorant.

Only the outer arithmetic predicates expressing powers, Pell conditions,
Euclidean divisions, factorials, binomials, and congruences are compiled
by the signed backend. These predicates are finite ordinary polynomials.

## 2. Pair arithmetic can be evaluated directly over the integers

Let `value(a,b)=a-b`. The pair operations in the source compiler are

    (a,b)+(c,d)=(a+c,b+d),
    (a,b)*(c,d)=(ac+bd,ad+bc).

The identities

    (a+c)-(b+d)=(a-b)+(c-d),
    (ac+bd)-(ad+bc)=(a-b)(c-d)

hold for all integers. Consequently structural induction proves that
replacing pair arithmetic by ordinary signed addition, subtraction and
multiplication preserves the polynomial value of every outer predicate.
A sum of squares is nonnegative for arbitrary integer inputs; the product
of such sums vanishes precisely when at least one factor vanishes. Thus
the conjunction and disjunction interpretations are preserved without
assuming that intermediate arithmetic registers are nonnegative.

In particular, an individual square needs one multiplication of its
signed residual, rather than separate multiplications for the positive
and negative pair members. The new compiler changes the arithmetic DAG,
not the underlying logical predicate.

## 3. One signed quotient replaces two natural quotients

Each congruence in the source has fresh witnesses `q0,q1` in the residual

    a + m*q0 - b - m*q1.

The replacement residual is

    a + m*q - b,                 q in Z.

For any nonnegative `q0,q1`, set `q=q0-q1`. Conversely, for any integer
`q`, set `q0=max(q,0)` and `q1=max(-q,0)`. The residual values are exactly
equal under these substitutions. This assertion also holds when `m=0`;
no nonzero-modulus assumption is required. Each quotient pair is fresh
and appears only in its own congruence and the enclosing arithmetic
predicate. Therefore the replacements compose simultaneously.

The two original natural quotients cost two semantic coordinates and six
coordinates for nonnegativity. The new quotient costs one unrestricted
coordinate and requires no nonnegativity guard. In addition, redundant
nonlinear gates disappear from the new arithmetic DAG.

## 4. Optional inferred signs of Euclidean quotients

The emitted Euclidean division equations are

    n=q*d+r,             d=r+s+1.

If `n,r,s` are nonnegative integers, then `d>0` and necessarily `q>=0`.
Indeed, `q<=-1` would give `n<=-d+r=-s-1<0`. Hence a separate guard on
`q` is redundant. The remainder and slack retain their nonnegativity
guards.

The optional sign-inference variant checks this prerequisite in call
order: each dividend is a nonnegative-coefficient arithmetic expression
in guarded semantic inputs and earlier Euclidean quotients already proved
nonnegative. Congruence quotients are not admitted to this induction.
This is a syntactic, finite check of the hypotheses of the displayed
unbounded lemma. It does not infer signs by numerical experimentation.

## 5. Literal quartic flattening

Every semantic input that still requires nonnegativity is given the
equation

    x=A^2+B^2+C(C+1),             A,B,C in Z.

The right side is nonnegative for every integer triple. Conversely, for
`x>=0`, Legendre's three-square theorem represents `4x+1` as a sum of
three squares: it is odd and is 1 or 5 modulo 8, and so is not an excluded
number `4^a(8b+7)`. Its residue 1 modulo 4 forces precisely one square
to be odd. Write the even coordinates `2A,2B` and the odd coordinate
`2C+1`, then divide the identity by 4. Thus the displayed equation
represents every natural number, including zero.

For an addition, subtraction, or multiplication by a fixed integer,
the backend normally substitutes the resulting affine form. To keep the
expanded polynomial manageable, an affine form whose sparse support
exceeds the chosen fixed budget is instead retained as one unrestricted
wire with its defining linear residual. Such a support barrier has a
unique integral restoration and introduces no nonnegativity guard.
For each genuinely
nonlinear product of two affine forms `L1,L2`, it introduces one fresh
unrestricted integer wire `z` and the quadratic residual `z-L1*L2`.
All final equality residuals are affine forms in the remaining inputs
and wires. The guard residuals are quadratic. Their sum of squares is
therefore a single polynomial of degree at most four.

Given a semantic assignment, every wire is restored uniquely by
topological evaluation. Conversely, when all gate residuals vanish,
induction through the DAG proves that the wires have exactly those
values. Their signs are immaterial. This establishes an explicit
two-way zero-set correspondence between the mixed-sign semantic
certificate and the unrestricted-integer quartic.

The delivered fully expanded sparse polynomial contains nonzero
degree-four monomials, checked exactly, so the degree is four, not merely
bounded by four. All coefficients are explicitly stored integers, and
the complete list of quantified coordinates is counted from the actual
polynomial support.

## 6. Scope of the consistency conclusion

These transformations prove existential equivalence with the original
natural arithmetic certificate. When composed with the accompanying
proof-rule and bounded-forall theorems, and the cited ordinary
C222-to-ZFC-refutation calibration, they give the desired equivalence
between existence of an integer zero and a finite syntactic ZFC
refutation. Negating both sides gives the consistency equivalence.
This does not prove consistency, global minimality, or completion of an
encoded object-language ZFC derivation. Finite checks of the literal
circuit and expanded polynomial certify the artifact and its counts;
the universal arguments above are the mathematical proof.
