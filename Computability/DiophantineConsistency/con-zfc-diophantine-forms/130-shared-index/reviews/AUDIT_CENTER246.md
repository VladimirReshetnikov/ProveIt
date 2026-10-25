# Independent review of the weighted-center degree-246 equation

## Verdict

The ordinary proof in `../center246/PROOF.md` is sound. I found
no fatal error or gap in the new center bounds, root recovery, positive
transport argument, completeness, or exact-degree calculation. The
source/native/refutation calibration remains inherited exactly as stated.
This is a degree improvement within the inspected ten-positive family,
with an operation-count increase; no global minimum is implied.

This review is mathematical. I did not duplicate the author's existing
149 transcription/coefficient checks. The independent checks below explain
why their tested identities support the claimed unbounded theorem.

## 1. Positive bounds are valid before decoding a zero

The stated weakened domain `L>=3`, `t>=4` suffices. In particular:

- The first term of `Q1/k^2` is
  `t^2 L(L-1)^2(tL-1)>=24t^3`, and its remaining term is positive.
  Thus `Q1>k^2(t+2)`.
- The exact remainder `r1=L^3+k^2(L^2-t-2)` is greater than
  `-k^2(t+2)>-Q1`, so `L^3D>(A-1)Q1>Q1`.
- `Q3>0` and `Q3<k^2 t X^2<D`. Consequently
  `0<4Q1+Q3<5L^3D<8L^3AD`, proving
  `0<Gamma<lambda A D E`.
- Since `lambda A=8L^3(tL+1)<=16tL^4<t^4L^4<Delta^2`,
  and `E>=1`, one obtains `Gamma<Q` and
  `lambda A D E<Q`.

These estimates are unconditional in the positive input domain. They
therefore do not create circular use of the later transport sign.

## 2. The changed weight does not weaken radical extraction

The two radicands are still unequal modulo `D`. The norm implies a
nonzero rational signed sum, hence each root is rational. Dividing the
first rational root by the positive integer `lambda` makes `D Fs` a
rational square; its integrality and `gcd(D,Fs)=1` recover exactly the
same positive `tau` and `f` as in the parent. Thus the kernel recovers
the same strong ordinate `I=tau E` and the same auxiliary integer root.

The parent folding and auxiliary-index gap apply before the center is
used. In particular `b>8Q`, while
`lambda tau f+X/q^4<2Q<b/4`. The new center is positive and enters
the solved-for padding coordinate with a minus sign. The other two
error bounds are each below `b/4`, so a negative `B` makes the new
padding coordinate negative. This establishes the required transport
sign without assuming any particular radical branch.

All subsequent modular terms are unchanged: the center and weighted
root are integers. There is no new denominator and no new cancellation
of a nonunit modulo the height modulus.

## 3. Completeness really preserves positivity

At the parent's canonical witnesses, the auxiliary difference satisfies
`u=y-V>2Q`. The new center satisfies `Gamma<Q`; the two other loss terms
satisfy `sY+kappa<2c`; and `Q>c^4>2c`. Therefore the proposed new padding
coordinate is greater than `2Q-Q-2c>0`, even if the native transport
quotient is zero. Its integrality follows from the unchanged canonical
source facts. This supplies a genuine positive witness, rather than
only an algebraic root over unrestricted integers.

## 4. Independent derivation of the center-defect leading coefficient

Put `H0=L^3D` for this paragraph only; it is unrelated to the source
height `H=4A-5`. The exact quotient identities are

    H0=A Q1+r1,       H0=A^3 Q3+r3.

The bracket in the center defect, after subtracting its leading square,
is

    (8A H0-4Q1-Q3)^2-64H0^2(A^2-1)
      =64H0 r1+16(Q1^2-A H0 Q3)+8Q1Q3+Q3^2.

Also

    Q1^2-A H0 Q3=(H0 r3-2H0 r1+r1^2)/A^2.

The latter identity may be used in the fraction field for the degree
calculation; the left side is already a polynomial. With weights
`deg(L,t,k)=(1,3,1)`,

    (H0)_top=k^2 L^5 t^4,
    (r1)_top=-k^2 t,
    (r3)_top=-3k^2 L^2 t^3.

The degree-24 contributions are consequently
`-64k^4L^5t^5` and `-48k^4L^5t^5`. Their sum is
`-112k^4L^5t^5`. Multiplication by `E^2` gives precisely

    C_top=-112L^5t^5k^4E^2,

of total degree 34 after the original variable substitution. The term
`-lambda^2D` is lower degree. This independently confirms the crucial
center-defect coefficient and shows that its cancellation is an exact
polynomial phenomenon rather than a heuristic truncation of a radical.

## 5. Both competing leading terms of the full norm are included

The review confirms `deg(Z0)<=19`, `deg(Theta)=112`, and the five
degree bounds `246,246,224,226,150` in the centered norm identity.
The second degree-246 term must be retained. The displayed combined
leading form

    4 delta0^2 M0^4 V0^2 (C0-2 Gamma0 b0 B0)

is correct. Its `C0` contribution has degree ten in `i`, whereas the
other has degree nine. Therefore cancellation of the entire top
homogeneous component is impossible.

Direct multiplication of the listed leading factors gives the first
contribution

    -7*2^14 q0^116 X0^29 i^10 Y^57 k0^32(q0-F)^2.

Selecting `x^29`, `eta^32`, and `F^2` yields the coefficient
`-7*2^14 beta^116` at
`J^116 x^29 i^10 Y^57 eta^32 F^2`. Its exponents sum to 246 and
its coefficient is nonzero for the actual fixed positive `beta`.
Thus the claimed exact total degree is proved for the actual tuple,
not merely for generic coefficient ports.
