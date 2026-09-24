# Decoding the constant coordinate: 110 operations

The exact checker `../verification/round8_1980_certificate.py` verifies 110
arithmetic instructions (61 multiplications and 49 additions), 33 positive
unknowns, and 21 equations. Generating the fixed numerals adds seven
instructions, for 117 operations. Every previous certificate is preserved.

## A homogeneous encoding with one special target

Start from the same integer quadratic system in input `x=X_0` and 58
nonnegative existential coordinates. Choose an integer basis of its rational
row span and pad to 1830 residuals `F_i`, exactly as in the direct quadratic
construction. Introduce an encoded unit coordinate `delta` and homogenize:

    F_i^h(delta,X) = sum_{|I|<=2} a_{i,I} delta^(2-|I|) X^I.

Introduce one more encoded nonnegative coordinate `u` and the ordinary guard

    u delta - x^2 = 0.

There are 1831 ordinary rows: the 1830 homogenized residuals and this guard.
Add a final special target with value `delta^2`. It is not an equation
requiring zero: the mask below permits precisely the target values 0 and 1.
All ordinary targets are scaled by two, so their even target values must
still be zero. The special target forces `delta` to be 0 or 1, and the
guard with positive input `x` excludes 0.

These extra coordinates and rows are part of the fixed integer encoding,
not additional unknowns or equations of the final polynomial system.

## Explicit uniform positions

There are 60 positive-weight coordinates, indexed `i=0,...,59`; index 0 is
the input, indices 1 through 58 are the original witnesses, and index 59
is `u`. Give `delta` weight zero and put

    J = 2*59^2+1 = 6963,
    v_i = 1+3(J*i+i^2),
    v_* = 1242895.

Use 1832 target positions, with

    D_step = 4v_*+1 = 4971581,
    T_first = (1832+1)D_step+2v_* = 9115393763,
    t_r = T_first+r D_step,    0<=r<1832,
    t_* = 18218358574,
    K = t_*+1 = 18218358575,
    L = 5^16 = 152587890625 > 3K+2 = 54655075727.

The exact checker verifies all support inequalities and all 1891 distinct
homogeneous quadratic monomial weights. They are distinct for the same
elementary reason as before: reduction modulo 3 distinguishes the number
of positive-weight factors (0, 1, or 2); for two factors, division by `J`
recovers their sum and their sum of squares, hence the unordered pair.

The support separation is

    D_step > 2v_*,
    T_first-2v_* > v_*,
    2T_first-2v_* > t_*.

In particular products involving dummy row coordinates do not contribute
to any target, and every low coordinate position, including zero, receives
an automatic zero from the residual polynomial.

## Coefficient and mask codes

For the ordinary rows, use the same integer coefficient rule as before:
if `a` is the coefficient of a homogeneous quadratic monomial and `c=1`
or `2` is its multinomial coefficient in `C^2`, put coefficient `2a/c` in
the complementary position. For the special row use coefficient exactly
`1` at its target position: its contribution is `delta^2`, not `2delta^2`.
Let `D(B)` be the resulting signed coefficient polynomial. The row supports
are disjoint, so no coefficients collide. Choose a power of two `z>=2`
strictly greater than the absolute values of all coefficients, including
the special coefficient 1, and put `Z=2z`.

Define

    ell_0(B) = 1 + sum_{i=1}^{59} B^(v_i) + sum_{r=0}^{1831} B^(t_r),
    e_0(B) = z sum_{j=0}^{K-1} B^j + D(B),
    V = ell_0(Z) + e_0(Z) Z^L.

Thus the mask now includes the unit coordinate. Both codes have degree
`t_*`; the digits of `e_0` are in `[1,Z-1]`, and the digits of `ell_0`
are 0 or 1. There are 1892 non-input code coordinates (the unit, 59 true
coordinates, and 1832 dummy coordinates), hence 1893 coordinates including
the input. We use the convenient strict coefficient bound `1900b`.

Choose a fixed power of two

    H > max(2Z^(2L+1), 4^(t_*+3) Z 1900^2, 3L, 16).

In particular `H>4Z1900^2` and `H>4Z`. All these choices depend only on
the represented set, independently of the queried positive input `x`.

## Changed arithmetic equations

Retain the complete 111-operation reversed-packing system from
`REVERSED_PACKING_PROOF.md`, with only two arithmetic replacements:

    C = xB+g                 instead of 1+xB+g,
    T_3 = (B-4)ell           instead of (B-2)ell.

In particular, its equations and abbreviations include

    B=Hb^2,                 b=x+beta,
    theta+Z=B,              lambda(B-1)=q^2-1,
    n=q^8,                  Y=ell+eq,
    Y+C^2+alpha=q^2,        Y=V+t theta,
    S_3=(2e-Z lambda)C^2+B lambda(1+q),    sigma=S_3,
    S=g+q^2(Y+q^2 S_3),
    T+1=q^2(1+theta lambda)-(b-1)ell+(B-4)ell q^4,
    r=S(n^2-n)+(T+1)(n^2-1).

The system unknowns, including `sigma`, are all positive. The coordinate
`delta` is the as-yet-unknown unit digit of `g`; it is decoded, not supplied
as an extra polynomial-system unknown.

## Bootstrap and canonical code recovery

Every initial bound and every Pell implication in the reversed-packing
proof remains valid. In particular `C=xB+g>B` because `x,g>0`, so
`C<q` still gives `q>B`. Replacing `B-2` by the smaller positive number
`B-4` preserves the complete bounds `0<S<n` and `0<=T<n`, even when the
first raw mask is initially negative. The identical borrow argument gives
`d=floor((b-1)ell/q^2)=0`, and the middle mask then decodes

    Y=ell_0(B)+e_0(B)q,
    ell=ell_0(B)+mq,    e=e_0(B)-m,    0<=m<e_0(B).

The low first mask gives precisely the digits of `ell_0` for `g`, each
less than `b`. In particular its unit digit satisfies `0<=delta<b`.
The input position 1 is excluded from `ell_0`, so the input digit of
`C=xB+g` is exactly `x`. All other decoded digits have the intended
positions, and `deg C<=t_*`.

Let `A=C(1)^2`, the sum of the coefficients of the square of this digit
polynomial. Then

    1 <= A < 1900^2 b^2,     4 <= ZA < B/4.

The lower bound uses the positive input digit, so it holds before `delta`
has been shown to be 1. As before, `e,C<B^K` and `L>3K+2` imply
`2eC^2<2B^(3K)<q`.

For the possible alias define `X=(B-4)m`. Since `m<B^K`, its digits have
positions at most `t_*+1`. The low term `(B-4)ell_0` is less than `q`, so
these digits of `X` appear unchanged in the third mask at positions
`L,...,L+t_*+1`. The high digits of `S_3` there are at least `B-ZA`:
the same raw-coefficient and carry argument from the reversed-packing
proof applies, including its safe first-digit interval `[B-ZA,B-ZA+2]`.
Therefore every base-`B` digit `X_j` is at most `ZA-1`.

Write `F(U)=sum X_j U^j`. The divisibility `F(B)=(B-4)m` implies
`F(4)=0 mod(B-4)`, whereas

    0 <= F(4) < ZA 4^(t_*+2)
                 < Z 1900^2 b^2 4^(t_*+2)
                 < B/4 < B-4.

Consequently `F(4)=0`, all its nonnegative coefficients vanish, and
`m=0`. Both codes are canonical. This recovers the decisive uniqueness
argument for the changed mask; it is not assumed from the earlier
evaluation-at-2 construction.

## Decoding the unit and the ordinary equations

Below `K`, the residual factor `e_0-z lambda` equals `D`. The coefficient
of `C^2D` is automatically zero at every low mask coordinate, including
the new unit coordinate. At an ordinary target it is exactly twice its
homogeneous quadratic residual; at the special target it is `delta^2`.
The uniqueness and support-separation proof used for the direct quadratic
layout remains valid with the constants above. In particular no dummy
row coordinate contributes to these target values.

Every coefficient of `(e_0-z lambda)C^2` has absolute value at most

    z A < z 1900^2 b^2 < B/4.

Below the first `q` boundary, the offset in `S_3/2` is exactly `B/2` in
every base-`B` digit. All such digits are therefore strictly between
`B/4` and `3B/4`, without carries between them. The even third block and
mask can both be divided by 2. The new mask has digit

    B/2-2

at each target. It has binary ones in every position except the unit bit
and the uppermost bit of a base-`B` digit. A digit in `(B/4,3B/4)` with no
binary overlap with this mask is thus either `B/2` or `B/2+1`. The target
coefficient must be 0 or 1.

For an ordinary target this coefficient is even, so it is zero. For the
special target it is `delta^2`, giving `delta=0` or `delta=1`. The guard
is an ordinary target, hence `u delta-x^2=0`. Since `x>0`, it excludes
`delta=0`. We obtain `delta=1`; each homogenized original residual is
therefore its original inhomogeneous residual, and every one vanishes.
This proves soundness without imposing an uncharged unit-coordinate
constraint on the system variables.

## Necessity and exact arithmetic count

Given a genuine solution, set `delta=1`, `u=x^2`, and assign any
nonnegative values to the dummy coordinates, for example all zero.
Choose a sufficiently large power of two `b` that exceeds `x`, `u`, and
every other coordinate. The unit digit now guarantees `g>0` without
requiring a positive dummy coordinate. Use the canonical code values.
The unchanged degree margins ensure `Y+C^2<q^2` and `ZC^2<q`, giving
positive `alpha` and `sigma`. The packed quotient is positive. The
ordinary target coefficients are zero and the special coefficient is
one, so all masks hold. The existing Pell necessity constructions supply
the remaining positive unknowns.

The 111-operation schedule computed `xB`, then `xB+1`, then `xB+1+g`.
The present schedule computes `xB` and `xB+g`, removing one addition.
The changed subtraction `B-4` has the same cost as `B-2`, and the numeral
4 is already required elsewhere. No other arithmetic instruction,
positive unknown, or equality test is added. The exact checker verifies
all 110 primitive instructions and all 21 residual identities, including
the pre-existing triangular corrections.
