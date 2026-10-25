# A balanced shear of one CRT gate

This ordinary proposal changes the coordinate of `mul.40`, rather than
translating coordinates or shearing the three encoded inputs alone. In
both pinned centered quartics the map

    x_21 = z_21 - 2z_10 - 2z_11,
    x_i = z_i for every i != 21

has determinant1 and a complete integer inverse. It substantially lowers
several specified large coefficients and removes one specified leading
monomial. These are exact coefficient identities, **not** a new whole
coefficient height, support count or numerical endpoint. No substituted
equation, expanded polynomial, application code or rendering is produced.

The more aggressive shear x_21=z_21-3z_10-4z_11, which annihilates a
repeated square argument, has a proved drawback: its coefficient of
z_10*z_11^3 is164828, larger than the present height128446. Balancing the
downstream forms matters.

## 1. Exact inputs and namespace

The two inputs are the existing plain and weighted `equation.json` and
`expanded_polynomial.json` under
`research/round16-common-name-centering/data/`. They have316 and315
unrestricted integer coordinates. In both, indices10,11,12,21 have names
`crt.encoded.a`, `crt.encoded.b`, `crt.encoded.c`, `mul.40`.

The accepted ordinary `research/translation-height-obstruction` note
proves that constant integer translations of either current polynomial
cannot lower its height128446. The present linear substitution changes
the leading form, so it is outside that obstruction. No global optimum
over linear changes is claimed.

SOURCE_PINS authenticates the complete three-file ordinary note, its
outside34-file observed centering inventory and every file in that
inventory. The observed centering checkpoint is immutable source data;
it is not relabeled a final accepted endpoint. Its historical optimized
interruption is not a successful result or retried here. Subsequent
root-owned verification is outside the present proof and pins.

Write P(x)=sum_j r_j(x)^2 for either actual complete residual list.
Throughout the proposed chart put

    a=z_10, b=z_11, c=z_12, u=z_21, g=z_3.

Every other indexed z has its own input profile's literal index. None
of a,b,c,u,g denotes a fixed constant or a natural-number restriction.
Residual row numbers below are zero based.

## 2. Universal inverse, degree, liveness and witness maps

Let S be the displayed map from z to x. Its matrix is the identity
except that row21 has entries-2 in columns10 and11. Adding twice row10
and twice row11 to row21 gives the identity, so det(S)=1. The inverse is

    z_21=x_21+2x_10+2x_11,
    z_i=x_i for every i != 21.

Both maps have integer coefficients and are inverse on the whole Z^n.
Define every new residual by r'_j(z)=r_j(Sz), with every original row
retained, and define P'(z)=sum_j r'_j(z)^2. Then, for all integer z,

    P'(z)=P(Sz).

Thus the entire integer zero sets correspond in both directions.
Substitution preserves the quadratic bound of each row. An invertible
linear substitution acts injectively on each homogeneous degree, so the
nonzero quartic leading form stays nonzero and the exact degree is4.

All current coordinates remain live. For j outside{10,11,21}, S fixes
x_j and its other images do not involve z_j. Consequently
partial_j(P o S)=(partial_j P) o S is nonzero whenever partial_j P is
nonzero. The three affected coordinates are also present: unchanged
row7 has quadratic part -(a+2z_22)^2, unchanged row9 has quadratic part
-(b+c)^2, and new row25 has quadratic part -16u^2. In a sum of squares
the coefficient of a pure fourth power is the sum of the squares of
the corresponding row's pure-square coefficient. Hence a^4,b^4,u^4
have positive coefficients, without a cancellation assumption.

For a source witness, first use the existing whole source construction
and centering map, then apply S inverse. For inversion, apply S first,
then add the current fixed58 shifts, then apply the existing complete
raw monic/Horn/source maps in their original order. Sign arguments
belong to the recovered old tuple. No new sign argument, private-witness
inverse, native tuple or calibration is supplied by this shear.

## 3. Every changed residual

The actual occurrence lists contain exactly13 rows in each profile.
Ten have the same row number and all referenced indices in both
profiles:5,6,12,15,19,21,25,50,51,52. The remaining three pairs of row
numbers and output coordinates are:

| Role | Plain row/output | Weighted row/output |
| --- | --- | --- |
| first bilinear row | 71 / z_86 | 71 / z_87 |
| second bilinear row | 73 / z_89 | 74 / z_90 |
| label-sum addition | 90 / z_105 | 91 / z_106 |

Every row not in this complete list is unchanged, since none of its
literal monomials contains index21. Put

    M = 2a+4b+2u,
    L_12 = 8a+4b+8c+2u+2z_27,
    L_15 = 2a+4b+4c+2u+4z_27+2z_30,
    L_19 = -2a-4b+2c+2u+2z_25,
    L_50 = -2a-4b+c+2u,
    L_51 = -2a-4b+2u+2z_66,
    L_52 = -4a-8b+4u+2z_65+2z_67.

The complete new residuals in the first ten rows are:

| Row | Complete r'_j |
| --- | --- |
| 5 | u-(a+b)^2-1 |
| 6 | z_22-M^2-5M-5 |
| 12 | z_28-L_12^2-M |
| 15 | z_31-L_15^2+2L_15-M+1 |
| 19 | z_35-L_19^2+8L_19-12 |
| 21 | z_37-M^2-3M-1 |
| 25 | z_41-16u^2-14u-2a-4b-6 |
| 50 | z_66-L_50^2-2L_50+c |
| 51 | z_67-L_51^2+2L_51+1 |
| 52 | z_68-L_52^2-L_52+2z_65-2 |

For the other three rows use the profile's output coordinate from the
preceding table. Their complete expressions, in the same order, are

    output-1+2g-2g(u-a-2b),
    output-1-gM,
    output-a-b-4u-D,

where the whole unchanged linear expression D is

    D = 2z_24+4z_26+2z_29+2z_31+4z_32+2z_34+2z_36
        +4z_39+2z_40+2z_43+2z_47+4z_68+2z_69.

These formulas are obtained by direct substitution in every term of
the listed literal rows. For example the old row5 is
x_21-(a+b-1)^2, which becomes u-(a+b)^2-1. The old row25 is

    x_41-16(2a+2b+x_21)^2-14(2a+2b+x_21)-2a-4b-6,

so its quadratic part becomes a single pure square. The old row6
and row21 use the same argument6a+8b+2x_21, which becomes M. These
examples explain both the factorization and the balanced choice.

## 4. A complete leading-form difference for the two-parameter family

This also describes why annihilating the repeated argument is risky.
For any fixed integers m,n define the integer shear S_(m,n) by
x_21=u-ma-nb and fix every other coordinate. Its determinant and inverse
proof are the same as above. Introduce the following complete linear
forms, including their unaltered gate coordinates:

    M_(m,n) = (6-2m)a+(8-2n)b+2u,
    L_12(m,n) = (12-2m)a+(8-2n)b+8c+2u+2z_27,
    L_15(m,n) = (6-2m)a+(8-2n)b+4c+2u+4z_27+2z_30,
    L_19(m,n) = (2-2m)a-2nb+2c+2u+2z_25,
    L_25(m,n) = (8-4m)a+(8-4n)b+4u,
    L_50(m,n) = (2-2m)a-2nb+c+2u,
    L_51(m,n) = (2-2m)a-2nb+2u+2z_66,
    L_52(m,n) = (4-4m)a-4nb+4u+2z_65+2z_67.

Let

    A_(m,n) = 2M_(m,n)^4
      + L_12(m,n)^4+L_15(m,n)^4+L_19(m,n)^4+L_25(m,n)^4
      + L_50(m,n)^4+L_51(m,n)^4+L_52(m,n)^4.

The subscript4 denotes the whole homogeneous degree4 component, not
evaluation or projection. The exact global identity is

    (P o S_(m,n))_4 - P_4
      = A_(m,n)-A_(0,0)
        +4g^2(((1-m)a-nb+u)^2-(a+u)^2)
        +g^2(M_(m,n)^2-M_(0,0)^2).

Indeed the nine affected square-type quadratic parts are minus the
squares of the listed linear forms, with M used twice. Squaring them
gives their fourth powers. The first and second bilinear rows have
quadratic parts -2g(a+x_21) and -g(6a+8b+2x_21), respectively. Row5's
quadratic part is unchanged and the final addition row is linear.
This accounts for every affected leading row and proves the identity
over all coordinates, for both profiles and all integer m,n. It is not
merely a restriction to a few variables or a sampled identity.

## 5. Exact selected coefficients, without a whole new census

For a linear form L=Aa+Bb+Cc+Uu+..., the coefficients of a^2bc,
a^2c^2,a^2b^2,ab^3,a^2bu in L^4 are, respectively,

    12A^2BC, 6A^2C^2, 6A^2B^2, 4AB^3, 12A^2BU.

The terms involving g in section4 contribute to none of these five
monomials. Applying those five elementary expressions to the entire
eight-form list, with M counted twice, gives:

| Monomial | Contribution from A_(0,0) | Contribution from A_(2,2) |
| --- | ---: | ---: |
| a^2bc | 124416 | 24768 |
| a^2c^2 | 58872 | 25080 |
| a^2b^2 | 121344 | 14592 |
| ab^3 | 77824 | 13312 |
| a^2bu | 72960 | 0 |

For example the a^2bc contributions in the old chart are110592 and
13824 from rows12 and15. The new contributions in rows12,15,19,50
are24576,768,-384,-192, whose sum is24768. All other listed forms
have zero c coefficient. Subtracting the old contribution and adding
the new one to each existing literal coefficient yields:

| Monomial | Current plain / weighted | Balanced plain / weighted |
| --- | ---: | ---: |
| a^2bc | 128446 / 128446 | 28798 / 28798 |
| a^2c^2 | 126901 / 126901 | 93109 / 93109 |
| a^2b^2 | 121910 / 121909 | 15158 / 15157 |
| ab^3 | 78812 / 78812 | 14300 / 14300 |
| a^2bu | 72960 / 72960 | 0 / 0 |

Thus a specified leading monomial disappears and several of the
largest present coefficients decrease. These finite identities do
not imply that no other coefficient grows, or that the full support
shrinks. For example L_19 gains a b term, and this can create mixed
monomials elsewhere.

There is also a useful lower bound on this entire gate-shear family.
In every S_(m,n), the coefficient of a*z_22^3 remains

    4*1*2^3 + 4*6*16^3 = 98336.

Only the quadratic parts of rows7 and8 contribute to that degree4
monomial. Neither contains x_21. Row6 contains z_22 only linearly,
so it cannot contribute z_22^3 after squaring. All other changed
rows omit z_22. The parallel rows22,23 similarly leave the coefficient
of a*z_37^3 equal to98336. Therefore the height throughout this
two-parameter family is at least98336, regardless of whether the
balanced member improves the present whole height128446.

## 6. The annihilating member is worse in height

For m=3,n=4 the repeated form M_(3,4)=2u loses both encoded inputs.
However L_52=-8a-16b+4u+2z_65+2z_67, whose fourth power contributes

    [ab^3] L_52^4 = 4*(-8)*(-16)^3 = 131072.

Rows19,25,50,51 each have a,b coefficients-4,-8 and each contributes
8192. The remaining affected fourth powers contribute0. Thus
[ab^3]A_(3,4)=163840. In the existing complete polynomial the part
outside A_(0,0) contributes78812-77824=988 to ab^3; the g terms
contribute0. Consequently the exact full coefficient is

    [ab^3](P o S_(3,4)) = 163840+988 = 164828.

Its height is at least164828 and exceeds the current128446. This
rules out that particular aggressive choice as a height improvement;
it does not rule out other unimodular matrices or prove an optimal
choice of m,n.

## 7. What remains before an endpoint claim

The balanced chart is an explicit complete substitution recipe with
proved ordinary integer inverse and all changed residuals specified.
A future separately prepared implementation must authenticate both
whole inputs and this recipe, substitute in every full row, collect
every coefficient independently, compare the complete substitution
identity and inverse, and measure the whole height/support/liveness.
It must bind the complete existing witness maps in the stated order.
The observed source checkpoint's separate final-verification boundary
must remain explicit. Further linear choices are a different recipe,
not part of a hidden optimization search here.

This packet contains only ordinary proof and source pins. No application
or helper is imported, compiled or run; no AST/optimizer/search is
used; no new polynomial packet, coefficient census, native tuple,
calibration, TeX/PDF or Lean result is produced. The maintained complete
compact66 page and all held/frozen author packages remain unchanged.
