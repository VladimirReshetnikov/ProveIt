# Independent review of the coordinated integer-variable reductions

Status: PASS in the scope below. The transformations from the supplied
25-integer octic to the 21-, 20-, and 19-integer equations introduce no
additional domain restriction and preserve existence of zeros over the
unrestricted integers. Their local zero-set maps are polynomial bijections.

## Incoming source alignment

The literal incoming 25-variable system and the independently reconstructed
parent have different row orders. The incoming quotient row is row 11,
using zero-based indexing. Reorder incoming rows as

    [0,1,2,3,4,5,6,7,11,8,9,10,12].

Then add respectively (E-a), -E(c-eta), and 1 times the original incoming
row 11 to aligned rows 2, 3, and 5. Every other row remains unchanged.
The resulting thirteen polynomials equal the reconstructed parent rows
exactly. These are invertible elementary row operations over the integer
polynomial ring, with the pivot row unchanged. They preserve the complete
zero set at identical coordinates. The independent checker also expands
the compact parent display and matches every literal parent residual.

## Twenty-one variables

The simultaneous coordinate changes are

    C = q-F-alpha,
    Y = a-E,
    k = eta+zeta,
    tau_gap = tau-E(c-eta).

Their inverses are alpha=q-F-C, a=E+Y, zeta=k-eta and
tau=tau_gap+E(c-eta). Each is a polynomial over the integers, with no
division or sign premise. The independent checker verifies the inverse
identities symbolically before imposing any equation.

Four source equations then solve F, E, eta and V monically:

    F=(K0+W)C-z(q-1),
    E=XY,
    eta=c-Yk,
    V=fo-c.

Substituting these expressions makes exactly the four designated defining
rows vanish identically and gives exactly the nine delivered target rows.
Because every restored value is an integer for arbitrary integer retained
coordinates, projection and restoration are inverse on zero sets. In
particular no denominator such as q, C, Y, or k has to be nonzero.

The shifted first norm uses the exact cancellation

    (s+u)^2-(k+u)^2+(k+u)k-1 = s^2+(2s-k)u-1,

with u=EYk. Its degree is six after the restorations. The independent
residual-degree census is [4,6,8,5,4,3,8,6,8]. The coefficient of
Y^8 k^8 in the sum of squares is exactly 1, proving degree 16.

## Twenty variables

Replace y by fo+y_gap and eliminate I=(2r+1)c^2 through its monic row.
The inverse y_gap=y-fo is integral on every integer tuple. The identity

    (fo+y_gap)^2-(fo-c)^2 = (c+y_gap)(2fo+y_gap-c)

lowers the degree of the substituted auxiliary residual to nine. All eight
delivered residuals match the source substitution exactly; their degrees
are [4,6,8,5,4,8,9,8]. The coefficient of r^4 c^10 f^2 o^2 in the sum
of squares is 64, proving degree 18.

## Nineteen variables

Eliminate Y=(2v_scale+1)(beta(3J3+1)+1)^3 through the first source row.
This is another monic integer-polynomial restoration, with no inverse
division. The seven delivered residuals match the substitutions exactly.
Their degrees are [12,14,7,7,14,9,20]. The coefficient of
v_scale^8 J3^24 k^8 in the sum of squares is

    2^8 3^24 beta^24,

which is positive for the fixed source coefficient beta>0. Thus the total
degree is exactly 40 after numerical specialization of the coefficients.

## Evidence and limits

The checker `check_coordinate_maps.py` uses its own restricted arithmetic
parser and sparse integer-polynomial engine. It imports neither the
author's polynomial engine nor the coordinate generator. It verifies the
compact display, incoming row permutation and row operations, triangular
inverses, every deleted-row identity, every remaining-row substitution,
domain strings, variable counts and liveness, all residual degree bounds,
and all three leading-coefficient certificates. The checks hold over the
polynomial ring treating the fixed coefficient ports as indeterminates,
which is stronger than evaluation at a finite sample of numerical ports.
Normal and optimized Python runs both pass.

The review does not reprove the inherited signed-Pell, determinant,
native-window/compiler, coefficient-calibration or K215/ZFC semantic
theorems. The algebraic bijections transport whatever exact refutation
equivalence the authenticated 25-variable source has. They do not prove
absence of zeros, consistency of ZFC, worldwide novelty, or global
minimality, and are not an end-to-end proof-assistant verification.
