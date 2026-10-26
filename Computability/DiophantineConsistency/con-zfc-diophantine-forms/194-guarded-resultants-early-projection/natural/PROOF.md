# A 201-variable natural quartic and certified degree tradeoffs

## 1. Result and calibration

Every displayed coordinate ranges independently over N={0,1,2,...}. The
principal equation is the sum of the squares of the **153 literal quadratic
residuals in `natural201/equation.json`**. It has **201 variables, exact degree
4, 6,002 nonzero expanded monomials, and coefficient height 1,860,103**.
`expanded_polynomial.json` supplies every collected coefficient, rather than
only an arithmetic-circuit description. Every variable occurs.

The inherited calibration is unchanged: a natural zero exists exactly when
the fixed effectively presented ZFC calculus in the inherited C222/ZF/ZFC
calibration has a finite syntactic refutation. Thus its no-natural-zero
sentence is equivalent to `Con(ZFC)` in that specified calibration. This is
neither a consistency proof nor a claim of global dimension optimality or a
new end-to-end kernel-checked derivation of the coefficients. The unbounded
Pell and syntactic arguments are ordinary proofs preserved in `inherited/`.
The new argument below is an ordinary proof of exact natural-zero-set
bijections. The accompanying independent programs certify its finite
polynomial identities and finite nonnegativity criteria.

| Profile | Variables | Rows | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|
| natural201 | 201 | 153 | 4 | 6,002 | 1,860,103 |
| chart202, before contraction | 202 | 154 | 4 | 6,000 | 1,854,571 |
| natural165_degree6 | 165 | 117 | 6 | 6,558 | 1,860,101 |
| natural164_degree6 | 164 | 116 | 6 | 15,774 | 1,860,101 |
| natural139_degree8 | 139 | 91 | 8 | 11,873 | 1,117,699,986 |
| natural138_degree8 | 138 | 90 | 8 | 16,515 | 2,933,403,776 |

The lower-dimensional companions spend degree and are not quartic-dimension
claims. Their rows have degrees at most three or four, respectively.

## 2. Affine charts whose positivity is certified on zeros

Let R=(R_0,...,R_(m-1)) be integral polynomials in n coordinates. Let S be a
set of coordinates with designated source rows

    R_(j(v)) = X_v-f_v(X),     f_v in N[X].                 (1)

Assume an order on S in which every coordinate of S occurring in f_v is
earlier than v. Coordinates outside S may be arbitrary natural witnesses;
they need no positive defining row. Let F be an integral affine automorphism
with integral affine inverse G, fixing the coordinates outside S. Suppose
that for each v in S the certificate gives an identity

    F_v = P_v + sum_j a_(v,j) R_j,     P_v in N[X],         (2)

where the a_(v,j) are integer constants. Then F and G restrict to mutually
inverse bijections between the natural zero sets of R and R composed with G.

Proof. At a natural zero x of R, (2) gives F_v(x)=P_v(x)>=0, and the other
coordinates are unchanged. Substitution gives (R composed with G)(F(x))=0.
Conversely, let y be a natural zero of the transformed system and set z=G(y)
in Z^n. The coordinates outside S are nonnegative. Exact affine substitution
gives R(z)=0. Induct along (1): all arguments in f_v have already been proved
nonnegative, so z_v=f_v(z)>=0. Thus z is a natural zero of R. The two affine
inverse identities give both inverse laws. QED.

This is strictly more flexible than requiring every elementary shear to add
a nonnegative affine polynomial. It does NOT assert that G preserves the
entire orthant. Integer negative intermediate values at nonzeros are harmless;
negative restored values at actual zeros are ruled out by (1).

An invertible integer row change preserves the common zero set. In particular,
R_i <- R_i+k R_j (i!=j) is reversed by subtracting k R_j. Affine substitution
preserves the maximum residual degree, because its inverse gives the reverse
inequality. The exact quartic degree is also checked from nonzero collected
fourth-degree coefficients.

## 3. Literal application and the new quartic contraction

The starting equation is the 202-variable,154-row pooled natural system in
`inherited/inherited/pooled202/equation.json`. Its complete pooled-power
orientation repair, additive frame bounds and calibration closure are kept
byte-for-byte. No Pell coordinate, modulus interpretation or power orientation
is assumed to survive an arbitrary shift: the exact original natural zero is
restored BEFORE applying any inherited theorem.

The chart begins by accumulating the positive syntax index budget into the
old gate x29, then applies the twelve preceding-round syntax shears. A further
40 recorded elementary affine shears give the final chart. The 24 recorded
integer residual shears are subsequently applied. The complete replay inputs
are `chart202/base_chart.json`, `checkpoint.json`, `row_operations.json` and
`source_equation.json`; `rebuild_and_check.py` replays them independently.
The authoritative certificate also gives every forward and inverse affine
coordinate and all original defining-row indices.

There are 33 changed coordinates. In 29 cases the final forward coordinate
is itself coefficientwise nonnegative. The other four use exactly one source
row in (2), for original coordinates 27,31,49,93 and source rows 13,17,34,75,
respectively. For example,

    F_31=X_27+X_31-16X_25,
    F_93=X_93-X_92.

Subtracting source row17 from F_31 gives the explicitly stored polynomial
whose coefficients are all nonnegative. Source row75 is X_93-H X_92 with
H having constant236 and nonnegative other coefficients; hence
F_93=(H-1)X_92+R_75 is nonnegative on zeros. The literal representative has
constant multiplier235. The independent checker verifies all four identities,
all 33 original positive definitions, their dependency order, both affine
inverse identities, all row changes and every expanded coefficient.

In the final 202-coordinate chart, retain the old indices temporarily. Two
rows are

    R_42 = X_57-2-6X_48-4X_48^2,
    R_44 = X_59-4X_57-X_58-X_58^2.                         (3)

No other row contains X_57. A coordinated shear of X_59 has removed its other
incidences. Substitute

    X_57=2+6X_48+4X_48^2                                 (4)

and delete row42 and coordinate57. The remaining occurrence becomes

    X_59-8-24X_48-16X_48^2-X_58-X_58^2.                   (5)

All residuals are therefore still quadratic. Equation (4) is nonnegative for
every natural retained assignment, and the deleted monic row forces exactly
this value. Extension by (4) and deletion of coordinate57 are mutually inverse
bijections of natural zero sets. Combining with Section2 and the inherited
calibration proves the principal result. Remaining indices are then renumbered
in increasing order; `contractions.json` lists the retained old indices.

## 4. General exact contractions without an orthant mistake

A useful extension permits signed restoring expressions and accounts for the
degree-six and degree-eight companions. Start from a chart C=U(R composed
with G), with U an invertible integer row matrix and with the hypotheses of
Section2. Repeatedly choose a row having the form

    aY_v+h(Y_other)=0,     a=1 or -1,

substitute Y_v=-a h in every other row, and delete that row and coordinate.
This process gives a polynomial extension E from retained coordinates to all
chart coordinates and a projection pi in the opposite direction. Over Z,
these are inverse maps on the two common zero sets: each deleted monic row
forces precisely its defining polynomial. This assertion follows by induction
on the literal sequence of substitutions; no division or congruence is used.

Let D be the set of deleted original coordinate indices, and suppose the
original system has positive acyclic defining rows (1) for EVERY coordinate
in S union D. Then the contractions preserve natural zero sets as well,
even if some polynomial entries of E have negative coefficients.

Proof. An original natural zero maps by F to a natural chart zero and projects
to a natural retained zero. Conversely, given a natural retained zero y,
extend to E(y) in Z^n and put z=G(E(y)). All source residuals vanish because
the deleted equations hold identically and U is invertible. Every coordinate
outside S union D is still a retained, unchanged natural coordinate. Induction
along its specified original positive defining rows proves z_v>=0 for every
v in S union D. Hence z is an original natural zero. The forward-positivity
identities (2) now prove F(z)=E(y) is natural too. Thus no unproved naturalness
of a signed restoring polynomial was assumed. The integer inverse identities
already proved give the natural inverse identities. QED.

For the 165-,164-,139-variable profiles the source chart is the new chart202;
the respective contraction sequences have 37,38,63 steps, and the restoration
sets have 69,70,83 coordinates. For the 138-variable profile the source is the
preceding-round chart202, with 64 steps and 74 restoration coordinates. All
these numbers, each selected monic equation, all substitutions, and all
renumberings are certified independently. This last profile eliminates the
original outer x as well, but not by assuming a sign: its retained source row
explicitly gives x=1+endpoint.ut*(1+mul.8), with a positive acyclic dependency
on mul.8. This preserves the existential refutation equivalence; no theorem
with x held as an externally fixed free parameter is being claimed.

The finite selection heuristic minimizes a local squared row-support cost
subject to residual degree at most3 or4. It is only a means of finding the
literal certificates; no optimality inference depends on it.

## 5. Current-source comparison and actual tradeoffs

The comparison is pinned to upstream commit
`ecb9a4b4dda617512952525d50f17343700aac52`, not an obsolete summary. Literal
natural equations from the authenticated source178 polynomial-centers packet
are included under `comparison/`; `verify.py` independently recollects all
of their SOS coefficients. Its 203-coordinate principal and sparse quartics
have respectively 8,237 terms/H799,349,232 and 8,263/H207,116,893, with155rows.
The new201 quartic improves variables, rows, support and height against both.
Its low-height203 companion has49,682 terms/H481,920, so it is a real height
tradeoff rather than dominated by the new201 equation.

Against the immediately preceding round22 principal202 quartic, the changes
are 202->201 variables,154->153 rows and9,353->6,002 terms. Height rises from
1,854,167 to1,860,103 (5,936, about0.32%). Thus this is NOT asserted to improve
every metric over the prior principal. The prior202 low-height endpoint
16,927terms/H416,488 remains in the inherited package. The earlier200-variable
degree-eight companion had152 rows,10,392 terms and height13,654,244. The
new165-variable sextic strictly improves variables, rows, degree, support
and height against that particular earlier point.
Integer-domain forms and positive-domain forms are not silently compared as
natural-domain forms.

## 6. Reproducibility and scope of checks

`build.py` uses only the standard library. It reconstructs the new affine
chart directly from its inverse map and row operations and reconstructs every
contraction by deriving the monic polynomial again from the current literal
row, checking it against the recorded definition, then substituting exactly.
`check.py` uses independent exponent-count monomials rather than the builder's
sorted variable lists. It checks both affine inverse identities, all forward
positivity representatives, all original positive restoration DAGs, every
literal residual, every expanded coefficient, and the metrics. Its negative
controls reject a negative forward representative, a reversed restoration
order, a corrupted coefficient and a corrupted contraction definition.

`verify.py --deep` additionally performs a byte-identical temporary rebuild,
parses all rendered LaTeX residuals back to exact polynomials, remeasures all
current-source comparison equations, checks pins and the package manifest,
and replays the entire inherited finite calibration/construction closure.
Normal and optimized Python runs are both required and recorded. These finite
checks do not turn the inherited unbounded semantic proof into a new kernel
formalization.
