# Verified integral transformations after the new arithmetic bootstrap

The semantic starting point of this component is the244-variable quartic
in `candidate244/equation.json`. Its new arithmetic theorem is supplied by
the main report. The present transformations are unconditional universal
identities and integral zero-set bijections. They introduce no further
arithmetic or proof-theoretic hypothesis.

## Credited affine exposure

The six coordinate shears and three hidden affine consequences come from
the inspected Residual Bases / Denominator Engineering package, whose
ordinary proof is copied as `AFFINE_EXPOSURE_SOURCE_PROOF.md`. They act on
unchanged syntax and Pell rows and remain valid after the new bootstrap.
They are not claimed as new mechanisms here. Their transfer to the new
equation is checked exactly, including the changed locations and literal
coefficients caused by replacing q by2z+1.

The source residual combinations are

    R21 - R6,
    R73 - R71 - 4 R70 - 8 R68,
    R119 - R117.

After the six listed coordinate shears they are affine with a unit
coefficient on, respectively, the coordinates named `add.145`, `mul.346`,
and `base4.T`. Replace their target rows by these combinations and remove
the three coordinates by the exactly recorded integral affine formulas.
This gives241 coordinates and178 rows. Source row90 is already affine
with unit coordinate `add.380`; removing it too gives240 coordinates
and177 rows but substantially increases the expanded support. The names
are historical coordinate labels. The literal coefficient lists and
restoration maps define every operation without relying on those names.

## Why every operation preserves integer solutions

For i different from j, replacing R_i by R_i+kR_j has inverse
R_i <- R_i-kR_j, so the common zero set is unchanged. Replacing one
coordinate by itself plus an integral affine expression in the other
coordinates is a bijection of integer lattices. If a residual is
epsilon*x+L=0, with epsilon=+-1 and L integral affine independent of x,
substitution x=-epsilon*L and deletion of that row give a bijection of
integer zero sets. Affine substitution preserves degree at most two.
Finally, the sum of integer residual squares is zero exactly when all
residuals are zero. These statements justify every recorded finite step.

The residual row reductions were found by a bounded pairwise coefficient
reduction. The selected sequence itself, not the search heuristic, is the
certificate. No global or local optimality is claimed. The241-variable
balanced endpoint uses only its first row operation; the lower-height
241 endpoint uses396 operations and the240 endpoint uses409.

## Selected endpoints

All variables range independently over all integers, and every variable
occurs in its collected polynomial.

| Directory | Variables | Rows | Degree | Terms | Height | Row height |
|---|---:|---:|---:|---:|---:|---:|
| `equation240` |240|177|4|21482|6144|64|
| `equation241_affine_balanced` |241|178|4|5351|15107|72|
| `equation241_affine` |241|178|4|9544|4512|64|

The240-variable endpoint minimizes dimension within this delivered set.
The balanced241 form has much smaller support. The other241 form has
smaller coefficients. None dominates all the others on these metrics.
The earlier252-variable current-source parent has182 rows,5340 terms,
height128446. In particular the balanced241 form uses11 fewer variables
and much smaller coefficients but11 more collected terms.

## Exact verification

`verify_affine.py` does not import a producer or a search routine. It
independently checks every coordinate inverse, elementary row inverse,
unit-affine restoration, absence of deleted coordinates, final renumbering,
and complete quartic expansion. It additionally constructs all244 original
coordinates as affine polynomials in the final coordinates and checks
every one of the181 original residual pullbacks against the inverse row
operations as a universal polynomial identity. The adjacent
`RESTORATION.json` is this complete explicit map.

Seven corrupted-artifact controls are required to fail, including changes
to the coordinate shear, row exposure, projection formula, composed map,
final residual, collected coefficient and final row operation. Each
selected endpoint passed the entire audit normally and with Python -O.
These checks authenticate the finite exact transformations. They do not
replace the main report's unbounded bootstrap proof or the inherited
C222/ZF/ZFC calibration.
