# Exact projection lemmas and the scope of the rank certificates

This note concerns a finite list of quadratic or affine polynomials
`R_1,...,R_m` with integer coefficients in unrestricted integer variables.
Its results are algebraic and have no logical-calibration hypothesis.

## 1. A common Hessian direction permits a quadratic graph projection

Write `H_i` for the ordinary Hessian matrix of `R_i` and `l_i` for the
linear coefficient vector. If an integral vector `d` belongs to the common
kernel of all `H_i`, the exact identity is

    R_i(x+t d) = R_i(x) + t (l_i · d).

Thus this criterion excludes both a squared moving coordinate and every
mixed term involving it. A primitive vector `d` extends to an integral
unimodular coordinate matrix. In those coordinates, all the residuals have
the shape

    R_i(t,z) = a_i t + q_i(z),       a_i in Z, deg(q_i) <= 2.

If the integer slopes `a_i` generate the unit ideal, Bezout coefficients
produce a residual combination `t+q(z)`. That primitive combination can be
completed to a unimodular row transformation. Subtract its constant slope
from each other row, then set `t=-q(z)`. The remaining residuals have degree
at most two, and the omitted coordinate has a unique integral restoration.
One variable and one residual have been removed. Consequently the sum of
the remaining residual squares still has degree at most four.

An existing slope `+1` or `-1` is a particularly simple special case.
Primitivity of the coordinate direction alone does not suffice: if all
slopes are divisible by a nonunit, ignoring the corresponding divisibility
condition could create spurious integral solutions.

## 2. An affine residual consequence is a different elimination mechanism

Suppose an exact constant rational combination of residuals is an affine
polynomial `L(x)`. Clear denominators and normalize its integer content.
If the gcd `g` of its linear coefficients divides its constant coefficient,
divide the affine equation by `g`. Its linear coefficient vector is then
primitive. A unimodular integer coordinate change makes this affine
equation `t+c=0`, and substituting `t=-c` in every other residual preserves
degree at most two. An existing unit coefficient permits direct substitution
without a preliminary coordinate change.

This is valid even when the eliminated coordinate occurs quadratically in
other rows. It is therefore not subsumed by common-Hessian projection.
If a coefficient of `R_j` in the affine combination is nonzero, the equation
`R_j=0` follows from `L=0` and the other residual equations. That row can be
omitted. Integer witness restoration is exact because the substitution has
integer coefficients. Nonunit constant coefficients in the row combination
cause no issue: the implication uses the fact that a nonzero integer times
an integer is zero only when that integer is zero.

For example, `R_1=x+y` and `R_2=x^2+y^2-1` have zero common Hessian kernel,
but `x=-y` eliminates a coordinate while keeping degree two.

## 3. The exact additional affine projection found in this iteration

In the 236-variable factorial-free two-square system, residual 82 is

    x96 - x9 - x10 - 4*x20 - 2*x23 - 2*x27 - 2*x29
        - 2*x31 - 2*x33 - 4*x35 - 2*x36 - 2*x39
        - 2*x42 - 4*x61 - 2*x62.

Indices here are zero-based and refer to the literal input variable list.
Solve this equation for `x96`, substitute the resulting integer linear
polynomial into all other rows, and delete residual 82 and coordinate 96.
This yields 235 variables and 170 quadratic residuals, with a bijection of
integer zero sets. Exact certificates record the input/output hashes,
the replacement polynomial, the omitted row, and the ordered variable list.
The transformation does not depend on the C222 arithmetic interpretation.

Before subsequent residual-basis reductions, the sum of squares has degree
4, 13,632 nonzero collected terms and coefficient height 16,924. Three
support-preserving elementary row operations give 10,496 terms and height
16,866. A separate sequence of 433 elementary row operations gives 18,550
terms and height 4,576. These are different final polynomials with identical
integer zero sets. The exact row-operation lists are the certificates;
the search heuristic is not part of the theorem.

The other inspected balanced 235-variable system also had one affine row.
Eliminating its unit coordinate 97 gave 234 variables and 171 rows, but
the resulting 20,745-term, height-6,144 polynomial is dominated by the
selected 234-variable construction on the measured support/height axes.
It is not selected as a final endpoint.

## 4. What the finite rank computations establish

The constant-row-combination search takes the matrix whose rows are the
quadratic coefficient vectors of the residuals. Its left kernel consists
exactly of the constant combinations with no quadratic part. Full row rank
therefore rules out any nonzero affine consequence formed by a constant
row combination.

Separately, full column rank of the vertically stacked Hessians proves
that their common kernel is zero. A full-rank minor modulo a prime suffices
to prove full rank over the rationals: its determinant is an integer which
is nonzero modulo that prime and thus nonzero in characteristic zero.

The inspected primary 234-variable system has quadratic row rank 171,
equal to its number of rows. The newly projected 235-variable two-square
system has quadratic row rank 170, equal to its number of rows, and zero
common Hessian kernel. Elementary invertible constant row transformations
preserve both conclusions.

These checks certify exhaustion of two precisely stated moves on the
given presentation: a constant-coefficient affine residual consequence,
and a common-Hessian direction with coordinate-independent residual
slopes. They do not certify a minimum variable count for this arithmetic
problem, for this ideal, for all quadratic presentations, or for general
Diophantine equations. They also do not preclude a nonlinear coordinate
change or a different semantic construction.

## 5. A counterexample to a stronger local-optimality claim

Consider

    R_1=x^2-1,      R_2=xy-1,      R_3=y^2-1.

The quadratic parts `x^2,xy,y^2` are linearly independent. The common
Hessian kernel is zero. Nevertheless,

    y R_1 - x R_2 = x-y.

The residual ideal has an affine consequence using polynomial coefficients.
Set `y=x`; all three remaining equations then equal `x^2-1=0`, leaving one
variable and one residual. Thus even the two rank certificates together
do not establish local optimality under arbitrary quadratic-preserving
algebraic transformations.

An exact next research step is a degree-three Macaulay calculation: combine
the residuals and their products by single variables, cancel all terms of
degree at least two, and look for further primitive affine consequences.
Any accepted result should retain an explicit polynomial-combination
identity and an integral restoration map. A bounded calculation at degree
three is a useful search certificate; failure at that degree would not
rule out higher-degree consequences.

## 6. Verification boundary

The supplied Fraction-arithmetic search recomputes the quadratic row rank
and checks every emitted affine relation against the actual input rows.
The projection constructor substitutes the literal integer polynomial,
collects the complete quartic, and emits a restoration certificate.
Separate exact checking is required before integrating a selected endpoint.
These finite algebraic operations preserve an inherited zero-existence
calibration but do not establish that calibration or prove consistency.


