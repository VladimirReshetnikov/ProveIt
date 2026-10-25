# Independent audit of common-Hessian-radical projection

## Scope and result

The main 240-integer source has also been checked through its entire
six-step common-radical projection and subsequent 147 elementary row
operations. The principal final equation has **234 integer variables,
171 quadratic residuals, 19,050 quartic monomials, and coefficient height
4,480**. Its row coefficient height is 64. The independently modified
two-square source gives a 236-variable sparse option. An additional exact
affine projection of that source, followed by 433 row operations, gives
the selected 235-variable option:

| Audited output | Integer variables | Residuals | Quartic monomials | Coefficient height |
|---|---:|---:|---:|---:|
| `eq234` | 234 | 171 | 19,050 | 4,480 |
| `beta235_reduced` | 235 | 170 | 18,550 | 4,576 |
| `eq236_sparse` | 236 | 171 | 4,947 | 16,866 |

These numbers refer to the exact currently delivered files. The individual
machine-readable audit receipts identify the input and output by canonical
SHA-256 and contain all reproduction details. They do not certify a global
minimum over representations or source calculi.

The proposed `factorial_free` projection was checked independently against
the 242-integer, 178-residual source named
`factorial_free_affine242_balanced`. All six projection steps pass exact
coefficient checks. The result has 236 unrestricted integer variables,
172 quadratic residuals, and a quartic sum of squares with 4,947 nonzero
monomials and coefficient height 16,924. The source sum of squares has
5,018 monomials and height 7,968: the reduction saves variables, equations,
and monomials but increases coefficient height. Its largest individual
residual coefficient remains 64.

The input and output SHA-256 identifiers below hash canonical JSON
(`sort_keys=True`, compact separators, final newline), not the raw source
file bytes:

- Input: `3970268165d2dea4914550913d1e882f9c6f108008de677a919fc2a01b8740a5`.
- Output: `4d7316d957bced303c264001383433ebc889602488caf170e8c9f4b105d4c8d6`.

This audit establishes the new algebraic equivalence. It does not independently
reprove the inherited source's proof-calculus and arithmetic-encoding calibration.
The implication for Con(ZFC) uses that inherited theorem as an explicit dependency.

## Exact theorem

Let `Q_1,...,Q_m` be integer polynomials in `n` variables, of degree at most
two. Write `H_i` for their Hessian matrices and `l_i` for their linear
coefficient vectors. Suppose an integer vector `v` and a coordinate `p`
satisfy

1. `H_i v = 0` for every `i`;
2. `v_p = 1`;
3. for a selected row `r`, `a_r := l_r · v` is either `1` or `-1`.

For an `(n-1)`-tuple `z`, insert zero in coordinate `p` to obtain `y`.
Define `a_i := l_i · v` and

`R_i(z) = Q_i(y) - a_r a_i Q_r(y)` for `i != r`.

All `R_i` have integer coefficients and degree at most two. The integer
zero sets of `(Q_i)` and `(R_i)` are in explicit bijection. Consequently
the sums of squares `sum_i Q_i^2` and `sum_{i != r} R_i^2` have integer
zeros simultaneously, and the second polynomial has total degree at most four.

### Proof

For every integer `t`, the exact quadratic translation formula is

`Q_i(y+t v) = Q_i(y) + t(l_i · v) + t y^T H_i v + (t^2/2) v^T H_i v`.

The last two terms vanish by hypothesis. Thus, with `x = y+t v`, the
original rows are `Q_i(y)+a_i t`. The selected row vanishes precisely when
`t=-a_r Q_r(y)`, because `a_r^2=1`. Substitution gives exactly the displayed
`R_i`; the selected row becomes zero identically. This defines the lift

`t=-a_r Q_r(y)`, `x_i=y_i+v_i t`.

Conversely, from an original integer solution `x`, set `t=x_p` and
`y_i=x_i-v_i x_p`. Then `y_p=0`, and the original selected row forces
`t=-a_r Q_r(y)`. The other equations give `R_i(z)=0`. These two maps are
mutual inverses: projection of a lifted `y` is `y`, and lifting the projection
of a root `x` recovers `x`. Every operation is integer polynomial arithmetic.
Finally, a sum of integer squares vanishes if and only if every summand
vanishes. This proves the claim.

The coordinate transformation `x=y+t v`, with `y_p=0`, is unimodular:
its inverse is `t=x_p`, `y_i=x_i-v_i x_p`. No division, congruence side
condition, existential choice, or unproved integrality statement is hidden
in the elimination. The proof is elementary and formalizable in ZFC.

## Why the three hypotheses matter

The unrestricted integer domain is essential. A shear generally does not
preserve nonnegative coordinates; using the same reduction over naturals
without transporting all positivity conditions would be invalid.

The common Hessian condition is what preserves quadratic degree. A mere
zero value of `v^T H_i v` removes the `t^2` term but can leave `t` multiplied
by a variable, so the coefficient of `t` need not be a unit.

A nonunit slope cannot be inverted over the integers. For example,
eliminating `t` from `2t-1=0` by rational substitution would spuriously
accept an inconsistent integer equation. The checker rejects slopes other
than `1` and `-1`.

## Independent implementation

`audit_projection.py` uses only Python's standard library and imports none
of the discovery/reduction implementation. The reducer performs a symbolic
shear and substitution. The independent checker instead computes `H_i v`
and uses the direct linear combination

`Q_i|_(x_p=0) - a_r a_i Q_r|_(x_p=0)`.

It checks every residual coefficient, selected solution polynomial,
coordinate list, metadata-derived intermediate digest, and final equation.
It independently expands every residual square and compares the entire
delivered quartic, as well as the variable, residual, term, degree, and
height counts. It performs 72 additional finite arithmetic checks of the
lift and inverse maps on arbitrary integer points, without supposing that
the consistency equation has a root. These finite controls supplement the
exact coefficient proof.

Eight deliberate mutations are rejected: a direction coefficient, slope
sign, pivot-solution coefficient, retained coordinate list, variable domain,
quadratic source term (with the input digest refreshed), nonunit selected
slope (also with the digest refreshed), and output digest. The source-term
mutations ensure that algebraic checks, not merely stale hashes, reject
incorrect certificates.

## Exhaustion within this specific method

For the final system the checker stacks all Hessian rows and finds full
column rank 236 modulo the explicitly verified prime 1,000,003. It records
236 independent original Hessian-row indices and their modular elimination
pivots. A nonzero 236-by-236 determinant modulo a prime is nonzero over the
integers. Therefore the stacked Hessians have rank 236 over the rationals,
and the final common Hessian radical is zero.

This rules out a further nonzero common-radical direction of the present
type: a constant direction along which every residual has degree at most
one with constant slope. It does not rule out an affine row-combination
elimination that permits other residuals to remain quadratic along that
direction. For example `x+y=0`, `x^2+y^2-1=0` has zero common Hessian
radical but allows immediate elimination of `y=-x`. It also does not rule
out nonlinear transformations, a different residual representation of the
same zero set, or a smaller Diophantine equation from another source.
No global minimality claim is supported by the computation.

## Elementary integer row changes

After projection, any operation `Q_i <- Q_i + k Q_j` with integer `k` and
`i != j` preserves the common zero set. Its inverse is the same operation
with `-k`, provided the operations are reversed in order. Thus the entire
certificate gives a matrix in `GL_m(Z)` with determinant one, although no
large matrix needs to be formed. Quadratic degree and integrality are
preserved term by term. The sum-of-squares polynomial usually changes, but
its zero set remains exactly the common zero set of the residuals.

The independent checker replays every row change with exact integer sparse
coefficients, then replays every inverse and requires recovery of all
original residuals. It checks the new quartic expansion coefficient by
coefficient and all metrics. Four additional mutation controls reject an
operation with identical source and target row, a changed multiplier, an
omitted operation, and a false output digest.

## Reproduction

Run, using the packaged source and output paths:

```text
python3 audit_projection.py SOURCE_EQUATION.json OUTPUT_DIRECTORY --output AUDIT.json
```

`OUTPUT_DIRECTORY` must contain `equation.json`, `projection_certificate.json`,
`expanded_polynomial.json`, and `metrics.json`. A failed check raises an
exception and returns nonzero status. Checks use explicit exceptions and
remain active when Python is run with `-O`.

For a row-operation stage use the same command with `--row-mode` and a
directory containing `row_certificate.json` instead of the projection
certificate. The audit does not import or execute either optimizer.

## Additional affine projection in the two-square source

The common-radical reduction of the two-square source has 236 variables
and 171 residuals. Its residual 82 is an affine equation. In the source's
zero-based variable indexing it solves coordinate 96 exactly as

```text
x96 = x9 + x10 + 4*x20 + 2*x23 + 2*x27 + 2*x29 + 2*x31
      + 2*x33 + 4*x35 + 2*x36 + 2*x39 + 2*x42 + 4*x61 + 2*x62.
```

Substituting this affine expression in every other residual and deleting
residual 82 produces 235 variables and 170 quadratic residuals. The
unreduced quartic has 13,632 monomials and height 16,924. The selected
433-operation row-basis certificate changes these to 18,550 monomials
and height 4,576. Variable and residual counts remain 235 and 170.

The affine-projection output has canonical SHA-256
`4a2bb9e1914825b661ccfb032e77e9f6a874d096e9e4b8e35c3773b86327d1fa`.
Its source certificate uses raw file hashes instead; the raw output hash
is `b4af0f075e1ff9685f143002175cc2377c8488294f913c8c7843857548f5b310`.
The selected row-reduced output has canonical SHA-256
`9963123d2504459a198a86a701e92922d8b7ae5af1e4905347e78de20efbeb7f`.

### General affine-consequence theorem

Suppose an exact integer row combination `L=sum_j lambda_j Q_j` is affine,
its nonzero content is `h`, and the primitive affine polynomial `L/h`
has coefficient `a=+1` or `-1` at coordinate `p`. Write

`L/h = a*x_p + b(y)`.

Choose a row `r` with `lambda_r != 0`. Substitute `x_p=-a*b(y)` in all
rows except `r`, and omit row `r`. This preserves the integer zero set
under an explicit bijection with one fewer coordinate.

Indeed every old solution satisfies `L=0` and therefore the displayed
unit-coefficient solution for `x_p`. Conversely, the substitution makes
`L=0` identically. If all retained rows vanish, the exact combination gives
`lambda_r Q_r=0`; since the nonzero integer `lambda_r` is not a zero
divisor, `Q_r=0`. The omitted row's combination coefficient need not be a
unit. The variable's coefficient in the primitive affine equation must be
a unit for this particular division-free projection. All substitutions are
affine, so the residuals remain quadratic. Projection drops `x_p`, and the
inverse reinserts `-a*b(y)`. No assumption about the existence of roots is
made.

For the delivered instance, `L=Q_82`, `h=1`, `lambda_82=1`, and `a=1`;
thus the theorem specializes directly to deleting an existing affine row.

### Independent checks for this stage

The checker verifies the exact affine row combination, the cancellation
of every quadratic coefficient, the content, the unit coordinate coefficient,
the restoration expression, and the nonzero coefficient of the omitted
row. For substitution it independently splits each quadratic residual as
`A*x_p^2+B*x_p+C` and constructs `A*S^2+B*S+C`, where `S` is the affine
restoration polynomial. It compares every output residual and the entire
expanded quartic. Five additional mutations are rejected: a row-combination
coefficient, affine-identity coefficient, restoration coefficient, choice
of a row absent from the combination, and a false content divisor.

Run this stage with `--affine-mode`; run the subsequent 433-row-operation
stage with `--row-mode`. These are exact arithmetic certificate checks
accompanied by an ordinary mathematical proof, not a Lean or Rocq proof.

