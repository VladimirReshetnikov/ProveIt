# Independent audit of the final coefficient reduction

## Outcome

**PASS.** The literal final polynomial in
`equations/quartic247/equation.json`, interpreted as the sum of all residual
squares, is related to the pinned weak-product source by invertible integer
coordinate transformations and invertible integer residual-row operations.
Every coefficient of its collected expansion was independently recomputed.
The complete printed residual appendix was parsed back into polynomials and
agrees with the JSON specification.

The result is a quartic in **247 unrestricted integers**, with **182
quadratic residuals**, **4,755 collected monomials**, coefficient height
**8,815**, and residual coefficient height **66**. There are 1,077 monomial
occurrences in the residual list. Every advertised variable occurs in the
collected final polynomial.

This review was performed separately from the author of `code/build_final.py`
within the AI-assisted research workflow. It is not outside human refereeing.

## Exact source boundary

The raw source is `source/equation247_weak/equation.json`, with SHA-256

```
14b814894521add09fb6847e59de2d802f2e466f6f9fc724f346a21461125a6b
```

The final residual equation has SHA-256

```
6df8f7de8b389084d6ce000f777f27ffc962e05b51217662e680201cffd1578d
```

The complete collected polynomial has SHA-256

```
19b2bc4e8cbb8d112feed0b88ca6c91884a40985745026eed020a78eee35187f
```

The raw source's mathematical calibration and new sign-recovery theorem are
not inferred from this finite audit. They are stated and proved separately
in the research article and its source proof closure. The earlier source
compiler's independent checker separately covers its own 18 Horn edits,
204 monic restorations, 70 integer translations and coefficient collection.

## Independent arithmetic implementation

`code/check_final.py` imports only Python's standard library. It imports
neither `build_final.py`, the source producer, its eliminator, nor an external
symbolic algebra system. Unlike the producer's repeated-index monomials,
the checker uses sparse exponent-vector monomials. A coordinate shear is
expanded with the binomial theorem. Sum-of-squares collection uses the
ordered Cartesian product of monomials, independently of the producer's
upper-triangle accumulator.

For each of the 76 coordinate shears, the checker applies the stated
substitution to all residuals and immediately applies the opposite shear;
the original residuals must be recovered exactly. For each of the four
residual operations, subtraction of the same multiple must recover the
changed row. It also applies the entire reverse row sequence and the entire
reverse coordinate sequence to the final residual list and recovers the
whole original list.

The checker separately constructs the full 247 by 247 integer coordinate
matrix and its proposed inverse, and the full 182 by 182 residual matrix
and its proposed inverse. Both left and right products must be identity.
Each elementary transformation has distinct target and source coordinates
or rows, so its determinant is one; the claimed total determinant one is
therefore justified by the explicit factorization. The published full
coordinate map agrees with the independently computed matrix.

These operations preserve the common zero set of the residuals. The
coordinate transformations give an integer bijection. Residual operations
change the sum-of-squares polynomial, while preserving its zeros because
they form an invertible transformation of the entire residual vector. The
review does not confuse equality of scalar polynomials with equivalence of
their integer zero sets.

## Historical shear transfer

All 76 ordered shears were checked against the actual source archive
`ConZFC_Shared_Residue_Bounds_2026-10-25.zip` in the repository snapshot
`3ecd6a6cf53d47519228328567f45fb7ee9781d9`.

`certificates/inherited_shear_equation.json` and
`certificates/inherited_shears.json` retain the exact historical inputs.
Together they occupy 49,044 bytes. Their pins and all 76 old-to-new
coordinate-name correspondences are in
`certificates/shear_transfer_provenance.json`.

The checker reads each historical coordinate's `pre_shear_origin.name`,
finds that exact name in the new raw equation, and verifies that the new
indices and coefficient equal the recorded transferred step. It checks
the complete ordering and the whole literal name-mapping certificate.
This verifies attribution and the transfer recipe; it does not assert that
the two source equations are equal or have identical coefficient changes.

## Printed specification and exact metrics

The independent checker reads `report_inputs/residuals.tex` as mathematical
input. It checks every one-based residual number, parses every signed
coefficient and power, converts one-based printed coordinates to the JSON
indices, and compares the resulting 182 polynomials. It rejects any
unrecognized noncomment material in that file. It also checks the readable
residual export and the printed metric macros.

The collected expansion, not a degree upper bound from the residual format,
establishes exact degree four, the exact 4,755-term support, and maximum
coefficient 8,815. The domain remains all of the integers in both source
and final specifications.

## Meaningful corruption controls

The following eight altered artifacts are separately rejected:

1. A changed coordinate-shear coefficient.
2. A false historical coordinate name in the transfer certificate.
3. A changed residual-row coefficient.
4. A changed final residual coefficient.
5. A changed collected polynomial coefficient.
6. A changed coefficient in the published complete coordinate map.
7. A changed coefficient in the printed TeX appendix.
8. Reinterpreting the final variables as nonnegative integers.

All required conditions raise explicit exceptions; none relies on Python
`assert`. Normal and optimized runs are recorded in
`FINAL_ALGEBRA_NORMAL.json` and `FINAL_ALGEBRA_OPTIMIZED.json`.

## Scope

The audit verifies the exact finite objects, all stated algebraic maps and
their inverses, historical name transfer, the coefficient census, and the
printed mathematical specification. It is not a search for integer zeros,
a consistency decision, a minimality proof, an external novelty survey, or
a new Lean/Rocq or encoded object-ZFC derivation. The report's unbounded
arithmetical theorem and inherited refutation calibration remain explicit
dependencies of the consistency interpretation.
