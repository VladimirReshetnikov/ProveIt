# Final manuscript review

Internal AI-assisted mathematical and scope review of
`report/ConZFC_Direct_Integer_Elimination_2026-10-25.tex`.
This review is independent of the manuscript authoring task. It is not
external human peer review or a new proof-assistant compilation.

## Finding and correction

One scope correction was required in the abstract. The phrase
“every reconstruction here is an integer polynomial” was too broad:
the 209-to-219 restoration of private quotient witnesses uses rational
expressions whose denominators are proved nonzero and whose values are
proved integral on zero sets. The separate 85-to-209 reconstruction
obtained from 124 acyclic unit pivots is an integer-polynomial map on
all integer inputs.

The manuscript author is applying the precise replacement:

> Each of these 124 coordinate reconstructions is an integer polynomial.

The body already distinguishes these two stages correctly. No other
critical mathematical or scope error was found in the reviewed text.

## Direct certificate and logical scope

The direct restoration argument agrees with the independent source-interface
audit. It correctly handles temporary zero bases: when a base is zero,
its denominator T is -1, so the divisibility needed to restore its old
private certificate is automatic. The joint residual's signs, group
formulae, and literal request table agree with the audited construction.

The main theorem explicitly identifies the inherited C222/ZF/ZFC
calibration. Its domain is unrestricted integers. The manuscript separates
the new ordinary mathematical proof and finite algebra certificates from
the inherited logical theorem and does not claim a newly compiled
end-to-end Lean or Rocq result.

The affine-scale obstruction is restricted to its stated weighted polynomial
ring and affine scales. It is not presented as a global minimality theorem.

## Independent calculation for the exact-degree witness

The following values were recomputed directly from the delivered principal
JSON graph and its reconstruction definitions, independently of the
manuscript's printed degree explanation. Let

    p = 1000000007

and use the supplied integer direction whose component associated with
free source index s is s+3. Propagation of degree upper bounds and the
corresponding leading coefficients modulo p gives:

| Reconstructed coordinate | Degree bound | Nonzero top coefficient modulo p |
|---|---:|---:|
| v79 | 8198 | 46952950 |
| v95 | 284 | 64682962 |

Because the recorded top coefficients are nonzero, these degree bounds
are attained. Source row 83 has the literal terms listed below; their
degrees after the same reconstruction are:

| Term | Degree bound |
|---|---:|
| -2 v1^2 | 12 |
| 2 v1 v12 | 7 |
| 2 v1 v13 | 7 |
| 2 v1 v97 | 11 |
| 2 v1 v98 | 11 |
| -v12^2 | 2 |
| -2 v12 v97 | 6 |
| -v13^2 | 2 |
| -2 v13 v98 | 6 |
| v17 v99 | 2 |
| -v79 v95 | 8482 |
| -v97^2 | 10 |
| -v98^2 | 10 |

Thus -v79*v95 is the unique highest-degree term, and

    (-46952950 * 64682962) mod 1000000007 = 140621492.

This nonzero residue proves that the row-83 residual has exact degree
8482. All residual upper bounds are at most 8482. Since the principal
polynomial is a sum of real polynomial squares, its maximal homogeneous
components cannot all cancel. Its exact degree is therefore

    2 * 8482 = 16964.

The final noncancellation argument is over the integers, rationals, or reals;
it does not assert that sums of squares cannot cancel modulo p.

## Review boundary

This final pass examined the manuscript for critical mathematical and scope
errors. Layout and completeness of the printed appendices are handled by
the separate document and artifact checks. No claim of a fresh audit of
the complete historical formal dependency closure is made here.
