# Suggested ProveIt intake

## Title

**Eliminating Auxiliary Witnesses in Diophantine Consistency**

Suggested unnumbered slug: `polynomial-centers-staged-indices`.
Choose a collection number at integration time; the repository may have advanced
since the pinned comparison commit.

## Collection summary

Three new certificate reductions yield four fully specified consistency
polynomials. A deterministic polynomial Pell comparison center, composed with a
signed cap and semantic anchor, gives a direct quartic in 314 unrestricted
integers with 204 residuals, 5,721 collected monomials, and height 128,446. A
descending-binomial factorial fixed point and one-row cap give a direct quartic
in 233 nonnegative integers with 182 residuals, 7,313 monomials, and height
86,543,666. A staged index-divisibility deduction removes the compact artificial
scale, yielding ten-positive-variable circuits with 78 operations/degree 630 and
79 operations/degree 468. The compact pair saves six operations relative to the
84/436 and 85/328 parents while increasing degree.

## Comparisons to preserve

- Direct integer endpoint: package 131's 324 variables, 208 rows, 5,808 terms,
  height 128,446 becomes 314 variables, 204 rows, 5,721 terms, same height.
- Natural endpoint: strictly improves package 129's recommended 234/183/9,019/
  87,741,134 metrics and its denser 233/182/50,762/88,674,690 endpoint in the
  displayed weak-dominance comparison, with at least one strict improvement.
- Compact endpoints: arithmetic-cost improvements with degree increases, not
  global Pareto improvements and not a reduction in fixed numeral size.

The baseline is ProveIt commit
`1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`, including packages 127–133.
The direct arithmetic is independent of K215 and Jones; the compact arithmetic
retains its native/K215 ancestry. Do not erase this distinction in the overview.

## Recommended entry points

| Purpose | Path |
|---|---|
| Full paper and editable master | `report/report.pdf`, `report/report.tex` |
| Main integer equation and collected expansion | `direct/equation.json`, `direct/expanded_polynomial.json` |
| Main natural equation and collected expansion | `natural/equation.json`, `natural/expanded_polynomial.json` |
| Compact equations | `compact/equation78.json`, `compact/equation79.json` |
| Offline exact replay | `verify.py` |
| Inherited boundaries | Component READMEs, `direct/proofs/INDEX.md`, source ledgers |
| Exact file integrity | `SHA256SUMS` |

## Status wording

The package proves the new arithmetic transformations by ordinary unbounded
arguments, composes them with named inherited refutation calibrations, and checks
the finite polynomial algebra independently. It is not a new full Lean or Rocq
formalization, a proof of Con(ZFC), a globally minimal equation, or a claim of
worldwide priority. Its independent reviews are separate AI-assisted reviews.

The source dependencies have been retained under short relative paths so the
bundle rebuilds offline. Historical texts are preserved for attribution; their
old package-relative links are resolved by the accompanying source ledgers.
The report's new sections and the top-level README define the current results.
