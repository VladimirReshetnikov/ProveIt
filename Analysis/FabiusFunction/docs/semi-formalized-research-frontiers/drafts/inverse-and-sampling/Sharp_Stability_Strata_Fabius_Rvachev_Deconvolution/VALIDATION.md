# Validation record

## Article and build

- Final article: 22 A4 pages.
- The PDF was regenerated from the delivered `article.tex` with three successful
  pdfLaTeX passes after the final source changes.
- The final LaTeX log contains no warnings, overfull boxes, underfull boxes,
  undefined references, or missing-character reports.
- Cross-reference types were checked: references to lemmas are labeled Lemma,
  rather than being mislabeled Theorem because of a shared theorem counter.
- The PDF's extracted text has no unresolved `??` cross-reference markers.
- Programmatic checks found no text blocks extending outside the page boxes.
- All pages were rendered during layout review. Contact sheets were inspected,
  and the principal theorem, leading-density theorem, and other selected pages
  were inspected at larger size. The final changed theorem page was re-rendered
  and inspected after the last cross-reference correction.
- This is visual and structural PDF validation, not a formal proof audit.

## Executed symbolic verification

`verification.py` completed successfully using Python 3.13.5, SymPy 1.14.0,
and mpmath 1.3.0. The recorded JSON status is `PASS`.

Exact rational checks covered Chebyshev orders 1 through 12: initial power-sum
cancellation, the nonzero first gap, the shifted construction, square-free
polynomials, and disjoint root sets. Moment-to-cumulant-to-polynomial recovery
was checked exactly for capacities 1 through 8, including repeated scales and
zero slots.

## Executed numerical diagnostics

The numerical run used 100 decimal digits, frequency 0.9, and a 220-factor
common up Fourier multiplier. At the smallest tested t = 2^-12, the halving
slopes were:

| Regime | m | Predicted | Computed |
|---|---:|---:|---:|
| Positive collision | 3 | 3 | 2.9999999998683037363 |
| Vanishing cluster | 3 | 6 | 5.9999999164164314285 |
| Positive collision | 5 | 5 | 4.9999999998130786161 |
| Vanishing cluster | 5 | 10 | 9.9999998632964711245 |

These are pointwise characteristic-function differences, NOT estimates of
L1 or total variation distances. The L1 asymptotics and sharpness in the article
are established by the analytical proofs, not by these diagnostics.

## Mathematical status

The article contains full conventional proofs, including matching-root counts,
separated cluster-factor extraction, cumulant bounds, symmetric Banach-space
Taylor cancellation, nonvanishing leading coefficients, and anchored positivity
certificates. It distinguishes a two-moving-point modulus from a fixed-base
modulus and separately treats vanishing and positive clusters.

There was no independent peer review, no Lean/Rocq verification, no exhaustive
literature-priority audit, no numerical integration of TV distances, and no
implemented certified feasible-fit optimizer. The article does not claim these.
