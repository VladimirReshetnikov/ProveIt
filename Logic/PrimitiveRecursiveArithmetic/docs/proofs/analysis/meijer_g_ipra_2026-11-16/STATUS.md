# Verification status

## Completed in this archive

- Human mathematical report: complete at the stated constructive/certificate level.
- LaTeX build: successful, 51 pages.
- Coverage audit: 107 source claim families (`P=46`, `Q=30`, `C=29`, `R=2`, `X=0`).
- Exact arithmetic regression: 1,000 checks passed.
- High-precision numerical regression: 63 checks passed at 80 decimal digits.
- PDF preflight: opens successfully, 51 letter-size pages, unencrypted, embedded fonts, bookmarks, no preflight warnings.
- Visual inspection: title, contents, theorem-heavy pages, special-function pages, coverage ledger, appendices, and references sampled from rendered pages.

## Deliberately incomplete

- `lean/FiniteCore.lean` contains `sorry` placeholders.
- The analytic contract structures have not been compiled into bounded object-language checkers.
- No main theorem has yet been proved as `[] ⊢[PRAAx] phi`.
- The Wimp transform is reduced to the certified kernel principle after expansion of its auxiliary kernel, but its long normalization and maximal test class are not separately developed.
- “Practical numerical contour integration” is not treated as a mathematical theorem; only a certified quadrature architecture is provided.

## Important logical reading

All real and complex statements are schemas for fixed primitive-recursive names, finite branch and apartness data, and requested precision. The report does not postulate arbitrary real/complex sorts, choice, unrestricted analytic continuation, or an identity theorem over arbitrary open sets.
