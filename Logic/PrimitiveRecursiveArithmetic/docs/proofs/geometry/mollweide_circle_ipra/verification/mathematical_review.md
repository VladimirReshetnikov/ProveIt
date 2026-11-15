# Mathematical review checklist

Date: 15 November 2026

## Statements

- Both standard Mollweide quotient formulas appear with the conventional side
  and opposite-angle notation.
- The law of tangents uses `tan((A-B)/2) / tan((A+B)/2)`.
- The law of cotangents uses `cot(A/2)/(s-a) = 1/r` cyclically and includes the
  standard inradius square formula.
- The three circle segment-product statements match their usual external,
  internal, and tangent configurations.

## Constructive safeguards

- Polynomial/cross-multiplied forms are proved before quotient forms.
- Every division or cancellation names a positive/apartness premise.
- Root separation is required before cancelling the factor `w-u`.
- Unsigned chord/secant lengths are derived from the signed theorem using
  explicit order data.
- The report does not infer apartness from `not (x=0)`.
- The first-order iPRA claim is a schema for fixed PR names, not quantification
  over all functions or all completed real numbers.

## Algebra audit

- 30 exact symbolic/rational checks passed.
- No floating-point arithmetic is used in the checker.
- The inradius formula has both a direct Heron proof and an independent
  denominator-free polynomial certificate.

## Artifact audit

- LaTeX build completed successfully: 25 pages.
- All cross-references resolved.
- PDF rendered at 180 DPI; contact sheet and selected full pages were inspected.
- No clipping, overlap, black squares, or broken glyphs observed.
- PDF text extraction produced no replacement characters.
- All fonts reported by `pdffonts` are embedded.
- Lean/Lake unavailable; Lean status is explicitly marked uncompiled.
