# Validation record

## Build and source portability

The final modular article compiles with `latexmk` to 22 PDF pages. The standalone LaTeX variant was independently compiled three times. Its 22 pages have exactly the same extracted text as the modular PDF. Both final TeX logs contain no LaTeX warnings, undefined references, or overfull boxes.

## Layout

All 22 pages were rendered at 120 dpi. The full contact sheet was inspected, followed by full-size inspection of the main classification and the J(3/5) theorem/proof. The bibliography was moved to a dedicated page to eliminate an orphan reference; the final reference page was inspected after that correction. No clipping, overlapping text, or broken mathematical glyphs was observed. A programmatic text-block check found no text outside the physical page bounds.

## Exact computation

`data/exact_results.json` records PASS at bound 500. The modular classifier was compared with an independently generated recurrence set over 76,115 coprime unordered pairs. Group-ring, exterior-algebra, symbolic substitution, recurrence-polynomial, and count regressions also passed. These finite checks test the implementation; the article contains the all-parameter proofs.

## Numerical computation

`data/numeric_results.json` records 38 comparisons at 90 digits and 38 comparisons at 140 digits, all passing the specified diagnostic thresholds. The integral representation and the analytic right sides are evaluated separately. These are not interval-certified bounds and are not used as the proofs of equality.

## Scope

No proof assistant was run. No numerical independence theorem is claimed. The package is a research contribution for independent mathematical review before repository integration, not a claim of exhaustive prior-art review.
