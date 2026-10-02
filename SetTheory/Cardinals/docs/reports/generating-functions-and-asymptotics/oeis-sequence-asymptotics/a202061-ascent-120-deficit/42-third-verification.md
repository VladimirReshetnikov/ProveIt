# Verification and audit boundary

## Mathematical signoff

The coefficient upper proof is developed and independently checked in `audit/one-sided-next-constant-proof.md`. The distinct normalized-row coefficient lower proof is adversarially reviewed in `audit/lower-construction-audit.md`. Their bounds match through additive o(F/log n), with exact kappa. The integrated article, inverse corollary and scalar-action interpretation require a separate source/PDF review recorded in `audit/integrated-report-review.md`.

The source notes and their audit records are hash-bound in `audit/audited-proof-sha256.txt`. The lower note's original draft wording is retained rather than silently edited after review. Its audit supplies the current mathematical verdict.

## Reproducible checks

- `checks/check_dependencies.py` pins the complete approved second-order package to its original manifest and verifies its exact payload set
- `checks/third_order_checks.py` checks scalar-action algebra, angular constant combination, repair-scale inequalities, and high-precision constants from their exact definitions
- `audit/check_constants.py` independently reduces the discriminant amplitude and row mass modulo the defining cubic and checks the calibration constant algebra
- The inherited second-order, sharp-deficit and foundation check chains are replayed unchanged
- `check_manifest.py` verifies both the exact top-level payload file set and every digest

These scripts certify their stated finite/algebraic facts. The asymptotic uniformity, probability bounds and variational arguments are mathematical proofs, not consequences of numerical fitting.

## Rendering and release

`build.sh` performs two pdfLaTeX passes with a fixed timestamp. Overfull boxes and unresolved references/citations fail the build. All final PDF pages are rasterized for visual quality checks. The release generator refuses to proceed unless the current main TeX, three proof/corollary sections and final PDF hashes appear in the integrated review. It also checks that the reviewed source notes and dependency remain unchanged.

A deterministic ZIP is generated with fixed entry timestamps. The external `.zip.sha256` file identifies that exact archive; the internal `SHA256SUMS` identifies the exact released payload set.
