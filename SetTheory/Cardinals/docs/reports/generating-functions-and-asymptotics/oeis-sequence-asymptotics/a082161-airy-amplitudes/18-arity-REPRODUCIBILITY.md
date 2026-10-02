# Reproducing the fixed arity Airy results

## Requirements

- Python 3 with SymPy (the production checks used SymPy 1.14.0)
- Bash and sha256sum
- Optional PDF rebuild: a TeX distribution with pdfLaTeX, AMS packages, Latin Modern, microtype, geometry, hyperref, enumitem, needspace and booktabs
- Optional image review: Poppler tools pdfinfo and pdftoppm

No network access is used by any check or PDF build. No third-party article text or dependency binaries are bundled.

## Run

Run `bash replay.sh` from any working directory. If the package contains SHA256SUMS, the script verifies it first. It then copies check scripts into a new output/replay-* directory and executes them there, preserving all supplied inputs. Assertions are exact rational or symbolic identities, with no floating-point Airy-root approximation.

Run `bash replay.sh --pdf` to perform the same checks and rebuild the supplied TeX. The builder creates missing TeX format/font maps locally from the installed distribution; it does not install packages. In a checksummed release it puts PDF build products in output/article. A missing TeX package is an environment requirement, not a mathematical check failure.

## What is checked

1. Exact left harmonics, all residue critical-variance and gradient/trace identities, and extra-bottom column losses
2. General-q scalar/profile coefficients through epsilon^4 and epsilon^5, checked by both producer elimination and an independent direct-linear-system recurrence
3. Exact source seeds, completed-run positive representations, source-to-signed transforms, scaled delay coefficients, and first ratio constants
4. The optional included cancellation proof has separate producer and independent symbolic/order checks

These finite checks supplement the supplied analytic arguments. They do not numerically certify compactness or asymptotic error transfer. The analytic review documents identify exactly which proof files were reviewed by hash.

## Main deliverable

`report/fixed-arity-airy-expansions.pdf` is the unified mathematical report. Its editable source is the adjacent TeX file. The detailed proof documents preserve the complete leading, relaxed all-orders, and signed-delay arguments. Amplitudes are positive but not explicitly evaluated. All asymptotics keep k fixed; every finite expansion order has its own controlled remainder.
