# Artifact verification receipt

Verified 1 October 2026.

## PDF and source

- Mathematical TeX source SHA-256: `40d52eb680316dd97f9c5c39fd208c341bc15c1c4301169da86f22d1d0751ad3`
- PDF SHA-256: `c85426482011fadfe29f33136dc4462e6226b4416d68a5300413c58923b8a9ed`
- 17 pages, all US Letter (612 by 792 points)
- 18 embedded, subsetted, scalable Type 1 fonts; Unicode mappings present
- 106 link annotations, including internal cross-references and external references
- No empty pages, unresolved `??` references, LaTeX warnings, overfull boxes, or underfull boxes in the final build
- PDF text extraction completed successfully

Every delivered page was rendered at 110 dpi using Poppler. Pages 2–13 were checked to be pixel-identical to the already visually approved pages of the preceding proof-complete version. The final changed pages 1 and 14–17 were independently visually inspected for readable formulas, clipping, collisions, margins, page numbering, and section transitions. The bibliography uses a slightly smaller readable font to avoid an otherwise nearly empty final page. No rendered images or local TeX caches are included in the distribution.

An isolated rebuild copied only the final TeX source and build script to a new empty directory. It produced the same 17-page layout with no warnings or box defects, and its extracted layout text is byte-identical to that of the delivered PDF. See `build-smoke.txt`. PDF serialization bytes may differ because of metadata and file identifiers.

## Mathematical computation

The following completed successfully with exit status zero. Their log files and JSON results are included in this directory.

1. `python3 code/check_two_coefficients.py`
   - First two residual coefficients vanish
   - Exact rational second coefficient is reconstructed
   - Third residual coefficient vanishes after substitution
2. `python3 code/check_bell_comparison.py`
   - Independently differentiated first three residual coefficients vanish
   - First and second Takeuchi-minus-Bell coefficient identities hold exactly
3. `python3 code/derive_residual.py --include-p3 --order 5 --output receipts/result-recomputed.json`
   - Exact canonical ODE for p3 holds
   - Residual coefficients through order four vanish
   - Order-five residual is computed without being forced to zero
4. `python3 code/test_generator.py`
   - Reconstructs p1 and p2
   - Verifies the triangular ODE for a generic symbolic coefficient
   - Checks finite-product coefficients through order six
   - Verifies p3 cancellation through order four
5. `python3 code/check_independent.py`
   - Independent explicit fourth-order formula equals the generic H3
   - Degree-12 numerator ansatz fails; degree-13 ansatz succeeds
   - H3/w^5 tends to -1/24 and p3/w^4 tends to 1/72
6. `python3 code/check_third_literal.py`
   - Imports none of the other checkers
   - Verifies literal manuscript H3 and p3 with independent Poisson moments
   - Checks the canonical ODE, leading growth, and rational derivative degrees
7. `python3 code/check_inverse.py`
   - Imports none of the other checkers
   - Solves the inverse coefficient equation with symbolic log C
   - Verifies the first two reversion residual cancellations and B/w tending to 3/8
   - Checks eight scaled derivative/growth bounds used in the proof
8. `python3 code/check_numeric.py --max-n 1500 --output receipts/numeric-recomputed.json`
   - Recomputes all used Takeuchi numbers as exact integers
   - Checks the first ten sequence entries
   - Reproduces the stored diagnostic errors with 70-digit arithmetic

Symbolic checks establish finite algebraic identities. They do not by themselves establish uniform analytic remainders or the coupling argument. Those proofs were read separately in the integrated mathematical review. The inverse checker corroborates algebra and derivative bounds; the finite Newton error and its interval control were reviewed as a proof. Numerical diagnostics use unenclosed historical constant digits and are not numerical certificates.

## Mathematical review and reproduction

The complete integrated source was independently read and approved against the hashes above. See `mathematical-review.md` for the faithful coupling, strict positivity, fixed-order hierarchy, third coefficient, explicit remainder, real inversion, and ceiling findings. `third-coefficient-review.md` and `inverse-review.md` give separately organized checks of the additions.

Run `python3 replay.py --build-pdf` for a complete isolated replay; omit `--build-pdf` when TeX is unavailable. The replay verifies all distributed hashes first and never overwrites the delivered PDF or recorded receipts. It writes a unique result directory containing each command, exit status, output, and build check. The separately differentiated Bell calculation can take a few minutes. Python, SymPy, and mpmath suffice for the algebra and diagnostics; the optional PDF build also needs a POSIX shell and TeX, and uses Poppler for page/text comparison when available.

The distribution is a whitelist of the PDF, TeX source, portable Python code, build and replay entry points, requirements, and verification receipts. It excludes generated caches, auxiliary files, rendered images, working research notes, and unrelated files. `SHA256SUMS` covers all distributed files except itself. Rebuilding a PDF is not expected to reproduce its metadata bytes, so compare extracted layout text as the replay does.
