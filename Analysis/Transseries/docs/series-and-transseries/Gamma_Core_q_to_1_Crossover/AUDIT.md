# Audit record

## Mathematical checkpoints

The manuscript explicitly treats the following delicate points:

1. The real-index Euler–Maclaurin identity is proved by differentiating an
   infinite tail and accounting for the resulting affine ambiguity. It is
   not inferred from agreement at integer indices.
2. The fixed-K order h^(2K+1) is proved by comparison with truncation K+1;
   it is not incorrectly inferred from a weaker h^(2K-1) bound.
3. The optimal exponential constant in the explicit uniform error majorant
   is derived from Gamma-ratio and Stirling estimates. A modular far-index
   limit proves sharpness of the exponential action for the stated family.
4. The inverse proof retains the endpoint vanishing order of the residual.
   It does not divide by a nonexistent positive global minimum derivative.
5. The half-integer convergence theorem cancels all periodic Fourier terms,
   not only the first harmonic. Generic indices have a nonzero first
   harmonic and therefore factorial growth.
6. The half-integer flat defect follows from an exact product identity and
   the eta transformation. A convergent Taylor block is not identified with
   the canonical function without accounting for that defect.
7. The multinomial lower-limit formula requires strictly positive weights.
   Its upper bound is uniform as weights approach zero; the order of limits
   in the lower formula is stated separately.

These checkpoints describe the written proofs. They are not a claim of
independent peer review or formal proof-assistant verification.

## Recorded computational checks

`data/verification_quick.json`: all main-suite assertions passed, at
100 decimal digits. The rational Faulhaber comparisons are exact; the other
calculations are high-precision floating-point tests, not interval proofs.

`data/verification_supplement.json`: all eight supplemental checks passed,
at 100 decimal digits. They cover two multinomial specializations, two
endpoint-curvature identities, two half-integer sheets, and two relative
residual-derivative bounds.

The larger 190-digit exploratory run is not included as a completed result.

## PDF checks

- The self-contained source compiled with pdfLaTeX.
- Cross-references and citations were resolved after repeat compilation.
- No overfull boxes or undefined-reference warnings remained in the final log.
- One minor underfull bibliography paragraph remained; it does not clip text.
- All 30 pages were rendered and reviewed through two contact sheets.
- Representative formula and table pages were inspected at larger size.
- Text geometry was checked for content approaching the media-box edges;
  no edge violations were found.
- Representative pages were also rendered with Poppler's pdftoppm.

No font files or build intermediates are included in the delivery archive.
