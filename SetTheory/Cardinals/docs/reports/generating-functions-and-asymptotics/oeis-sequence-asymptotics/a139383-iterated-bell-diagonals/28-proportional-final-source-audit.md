# Final integrated source mathematical review

Date: 2026-10-02. Verdict: **PASS**, retaining the dependency and scope qualifications of the independent proportional-depth audit.

Reviewed source: `proportional-depth.tex` (single file, no included mathematical source). Its exact SHA256 is `346eebade9485d0e5c091f206345458dcee727bdafba819763c8deb73bae5115`. Source and copied foundation hashes are recorded in `FINAL_SOURCE_SHA256SUMS` using package-relative paths. This report does not replace or modify the frozen original independent audit.

Compared against the approved research snapshot (SHA256 `2466012069be41cab1d5f8d1e0e985b9b36ebe909d0be925297ab52269515556`) and the full independent audit, the integrated source has no substantive mathematical transcription drift. In particular:

- Exact residue, factorial normalization, Stirling factor, shift exponential, and first correction agree
- Absolute transfer is established before positivity or division by the amplitude, uniformly on compact positive ratio ranges
- The complex-linear full-circle/two-lip functional has the correct orientation and supports the stated holomorphic extension
- Finite-iteration pre-crossing lip cancellation is expressly retained
- Interior quadratic-convolution normalization and the bounded accumulated error are correct; the limit on the left is exp(beta) I(beta)
- Isolated zeros and nonnegativity imply a strictly positive interior convolution integral, establishing positivity at every positive parameter
- Bounded floor phases are retained and are not differentiated during inversion
- Lambert-W normalization, first inverse coefficients, all-order recursion, and inverse remainder scope agree with the approved proof
- Smooth inverses remain explicitly distinguished from integer thresholds; no unconditional rounding rule or concrete numerical threshold certification is asserted

The added rational-slope residue-class observation is valid: the floor phase is constant on each arithmetic progression, allowing separate fixed-shift models with lattice bracketing. It does not resolve threshold rounding without forward error control.

The historical section was compared against the verified research source audit and the saved primary Prellberg slide-17 text. The specialization to a constant a0 and b(z)=z gives the displayed m^(−1−beta/3) J(beta) normalization. The factor I(beta)=beta J(beta) is correctly described as conditional on contour correspondence, normalization, and endpoint terms. The text properly credits the direct 2002 bivariate announcement and parabolic method, disclaims priority for the leading equivalent and formal corrections, and bounds the claims about what was not located in the inspected sources. This is a transcription and algebra review, not a new exhaustive literature search or novelty certification.

One minor issue was found and fixed before this hash was pinned: the branching identity had a comma in the exponent. The final source now reads E[Z_(m−1)^n] and explicitly restricts that identity to m≥1. No other mathematical correction was required.

The original positivity certificate and finite-contour foundation remain dependencies, rather than newly reverified arithmetic in this review. Visual PDF quality, compilation reproducibility, numerical diagnostics, and the final archive manifest are separate checks and are not certified by this source review. Any subsequent mathematical source change requires reconciliation against this pinned version.
