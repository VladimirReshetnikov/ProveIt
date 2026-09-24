# Validation performed before delivery

## Mathematical scope

The note contains proofs of the universal statements. Its principal
sum-of-squares identity is independently derived from the binary Stern
recurrence; it is not extrapolated from the computed cases. The exceptional
case t=0 is treated explicitly. Root counts in the spectral theorem include
algebraic multiplicities; no unproved assertion of simple roots is made.
The asymptotic theorem fixes j before letting n tend to infinity.

The source's adjacent quadratic expression and its forward mod-3 congruence
are credited as existing results. The exact identity after substitution is
checked algebraically. The note's appendix identifies only the specific
arXiv-v1 formula discrepancies relevant to this proof. It does not claim
that the same discrepancies occur in the final journal publication.

## Exact implementation audit

Command executed from the archive root:

    python3 code/verify_exact.py

Result: PASS, 6,722 exact checks.

The run was independently repeated to a temporary output path. Every
recorded field except the elapsed runtime agreed exactly between the two
runs. The optional floating-point script is not imported by the exact
verifier. Exact Sturm calculations use rational arithmetic.

## Optional numerical diagnostics

Command executed:

    python3 code/numerical_checks.py

Result: all matrix enclosure checks passed for n=1,2,5,10,20,50,100.
Twelve high-precision sine-equation solves (j=1,2 and six choices of n up to
500) also passed the separate Chebyshev-recurrence residual check at the
1e-65 threshold. These are NOT interval-certified roots. Numerical results
are not premises in any proof in the paper.

## PDF checks

The final source was compiled with pdfLaTeX twice after the last layout
revision. The resulting PDF has 14 pages. The final compilation reported no
undefined references or overfull/underfull boxes. All 14 pages were rendered
with Poppler (pdftoppm) and visually inspected. No clipped text, overlapping
formulas, missing glyphs, or off-page text blocks were found. A separate
PDF text-block bounds check found no blocks extending outside any page.
The illustration is plotted from computed data, with labels identifying
its non-certifying status.

## Remaining limitations

There has been no external mathematical peer review and no Lean or other
proof-assistant formalization. The literature search did not certify
publication priority or the status of the conjecture in the inaccessible
final journal PDF. Finite checks, numerical residuals, and layout inspection
must not be construed as a substitute for mathematical review of the proofs.
