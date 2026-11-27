SHARP POWER LAWS FOR ALMOST POSITIVE HERMITE MATRICES
Research package prepared for Vladimir Reshetnikov
26 November 2026

START HERE
report.pdf is the complete paper. report.tex is its editable LaTeX source.

MAIN RESULT
For n >= 2 conjugation-invariant roots in the unit disk, form
H[i,j] = sum_l z_l^(i+j), 0 <= i,j < n.
Let b = max_l |Im z_l| and D = max(0,-lambda_min(H)). Then

  2 [b/(4 floor(n/2))]^(2n-2) <= D
  <= n^2(n-1)(7n-11) b^2 / 6.

Both exponents are optimal for these positivity-defect estimates. No root
separation or simplicity assumption is needed. The report proves a certified
moment-error version and applies it to finite contour windows of zeros of xi
and primitive completed Dirichlet L-functions. These finite implications do
not assume RH or GRH.

RESEARCH STATUS
The paper contains a complete mathematical proof. The exact bound and sharp
exponent statement were not found in the targeted literature review, so they
are presented as a proposed original contribution, with priority unconfirmed.
The classical Hermite--Sylvester criterion, interpolation witness, and contour
moment representation are explicitly attributed. This package does not claim
to settle another named open conjecture.

The new theorem has not been formalized or compiled in Lean. The included
roadmap is an implementation plan. Source inspection of the GRH repository
is distinguished from its externally reported full builds and kernel checks.
No new complete GRH build was performed for this report.

CONTENTS
report.tex, report.pdf       Complete proof, source analysis, and references.
code/verify_certificates.py  Exact rational algebra and finite certificate checks.
code/make_figure.py          Reproduces the two-panel scientific figure.
data/exact_certificates.json Exact identities, witnesses, and PSD certificates.
data/scaling_eigenvalues.csv 80-decimal-digit illustrative cubic eigenvalues.
figures/                    Plot in PDF and PNG formats.
lean/formalization_plan.txt Formal target and proof decomposition; not a proof file.
verification_notes.txt      Mathematical checks and limitations.
sources/repository_audit.txt Scope and proof-chain analysis at a pinned commit.
sources/source_manifest.json SHA-256 inventory of the inspected source snapshot.
sources/grh_snapshot/       Selected upstream source files, license and notices.
sources/novelty_review.txt  Literature comparison and access limitations.
SHA256SUMS.txt              Checksums for every other file in the package.

REPRODUCING THE COMPUTATIONS
Python 3 with sympy and mpmath is needed for the exact-check script.
Matplotlib and NumPy are needed for the figure.

  python3 code/verify_certificates.py
  python3 code/make_figure.py

No network access is required. Exact identities and PSD tests use rational
arithmetic. The CSV eigenvalues are illustrations, not interval certificates
of actual zeta zeros. The mathematical proofs do not depend on them.

REBUILDING THE PAPER
Use a complete LaTeX installation with the packages listed in report.tex:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

Tectonic can also compile the source if its TeX bundle is available. The figure
PDF is supplied, so rebuilding the paper does not require rerunning Python.

SOURCE PROVENANCE
Repository: https://github.com/lsernau/grh-lean
Pinned commit: 72fead102f663d5c7a407964a13dc0cf9d977207
Lean: 4.35.0
Mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679
The snapshot is deliberately partial and is not a standalone Lean project.
Upstream source files remain under Apache-2.0; their LICENSE, NOTICE and
ATTRIBUTION.md are retained. The report is newly written analysis and proof.

INTERPRETING SHARPNESS
The optimal exponent concerns bounds using the scalar PSD defect or a noisy
PSD certificate. It is not a universal information-theoretic limit for all
algorithms that exploit every moment and polynomial-coefficient identity.
