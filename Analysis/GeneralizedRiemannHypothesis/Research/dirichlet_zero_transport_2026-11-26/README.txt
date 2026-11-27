LOCAL CAUCHY LAWS AND INFINITE TRANSPORT OF DIRICHLET ZEROS
Research packet — November 26, 2026

START HERE

Read paper.pdf for the complete 20-page report, proofs, source comparison,
examples, references, and verification discussion. The LaTeX entry point
is paper.tex. All sections, figures, and bibliography text are included.

MAIN RESULTS

1. Arbitrarily fine local Cauchy law (Theorem 3.1).
   For a fixed phase-real primitive completed Dirichlet function F,
   including the Riemann xi-function on the critical line, put
       Z_T = 2 F'(U_T) / (F(U_T) log T),
   where U_T is uniform on [u T, v T] and u < v are fixed. If
   alpha_T < beta_T and both endpoints tend to a finite c, then
       Prob(alpha_T < Z_T < beta_T)
         ~ (beta_T - alpha_T) / (pi (1 + c^2)).
   There is no lower bound on the positive interval width.

   In particular, if Xi(t) = xi(1/2 + i t), then
       measure{t in [T,2T]: |Xi'(t)/Xi(t)| < exp(-T)}
         ~ 4 T exp(-T) / (pi log T).
   This is Lebesgue measure for a continuous variable, not a statement
   about the resolution of a numerical sampling grid.

2. Infinite Hermitian zero transport (Theorems 2.1, 2.4, and 2.5).
   For P_A = det(diag(F_i) A + diag(F_i')), A Hermitian, and a fixed
   nonzero positive semidefinite increment B, the canonical nonnegative
   transport density sigma is defined by an inertia difference. It has
   an exact convergent Poisson transform, and
       integral_[aT,bT] sigma(t) dt
         ~ (2 tr(B)/pi) (b-a) T/log T.
   Adding a graph edge of conductance h gives clipped total displacement
       integral_[-T,T] sigma(t) dt ~ (8h/pi) T/log T.
   The full Poisson-smoothed expansion is given to every order as finite
   matrix traces. Conductors first enter at second order, and the initial
   coupling first enters at third order. Shared and multiple zeros are
   treated with their exact multiplicities.

3. Electrical law in the squared coordinate (Theorem 4.1).
   For even inputs, remove central zeros and write
       F_i(z) = z^(2m_i) G_i(z^2).
   Form the analogous determinant with G_i and derivatives in its own
   variable. If connected graph Laplacians increase from L_0 to L_1,
   let Delta K be the decrease in the Kirchhoff index and let n be the
   number of vertices. Its transport density eta satisfies
       integral_[-infinity,X] eta(u) du
         ~ Delta K sqrt(X) log(X) / (4 pi n).
   A spanning-tree-normalized exact Stieltjes transform and its positive
   Tauberian argument are proved. This is a different entire-function
   construction from the ordinary-coordinate determinant.

PROOF AND NOVELTY STATUS

The report imports the zero-location theorem for zeta and Dirichlet
L-functions from the pinned upstream development below. Its new results
are proved in ordinary human-readable mathematics. They are not Lean
formalizations, and this packet does not claim a fresh full build of the
upstream Lean project. The included Lean files are a verbatim review
subset, not a standalone buildable checkout and not implementations of
the new theorems.

The contribution was compared with the requested ProveIt sources and
targeted primary literature. Earlier scalar weak Cauchy limits, matrix
Herglotz interlacing, spectral-shift formulas, and Stieltjes Tauberian
theory are explicitly credited. No identical statement was located in
that comparison. This documents the novelty assessment; it does not
certify worldwide historical priority or external peer review.

SOURCE PINS

grh-lean:
  https://github.com/lsernau/grh-lean
  72fead102f663d5c7a407964a13dc0cf9d977207

ProveIt:
  https://github.com/VladimirReshetnikov/ProveIt
  041d8032541746f2ac2e686fbe437f8092771670

Direct predecessor within that tree:
  Analysis/GeneralizedRiemannHypothesis/docs/incoming/
  graph_coupled_zeros_2026-11-26.zip

The report distinguishes the formal Dirichlet scope from broader uses
of the phrase GRH. It also distinguishes the requested Wikipedia status
account from the primary mathematical and verification evidence.

CONTENTS

  paper.pdf, paper.tex          Compiled report and LaTeX driver
  sections/*.tex              Complete source sections and proofs
  references.tex              Bibliography with source links
  code/verify_transport.py    Exact algebra and numerical diagnostics
  code/make_figures.py        Regenerates vector figures and PNG previews
  code/build_pdf.py           Portable local pdfLaTeX build helper
  requirements.txt           Python dependency versions used
  data/verification.json      Recorded symbolic and numerical results
  data/pdf_build.txt          Three-pass PDF compilation log
  data/validation_summary.txt Verification scope and visual QA record
  figures/                   Vector PDF figures and PNG previews
  provenance/                Source pins, comparison, and review notes
  provenance/upstream_source_subset/
                             Selected upstream files and original license
  SHA256SUMS.txt              Checksums of every other delivered file

REPRODUCE

Use Python 3.11 or later for the listed dependency versions; the recorded
run used Python 3.12.14.
From this directory, in a Python environment with the listed dependencies:

  python3 -m pip install -r requirements.txt
  python3 code/verify_transport.py
  python3 code/make_figures.py
  latexmk -pdf -interaction=nonstopmode paper.tex

The first command may need network access. The verification and figure
scripts use local computation and do not download zero tables or sources.
An existing standard TeX Live installation is required to compile LaTeX.
As an alternative to latexmk, run:

  python3 code/build_pdf.py

The helper creates temporary local format/font-map support if an installed
TeX distribution lacks those generated files. It changes no global TeX
configuration. The included PDF is ready to read without any compilation.

VERIFICATION LIMITS

The rational identities, real-root isolation, and finite interlacing and
inertia checks are exact. The mpmath calculations are floating-point
diagnostics, not rigorously rounded interval certificates. They check
the exact transform formulas and displayed constants, not RH/GRH or an
infinite list of zero ordinates. The arbitrary-window and unsmoothed
asymptotic conclusions rest on the supplied proofs.

The comparison and independent re-derivation notes were produced during
this research session. They are not external peer review. The new work
assumes neither simple zeros nor a zero-spacing conjecture. Conductors,
the number of inputs, and matrices are fixed as the height tends to
infinity. The squared-coordinate theorem requires even inputs.

Upstream source copies retain their original license and notices.
The source archive manifest identifies the inspected ProveIt archives;
those full predecessor archives are not duplicated in this packet.
