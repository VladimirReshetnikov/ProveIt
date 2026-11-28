PROVEIT: SHARP ZERO INEQUALITIES AND HIGH-DERIVATIVE POSITIVITY
Research package — 27 November 2026

START HERE

1. sharp_reciprocal_zero_inequalities.pdf (11 pages)
   The main paper proves sharp inverse-power bounds for the positive imaginary
   parts of complex zeros of the Laplace transform of a compactly supported
   probability measure. It includes equality cases, a transport stability
   theorem for Fourier zeros, the optimal constant in Steinerberger's square-sum
   support inequality, and square-frequency zero-free interval bounds answering
   the asymptotic-order alternative in Kozma–Oravecz Question 2.

2. central_derivatives_note.pdf (8 pages)
   The companion proves explicit eventual increase and growing-dimension Hankel
   positivity for even central derivatives of primitive quadratic Dirichlet
   L-functions. At fixed conductor, it permits degree r of order m log m.
   It includes an explicit finite sufficient inequality and a proof explaining
   why all matrix sizes cannot be covered at one fixed m for a sign-changing
   theta kernel.

Both papers include complete LaTeX sources and bibliography entries. Every theorem
proved in these papers is unconditional. The repository's RH/GRH assertions are
not used as assumptions. The main source revision is:

    41a284d6ef8eb16d783bfc685ab99cc6e1d28daa

CLAIMS AND PRIORITY

The main paper supplies a rigorous affirmative answer to the particular support
inequality asked in Steinerberger's problem, including its sharp constant. It
does not determine the exact minimum support for every frequency set. The
square-spectrum result determines the uniform order and the short-band leading
term, but not the exact long-band constant.

The integrated strip identity and mean-frequency bound are credited to the
repository and to their integrated-Obrechkoff antecedents. The elementary
majorization step is not claimed to be a new general majorization principle.

Wagner's 2019 central-derivative asymptotics are credited in the companion. The
qualitative eventual-increase conclusion and the existence of an asymptotic are
not presented as newly discovered facts. The proposed quantitative contributions
are the explicit thresholds and growing-matrix bounds. The full Sheth–Voo
one-turning-point assertion is not proved.

The targeted literature review found no matching earlier sharp-support theorem
or square-order answer. This is a record of a bounded search, not a certification
of publication priority. The internal mathematical reviews are not external
peer review or Lean kernel checking. No internationally prominent conjecture is
claimed to have been settled by this package.

CONTENTS

  *.tex, *.pdf                 Complete papers and their typeset versions.
  figures/                     Vector PDF and raster PNG of the proved bounds.
  verification/                Reproducible scripts, JSON outputs, exact CSV data.
  audit/independent_proof_review.txt
                               Detailed internal mathematical audit.
  SOURCE_AUDIT.txt              Repository analysis, source attribution and scope.
  source_manifest.json          URLs and hashes of inspected local source copies.
  build.py                     Rebuild papers; optionally rerun checks and render.
  requirements.txt             Python versions used for verification/figures.
  SHA256SUMS                   SHA-256 hashes of every other file in the archive.

REPRODUCING

To compile the two papers from this directory:

    python build.py

This requires pdflatex and standard TeX packages, including amsmath, amsthm,
mathtools, geometry, hyperref, xurl, microtype, lmodern, and graphicx. The supplied
figure is already present, so Python scientific packages are not needed merely
to rebuild the PDFs. The build runs LaTeX twice and checks for unresolved
references and overfull boxes.

To rerun the exact checks, numerical illustrations and figure generation first:

    python -m pip install -r requirements.txt
    python build.py --verify

To also generate page PNGs for visual inspection (requires pdftoppm):

    python build.py --render

The scripts may also be run directly:

    python verification/verify_reciprocal_bounds.py
    python verification/verify_central_derivatives.py

The first performs 21,200 exact rational checks of the square-prefix optimizer,
symbolic identity checks, sharp-constant calculations, and an exact Bernstein
positivity certificate for one illustrative polynomial. Its curves are analytic
bounds, not computations of the unknown extremal interval.

The second records nine high-precision derivative illustrations and three
numerical checks of the finite Hankel criterion. These calculations use ordinary
high-precision arithmetic, not interval certificates. The proofs do not depend
on them.

The supplied hashes describe the archived versions. Rebuilding a PDF can change
its metadata and hence its hash. No network access is needed by either proof
verification script or by the LaTeX build once dependencies are installed.

NORMALIZATION

Real-line Fourier transform: integral exp(i lambda t) d mu(t).
Circle: R/Z, with Fourier coefficients integral f(t) exp(-2 pi i a t) dt.
The optimal support-radius constant is 1/(sqrt(2) pi) for this unit circle.
For the angular circle R/(2 pi Z), multiply radii by 2 pi; the constant is sqrt(2).
For square spectra, H=K+1 is the number of positive frequencies.

