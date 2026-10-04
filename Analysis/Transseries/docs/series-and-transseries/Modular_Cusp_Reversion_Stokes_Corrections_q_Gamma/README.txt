COMPLEX TRANSSERIES REVERSION AT MODULAR CUSPS
Stokes corrections, flat critical values, arbitrary ramification,
and q-gamma special values

Research article, 4 October 2026; 36 PDF pages.
Repository comparison pinned to ProveIt commit:
6cb1d86f19ebf9f54c8d985b141b84233b6eab66
https://github.com/VladimirReshetnikov/ProveIt

CONTENTS

complex_transseries_q_cusps.pdf
    Complete article with proofs, worked examples, a convergence figure,
    explicit error bounds, eleven research questions, and references.

complex_transseries_q_cusps.tex
    Main LaTeX file. Keep it beside the sections/ and figures/ directories.
    All source text is included in this archive.

sections/01_scope.tex through sections/09_references.tex
    Article source sections and the integrated bibliography.

figures/eta_inverse_convergence.pdf
    Vector figure used by the article.

verification/verify_eta_reversion.py
    Exact Fraction-arithmetic coefficients, two independent Euler-product
    generators, composition checks, arbitrary ramification constructions,
    and 360-digit real and complex examples. Also recreates the figure.

verification/verify_cusp_phases.py
    80-digit checks of 24 one-factor and 24 general-product cusp identities;
    exact rational Dedekind reciprocity and inverse-disk certificate;
    exact initial raw q-gamma inverse coefficients and numerical examples.

verification/verify_stokes.py
    Independent 80-digit ray quadratures for four paired Borel summands,
    compared with the stated Stokes residue correction.

The data/ directory contains the recorded JSON outputs and inverse_errors.csv.
SOURCES.txt describes provenance and the scope of the mathematical claims.
MANIFEST.sha256 provides checksums of every other file in the archive.

BUILD THE ARTICLE

From this directory, run:
    latexmk -pdf -interaction=nonstopmode -halt-on-error complex_transseries_q_cusps.tex

Alternatively, run pdflatex on the main .tex file three times. The bibliography
is part of the source; neither BibTeX nor network access is needed to build.
A standard recent TeX Live installation is sufficient. The source uses
amsmath, amssymb, amsthm, mathtools, lmodern, microtype, geometry, booktabs,
longtable, array, tabularx, graphicx, xcolor, enumitem, fancyhdr, hyperref,
and cleveref. No external programs are needed during LaTeX compilation.

REPRODUCE THE COMPUTATIONS

Use Python 3.9 or later. Install dependencies into your preferred environment:
    python3 -m pip install mpmath numpy matplotlib

Then run:
    python3 verification/verify_eta_reversion.py
    python3 verification/verify_cusp_phases.py
    python3 verification/verify_stokes.py --dps 80

The main and cusp scripts write fresh outputs beside themselves in verification/.
The Stokes script also defaults to an output beside itself; --output PATH can
select a different destination. The archived reference outputs remain in data/.
Numerical regeneration can take several minutes. The scripts do not require
network access. Exact coefficient calculations use Python Fraction arithmetic;
mpmath precision is 360 decimal digits in the main script and 80 in the two
supplements. The precision can be changed in the script or, for Stokes, by CLI.

CONVENTIONS IMPORTANT WHEN READING THE DATA

Coefficient arrays are indexed from degree zero, including initial zeros.
Rational numbers are serialized as strings to preserve their exact values.
In exact_coefficients.json, the field
log_denominator_correction_coefficients_indexed_from_zero
uses -log(Psi(u)/u), whereas the article defines ell(u)=+log(Psi(u)/u).
The opposite sign reflects the denominator convention, not different inverses.
Complex values are recorded without resetting the analytic logarithm lift.
The winding index in the complex eta example is essential to recovering the
original parameter rather than a different inverse sheet.

SCIENTIFIC STATUS

The article gives analytical proofs and clearly stated local/sectorial domains.
The exact finite coefficient tests and rational disk certificate are distinct
from the floating-point numerical checks; the latter are not interval proofs.
The article is not a Lean or other proof-assistant formalization, and no theorem
is claimed to have been accepted by the ProveIt repository or peer reviewed.
Classical inversion, modularity, and resurgence results are explicitly credited.
The conjecture correction targets one named clause at the pinned snapshot.
The remaining parameter-uniform resurgent inverse problem is listed as open.
