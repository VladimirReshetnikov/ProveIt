DYADIC RADON PROFILES IN THE FABIUS--RVACHEV WEB
=================================================

Package date: 2026-08-30
Prepared for: Vladimir Reshetnikov

MAIN DELIVERABLES
-----------------

dyadic_radon_profiles_fabius_rvachev.tex
    Complete 2,050-line, 74,839-byte LaTeX manuscript; SHA-256
    0ac7695620cb22896bb912598e2e91fd404e70dbd3c5d1e769ee76a6e92578d4.

dyadic_radon_profiles_fabius_rvachev.pdf
    Synchronized 29-page, 998,017-byte A4 PDF; SHA-256
    39e76001f71c6628308ccdb8232251538674faee3c9102fa26e4cec00eb276c0.

numerical_experiments.py
    Fully commented experiment driver.  Exact integer/rational arithmetic is
    used for profile inversion, Pascal factorization, digital signs, Prouhet
    sums, finite differences, and Hankel determinants.  mpmath is used for the
    zero-zeta and high-frequency logarithmic-product experiments.

CORPUS_AUDIT.md
    Claim-oriented source audit and nonduplication boundary.

corpus_inventory_2026-08-27.txt
    Preserved recursive TeX path ledger for the historical source snapshot.

DATA AND FIGURES
----------------

data/profile_inversion.csv
    c_h, cumulative exponents a_h, zero multiplicities m_h, and recovered
    second differences.

data/pascal_factorization.csv
    Exact verification of the Pascal shell multiplicities through rank 6.

data/pascal_norms.csv
    Numerical checks of the exact scale-norm identity.

data/sign_prefixes.csv
    Prefixes of four generalized spectral sign sequences.

data/prouhet_checks.csv
    Exact finite-block Prouhet cancellation tests.

data/complete_monotonicity.csv
    Exact signed finite differences of the cumulant-ratio sequence.

data/hankel_determinants.csv
    Exact leading Hankel determinants.

data/zero_zeta_convergence.csv
    Direct partial sums versus the closed zero-zeta formula.

data/fourier_envelope.csv
    High-precision sharp-ray Fourier-envelope data.

data/fourier_envelope_table.tex
    Generated table included by the manuscript.

figures/*.pdf
    Retained vector source figures.

figures/*.png
    Raster figures used by the manuscript to avoid Type 3 plot fonts.

numerical_results.txt
    Compact human-readable computation summary.

REPRODUCING THE EXPERIMENTS
---------------------------

From the package root:

    python numerical_experiments.py --output-dir .

The script is deterministic and overwrites the generated data/figure files.

BUILDING THE PDF
----------------

A TeX Live installation with Libertinus is required. Run exactly three serial
passes:

    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error dyadic_radon_profiles_fabius_rvachev.tex
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error dyadic_radon_profiles_fabius_rvachev.tex
    pdflatex -interaction=nonstopmode -halt-on-error -file-line-error dyadic_radon_profiles_fabius_rvachev.tex

The manuscript expects the relative directories data/ and figures/ to remain
next to the TeX source.

PDF ARTIFACT VERIFICATION
-------------------------

The synchronized 2026-09-04 rebuild began with absent auxiliaries. Its three
successful serial halt-on-error passes produced 27 pages/984,841 bytes, 29
pages/998,017 bytes, and 29 pages/998,017 bytes. Every page is A4 at rotation
zero, rendered, and contains extractable text. All 24 font rows are embedded
and subset, six are Libertinus, and none is Type 3. The final log has no TeX
error, unresolved reference/citation, rerun request, overfull box, or underfull
box; title, author, subject, and keywords metadata are present. Representative
title, body, table, figure, and final pages passed visual inspection. Generated
sidecars were removed, and no checksum ledger is a live publication gate.

DEPENDENCIES
------------

Python versions used for the packaged run are listed in requirements.txt.
The script supports recent compatible versions of NumPy, Matplotlib, mpmath,
and SymPy.

INTEGRITY
---------

The former checksum ledger covered every deliverable file in the ZIP except
itself and transient build/render files. It is now retired and recoverable
from Git history.

NOVELTY STATUS
--------------

The report uses [I] for imported/classical material, [N] for theorems proved in
the report, [E] for numerical evidence, and [C] for conjectures or open
problems.  “New” means apparently new relative to the audited repository
corpus, not a claim of worldwide priority.
