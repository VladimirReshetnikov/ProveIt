DYADIC RADON PROFILES IN THE FABIUS--RVACHEV WEB
=================================================

Package date: 2026-08-30
Prepared for: Vladimir Reshetnikov

MAIN DELIVERABLES
-----------------

dyadic_radon_profiles_fabius_rvachev.tex
    Complete LaTeX manuscript.

dyadic_radon_profiles_fabius_rvachev.pdf
    Compiled 31-page PDF, rendered and visually inspected page by page.

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
    Vector figures used by the manuscript.

figures/*.png
    Raster inspection copies.

numerical_results.txt
    Compact human-readable computation summary.

REPRODUCING THE EXPERIMENTS
---------------------------

From the package root:

    python numerical_experiments.py --output-dir .

The script is deterministic and overwrites the generated data/figure files.

BUILDING THE PDF
----------------

A TeX Live installation with latexmk is recommended:

    latexmk -pdf -interaction=nonstopmode -halt-on-error \
        dyadic_radon_profiles_fabius_rvachev.tex

The manuscript expects the relative directories data/ and figures/ to remain
next to the TeX source.

PDF VISUAL VERIFICATION
-----------------------

The final PDF was rendered with the supplied PDF workflow at 150 dpi:

    python /home/oai/skills/pdfs/scripts/render_pdf.py \
        dyadic_radon_profiles_fabius_rvachev.pdf \
        --out_dir _renders --dpi 150

All 31 pages were inspected through contact sheets, with full-resolution checks
of dense tables and figures.  No clipped text, overlaps, broken glyphs, or
missing figures were observed.

DEPENDENCIES
------------

Python versions used for the packaged run are listed in requirements.txt.
The script supports recent compatible versions of NumPy, Matplotlib, mpmath,
and SymPy.

INTEGRITY
---------

SHA256SUMS.txt contains SHA-256 hashes for every deliverable file in the ZIP,
except the checksum file itself and transient build/render files.

NOVELTY STATUS
--------------

The report uses [I] for imported/classical material, [N] for theorems proved in
the report, [E] for numerical evidence, and [C] for conjectures or open
problems.  “New” means apparently new relative to the audited repository
corpus, not a claim of worldwide priority.
