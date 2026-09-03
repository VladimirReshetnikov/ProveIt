> **Absorbed into the consolidated volume.**
> This directory is the preserved verification package of a report that is now
> **Part III** of `geometric_q_fabius_frontiers.tex`, two levels up. The
> report's own `.tex` and `.pdf` were deleted when it was merged; git history
> is the archive, and the volume's Provenance section pins the absorbed
> snapshot by SHA-256. The scripts, data, and figures here are still live —
> the volume includes them from `assets/finite_sinc_products_report/`. Any build or path
> instruction below describes the original standalone package and no longer
> resolves as written.

FINITE DYADIC SINC PRODUCTS AND RVACHEV UP APPROXIMANTS
=======================================================

Retained companion files
------------------------
finite_sinc_experiments.py        Reproducible numerical and exact-arithmetic code.

Generated figures
-----------------
finite_sinc_approximants.pdf
finite_sinc_approximants.png
scaled_error_profiles.pdf
scaled_error_profiles.png
convergence_comparison.pdf
convergence_comparison.png

Generated data
--------------
sharp_error_verification.csv
positive_acceleration_verification.csv
exact_coefficients.txt
exact_rational_samples.csv

Reproduction
------------
Python 3 with NumPy and Matplotlib is required. From this directory, run:

    python finite_sinc_experiments.py --output-dir . --fft-power 17

The script regenerates the vector-PDF figures and every data table. It also
contains an exact rational truncated-power evaluator, reciprocal-product
coefficient generation, and geometric Richardson weights.  The consolidated
volume uses deterministic 300-dpi raster companions to avoid importing Type 3
fonts from Matplotlib's PDFs.  Regenerate them after running the script with:

    for stem in finite_sinc_approximants scaled_error_profiles convergence_comparison; do
      pdftoppm -png -r 300 -singlefile "$stem.pdf" "$stem"
    done

The standalone report source and PDF were absorbed into the consolidated volume.
From the volume directory, rebuild that canonical PDF with exactly three passes:

    pdflatex -interaction=nonstopmode -halt-on-error Exponents_and_q_Series_Frontiers.tex
    pdflatex -interaction=nonstopmode -halt-on-error Exponents_and_q_Series_Frontiers.tex
    pdflatex -interaction=nonstopmode -halt-on-error Exponents_and_q_Series_Frontiers.tex

Research status
---------------
The report distinguishes results already present in the ProveIt documentation
from new theorems and conjectures developed here. The new material is proved in
the report but has not been independently peer reviewed or formalized in Lean.

> **Editorial note (2026-08-28):** the standalone report source and compiled PDF
> were removed from this directory after their content was merged into
> `../../Exponents_and_q_Series_Frontiers.tex`; their SHA-256 hashes remain in the
> volume provenance list, and git history archives the files. This directory
> keeps only figures, data, scripts, and this asset README.
