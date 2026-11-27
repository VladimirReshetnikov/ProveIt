# Recovering prime powers and the modulus from three large prime sums

Read **prime_power_echoes.pdf** for the statements, proofs, prior work, and references. Theorem 1 extracts prime powers and their progression weights from a three-cutoff limiting profile. Theorem 3 classifies the induced metric spaces up to isometry. Theorem 4 recovers the rightmost zero abscissa from two lags.

## Reproduce the paper and examples

From this directory, with a standard TeX Live installation, run

    pdflatex -interaction=nonstopmode -halt-on-error prime_power_echoes.tex
    pdflatex -interaction=nonstopmode -halt-on-error prime_power_echoes.tex

The vector illustration lag_profile.pdf is bundled. To regenerate it, use Python 3 with NumPy and Matplotlib.

    python3 plot_profile.py lag_profile.pdf

For the numerical checks, use Python 3.11 or higher. The checker uses only the standard library.

    python3 check.py

Its recorded output is checks.txt. It checks the scalar prime ramp at prime, prime-power and composite lags, primitive-character splitting modulo 12, and the direction of the complex-character phases modulo 5. The calculations test finite consequences of the paper. The rigidity theorem and infinite limiting statements are proved in the text.

## Formal input

The paper uses the Dirichlet critical-line theorem from lsernau/grh-lean, revision 72fead102f663d5c7a407964a13dc0cf9d977207. Its source paths and independent verification records are linked in the paper. The new results are human-readable proofs. This archive contains neither a rebuild of that repository nor a Lean formalization of the new theorems.
