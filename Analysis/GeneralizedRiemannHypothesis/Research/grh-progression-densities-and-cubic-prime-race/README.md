# Geometric progressions and one-sided prime sums

Start with **progressions.pdf**. It proves three results for all finite fields addressing Questions 6.1, 6.2 and the existence clause in 6.4 of Asada, Fourakis, Manski, McNew, Miller and Moreland. The polynomial-ratio upper-density Conjecture 6.3 remains open. The proofs use the exponent method and have no RH or GRH dependency.

**analytic.pdf** examines the analytic mechanism more directly. It gives an eventual-sign criterion on sparse grids for the nonabelian conductor-23 Artin factor, an unconditional negative liminf bound, and the sharp growth requirement for a window schedule valid for all polar pairs. An eventual sign of the cubic statistic is still an open arithmetic input.

The two PDFs were compiled from the included LaTeX. SOURCE.md records the Lean revision and declarations. PRIOR.md and PRIOR.tsv identify the comparison with earlier reports. The mathematical results presented here are paper proofs. The public Lean build results in these papers are attributed to the repository's authors.

## Reproduce

From this directory, with Python 3.10 or newer and no additional Python packages, run

    python3 code/check_density.py
    python3 code/triangle_check.py
    python3 code/check_eta23.py

Expected outputs are in checks/. The first two checks use exact arithmetic. The last check is exact for the integer prime coefficients and uses floating point for the displayed log-weighted sums. To rebuild with a standard TeX Live installation, run

    latexmk -pdf progressions.tex
    latexmk -pdf analytic.tex

A list of archive member digests is in SHA256SUMS.
