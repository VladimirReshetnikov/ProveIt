# Which samples of Li coefficients detect off-line zeros?

Read **li_sampling.pdf** for the complete paper. Its main source is **li_sampling.tex**. The other four TeX files are included by that source.

## Results

The paper gives a necessary and sufficient condition for a family of sample indices to detect every symmetric strip spectrum with an off-line zero by simultaneous negative Li coefficients. The condition is simultaneous recurrence in every finite torus. For polynomial indices it is equivalent to a common root modulo every integer. On prime parameters the common root must be a unit. Failure yields a finite polynomial witness and an entire-function witness whose zeros agree with those of Riemann's xi at every sufficiently large absolute height.

For the classical Li coefficients, let d(n) be their centered second difference. Each of the four possible sign patterns of d(n) and d(n²) recurs with positive lower Banach density, with both magnitudes greater than 0.011. The first negative value is at 118. Whole runs of exactly 235 positive values, immediately bounded by negative values on both sides, recur simultaneously at squares and cubes. The paper also proves prime-parameter analogues.

## Rebuild and verify

Compile in this directory on a standard TeX Live installation. The plot used by the manuscript is included.

    pdflatex -halt-on-error li_sampling.tex
    pdflatex -halt-on-error li_sampling.tex

Use Python 3.9 or later with assertions enabled. These three checks use only the standard library.

    python3 li_verify.py
    python3 constants_verify.py
    python3 moment_constants.py

The next checks use the MPFI and MPFR shared libraries on 64-bit GNU/Linux (LP64). They independently enclose forty zeros from decimal candidates by Euler–Maclaurin summation and Rouché's theorem. The total spectral mass and moment inequalities bound every omitted zero.

    python3 certify_zeta.py
    python3 certify_window.py --csv window_bounds.csv

An independent power-series computation verifies the first negative second difference without any hypothesis about zeros. It requires the python-flint package, tested with version 0.9.0.

    python3 verify_keiper.py

To redraw the figure from the certified CSV, use Matplotlib.

    python3 plot_window.py

The text files ending in _output.txt record successful executions. The constants and moment calculations use rational interval bounds. The 119 rows of window_bounds.csv give outward-rounded bounds for d(0) through d(118) from the forty-pair method. The independent Arb calculation yields much narrower enclosures for the first sign change. The proof of recurrence is given in the paper.

## Source comparison

The paper cites the Lean statements at commit 72fead102f663d5c7a407964a13dc0cf9d977207, the independent upstream verification, and the closest ProveIt results at commit 4d7990202f9f106b2ffe8c209f073ad01d5e1987. The file proveit_inventory.tsv records the 100 compared packet locations and Git object IDs. The source comparison included the historical research directories and the archives in the GRH folder's own docs/incoming directory.

The upstream Lean development supplies RH for zeta and GRH for Dirichlet L-functions. The downstream results have mathematical proofs and reproducible computational certificates. A new Lean formalization and an independent rebuild of the upstream proof were outside this work. The literature comparison is documented in the paper. Publication priority is unverified.

SHA256SUMS records the contents of each other file in this archive.
