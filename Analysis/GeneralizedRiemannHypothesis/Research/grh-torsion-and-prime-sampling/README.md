# Torsion specialization and sparse prime sums

Start with **torsion.pdf**. It answers the earlier ProveIt question about uniform polynomial bounds for the sum of the positive losses. It gives the exact finite threshold, its extremizers, the small-tolerance transition and an exact formula over a fixed cyclotomic coefficient field.

**prime-sampling.pdf** contains two analytic applications. The first gives a one-sided Dedekind zeta criterion on any prescribed power grid. The second recovers individual zero multiplicities from smoothed prime sums and gives an explicit simplicity defect. Global simplicity of the Riemann zeros and the critical-line assertion for the example cubic field remain open in this work.

## Rebuild

Run from this directory with a standard pdfLaTeX installation, including the packages in paper-style.tex.

```sh
pdflatex -halt-on-error torsion.tex
pdflatex -halt-on-error torsion.tex
pdflatex -halt-on-error prime-sampling.tex
pdflatex -halt-on-error prime-sampling.tex
```

## Independent computations

The torsion checks use Python 3 and the standard library. They enumerate all small mark configurations, check orbit descent directly using Galois orbits, test strict thresholds, and check critical-budget crossings. The proofs for arbitrary polynomials are in the first paper.

```sh
python3 verify_minimax.py
python3 verify_minimax.py --table 2 1 6 1/4
python3 check_descent.py
python3 check_transition.py
python3 prime_statistics.py
```

The exact calculator uses binary search and integers for rational tolerances. Its output column cumulative_cost is the minimum budget that can block every shell from the starting index through that row. For budget B, the first cumulative_cost strictly larger than B gives the least universally sufficient exponent. prime_statistics.py computes the cubic-field statistic as rational coefficients of prime logarithms and checks the rounding of the analytic tail bound. verification.txt records all runs. sources.md and prior_reports.tsv document the pinned inputs and closest precedents. SHA256SUMS covers every other file in the archive.
