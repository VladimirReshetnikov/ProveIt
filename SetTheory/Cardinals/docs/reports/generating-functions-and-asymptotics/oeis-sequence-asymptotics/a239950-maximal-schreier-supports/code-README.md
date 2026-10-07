# Authored exact and optional symbolic programs

- `partition_exact.py`: positive integer dynamic program, plus an independent recursive generator of ordinary partitions. The DP is documented in the report and reproducibility guide.
- `check_exact.py`: regenerates all 1501 counts, checks the observed 58-term prefix and all ordinary partitions through 35, checks finite Euler exponents, and verifies rational first-correction and interior-zero certificates.
- `independent_wick_check.py`: optional SymPy two- and three-dimensional Wick calculation, verifying both closed correction identities by explicit exceptions. It computes the first correction. It is run only with `--symbolic`.

- `second_wick_check.py`: optional direct derivative/Wick evaluation of the second correction. It verifies the displayed B2 polynomial and the full d2/c2 identities, using D=X+a*Z only as a covariance-diagonalizing speed coordinate. It is run only with `--symbolic`.

The two symbolic programs compute fixed first/second corrections; neither is an unrestricted all-orders coefficient engine.

All mandatory Python arithmetic is integer or `fractions.Fraction`; no floating-point approximation decides a mandatory test. Every failure check remains active under `python -O`. Do not infer an asymptotic theorem from finite checks; the analytic proof is in Report195.tex.
