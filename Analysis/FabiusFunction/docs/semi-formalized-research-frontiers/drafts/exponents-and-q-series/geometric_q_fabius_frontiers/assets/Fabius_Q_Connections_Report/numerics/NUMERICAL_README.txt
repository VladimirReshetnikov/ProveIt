Numerical supplement for the q-Fabius/Rvachev report
=====================================================

Run: python q_fabius_experiments.py

The program is deterministic. Exact rational arithmetic is used for
q-binomial, q-Lagrange, and digital-product checks; mpmath uses 80
decimal digits for analytic product checks. Density figures use direct
FFT inversion on a 2^16-point padded grid.

Python: 3.13.5
NumPy: 2.3.5
Matplotlib: 3.10.8
mpmath: 1.3.0
