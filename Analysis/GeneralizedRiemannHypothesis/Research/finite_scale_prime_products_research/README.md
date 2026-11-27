# Finite-scale prime-product inequalities

A mathematical research note inspired by the one-sided prime-error criterion in the Alpöge–Claude Dirichlet GRH formalization.

- `report.tex`, `report.pdf`: complete mathematical exposition, proofs, and bibliography.
- `SOURCE_AUDIT.md`: inspected source snapshot, proof dependencies, and unverified formalization roadmap.
- `experiments.py`: reproducible exact algebra checks and illustrative sieve and residue calculations.
- `prime_products.csv`, `experiment_log.txt`: results of executing the script.

Rebuild the PDF with `pdflatex -interaction=nonstopmode -halt-on-error report.tex` twice (requires standard AMS/Latin Modern LaTeX packages). Run `python3 experiments.py --output .` to reproduce the data; optional `mpmath` gives illustrative zeta-zero amplitudes. Default sieve bound is 7,290,000. The finite checks do not prove asymptotic statements; the proofs are in the report.

Scope: fixed modulus, Dirichlet GRH. The proposed novelty is the combined finite-scale filter, sharp one-sided exponent, and Hermitian residue bound. Historical priority is not certified. The external Lean GRH project was inspected but not rebuilt locally; the new results are not Lean-verified.
