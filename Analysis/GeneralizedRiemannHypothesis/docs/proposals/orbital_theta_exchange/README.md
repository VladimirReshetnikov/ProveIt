# Canonical orbital sections for the theta exchange argument

A distinct proof-simplification proposal for the readable Alpöge–Claude RH/Dirichlet GRH proof.

- `orbital_theta_exchange.pdf`: mathematical report (9 pages).
- `orbital_theta_exchange.tex`: complete TeX source.
- `FORMALIZATION.md`: Lean integration specification and acceptance gates.
- `check_orbital.py`, `checks.txt`: exact finite-model regression tests and their output.
- `source-audit.tsv`, `proposal-audit.tsv`: pinned source and nonduplication audit (Git blob IDs).
- `verify_sources.py`: optional local checkout audit tool.

Rebuild: `latexmk -pdf -halt-on-error orbital_theta_exchange.tex`.
Run tests: `python3 check_orbital.py`.
Audit a local clone (after checking out pinned commit): `python3 verify_sources.py /path/to/ProveIt`.

The report proves the local replacement mathematically. It does not claim a compiled Lean port, a net line-count reduction, or a new proof independent of the original determinant and zero-exclusion arguments. All 8 proposal folders at the inspected snapshot were reviewed. The compact edition was outside the requested source scope. Independent verification of the original proof is reported at https://math.mit.edu/~drew/shortgrh/; the present proposal has not undergone that verification.
