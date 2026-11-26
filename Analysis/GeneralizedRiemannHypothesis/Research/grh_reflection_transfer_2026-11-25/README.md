# Reflection detectors for nonabelian Riemann hypotheses

Research note, 25 November 2026. Main result: for an S_n-Galois extension
L/Q and E fixed by a transposition, under Dirichlet GRH the order of any
right-of-line critical-strip zero of ζ_L is at most 2(n-H_n) times its
order in ζ_E. This extends to real reflection groups using a small set of
reflection classes. A single centered one-sided smoothed prime estimate
for the selected fields would therefore imply Dedekind RH for L.

- `report.tex`, `report.pdf`: mathematical proof and transfer analysis.
- `verify.py`, `verification.txt`, `quintic_prime_sample.csv`: exact finite checks.
- `source-audit.txt`: upstream blobs and earlier archive inventory.
- `lean-interface.md`: implementation dependency plan; not a Lean proof.

Reproduce: `python verify.py` (Python 3, SymPy 1.14); then
`pdflatex -interaction=nonstopmode -halt-on-error report.tex` twice.

The new geometric estimate is unproved. This is a reduction beyond Dirichlet
GRH, not a proof of full Dedekind GRH. Prior archives were surveyed by names
and ZIP member inventories, not fully read; historical novelty is unverified.
