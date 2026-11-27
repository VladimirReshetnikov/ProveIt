# One-sided multiscale prime fluctuations

- `report.pdf`: compiled research note, with proofs of the exact abscissa theorem, critical uniform mean, sharp convergence threshold, and arithmetic series.
- `report.tex`: complete LaTeX source; compile twice with `pdflatex report.tex`.
- `SOURCE_AUDIT.md`: GitHub source provenance and related literature, including the close Dumas precedent.
- `verify.py`: standard-library Python exact rational identity tests and finite numerical illustration.
- `verification.txt`: recorded test run.
- `sample_fluctuations.csv`: finite log-grid samples for four moduli and two scale tuples. These are illustrative, not proof of an asymptotic law or of RH/GRH.

Run `python3 verify.py` to regenerate samples. The analytic proof has not been formalized in Lean. Its main exact-abscissa theorem is unconditional; critical square-root asymptotics use Dirichlet GRH as stated in the report. A complete independent audit of the upstream GRH proof was outside this task. The claimed novelty is the particular extension, not the already studied dyadic lcm ratio or Landau principle.
