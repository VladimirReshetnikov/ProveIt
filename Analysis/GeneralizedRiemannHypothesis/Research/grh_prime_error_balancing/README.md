# Simultaneous balancing of prime errors after Dirichlet GRH

Read `report.pdf` (9-page mathematical research note) or compile the editable `report.tex` twice with `pdflatex`.

## Main results

- An unconditional spectral-rank lemma: the noncentral zero multiplicity vectors of distinct primitive Dirichlet L-functions have full rank over the complex numbers.
- Under Dirichlet GRH, the convex hull of the normalized ramp-prime-error vector in every sufficiently large bounded logarithmic window contains a uniform ball around its central-zero bias. At most phi(q)+1 scales suffice for exact simultaneous balancing.
- An explicit common positive convolution measure that kills all low nonzero critical ordinates and attenuates the higher frequencies by at least pi^(-N). Its log-support radius is O_q(log^2 T) for cutoff T. Includes the specific non-split-prime ramp used in the GRH proof.

The derivations are self-contained given standard classical analytic-number-theoretic facts and the Dirichlet GRH theorem. Historical novelty has not been exhaustively verified. No claim of a new Lean-checked proof or an independent rebuild of GRH is made.

## Files and reproduction

- `report.tex` / `report.pdf`: theorem statements, proofs, comparison, references.
- `experiment.py`: numerical illustration. Run `python -m pip install numpy scipy mpmath`, then `python experiment.py`. The script writes `q4_samples.csv` and `experiment_results.json` beside itself. Uses Python 3.11+.
- `experiment_results.json`: includes negative results at smaller centers as well as a positive triangle at X=1,000,000. These data are floating-point illustrations, not interval certificates or evidence of the theorem for all centers.
- `q4_samples.csv`: sampled two-coordinate ramp errors in four windows.
- `formalization_plan.md`: Lean dependency and theorem plan, not an executable or machine-checked proof.
- `source_audit.md`: inspected upstream files and exact revision.
- `SHA256SUMS`: integrity hashes for deliverable files.

No changes were made to any GitHub repository.
