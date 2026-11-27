# Peak rigidity and simultaneous recurrence of smoothed prime-counting errors

Research note dated 2026-11-26. The main theorem is a Dirichlet-GRH implication, with an exact one-sided converse for the identity class. The public Lean repository reports the relevant endpoint; this package is not a new Lean proof or independent audit of that repository.

## Files

- `prime_peak_rigidity.tex`, `prime_peak_rigidity.pdf`: complete mathematical argument and references.
- `SOURCES.md`: consulted source paths, file hashes, and priority limitations.
- `check.py`: exact rational phase-inequality checks and numerical illustration for moduli 1, 3, 5, 7, 11.
- `profiles.csv`: peak vectors and centering constants (modulus 1 uses residue 0 for its unique class).
- `prime_samples.csv`: prime-power error samples at x=100, 1000, 10000, 100000, 1000000. The deficit of the arithmetic error can be negative at finite x; the exact nonnegative deficit is defined on the spectral approximation, not the uncorrected finite-x error.
- `checks.txt`: output of the executed checks.

## Reproduction

Run `python -m pip install -r requirements.txt` if needed, then `python check.py`. For LaTeX, run `pdflatex -interaction=nonstopmode -halt-on-error prime_peak_rigidity.tex` twice. The sample CSV uses high-precision mpmath for constants and numpy floating point for the sieve sums; these are illustrative numbers, not rigorous interval enclosures. The rational tests verify 16 finite translate instances; the proof in the PDF covers the full infinite result.

No Lean executable was available. No code is asserted to have kernel-checked the new statements. The possible formalization path is described in the paper.
