# Sharp positive zero-cancelling filters

Research note dated 2026-11-27. The report extends the reflected-harmonic filter method in ProveIt's merged GRH article and proves an analytic perturbation theorem. It also contains an exact integer interval certificate for the optimal three-frequency width in a rational box around the first three zeta ordinates.

## Contents
- `paper.tex`, `paper.pdf`: self-contained mathematical proof, references, and limitations.
- `certify_three.py`, `certificate.txt`: executed exact rational/outward integer interval certificate. Python 3 standard library only. Run with assertions enabled (do not use `python -O`). It certifies the optimization for the stated frequency boxes; it does not compute the zeros themselves.
- `reproduce.py`, `computations.txt`: exact polynomial examples and exploratory numerical calculations (requires `mpmath`). These numerical checks are not relied on for optimality.
- `sources.md`: source snapshot and provenance.
- `SHA256SUMS`: content checksums.

## Reproduction
```sh
python certify_three.py
python reproduce.py  # requires mpmath
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
sha256sum -c SHA256SUMS  # before regenerating files
```

All optimization theorems are unconditional. The explicit-formula application takes the supplied Dirichlet GRH declaration as input. Neither the upstream Lean build nor a new Lean formalization was executed. Literature priority has not been established by an exhaustive search.
