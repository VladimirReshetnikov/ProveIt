# Three-scale extremal reconstruction of Dirichlet L-function zeros

Research note, 26 November 2026.

## Contents

- `three_scale.tex`: complete LaTeX research manuscript, including the proofs and references.
- `three_scale.pdf`: compiled eight-page manuscript.
- `verify_filters.py`: standard-library-only Python demonstration. It expands the finite dilation filters as exact integer combinations of shifts, checks cancellation over rational numbers, checks critical-line multipliers and the alias example numerically, and evaluates a small sample of zeta-case prime sums.
- `verification.txt`: recorded output of that program.

## Build and reproduce

```sh
pdflatex -interaction=nonstopmode -halt-on-error three_scale.tex
pdflatex -interaction=nonstopmode -halt-on-error three_scale.tex
python3 verify_filters.py
```

The LaTeX source uses ordinary TeX Live packages. No external data or network access is needed to reproduce the Python output. The floating-point samples are not rigorous intervals or estimates of the actual limsups. The exact tests verify finite identities, not the analytic theorem.

## Mathematical status

The paper proves a three-scale reconstruction result from Dirichlet GRH and standard analytic facts about Dirichlet L-functions. It also proves a primitive-conductor inversion formula, an oriented extension for individual complex characters, and a two-scale obstruction for general positive spectra. It does not assume simplicity or independence of zero ordinates.

The repository was inspected at revision `72fead102f663d5c7a407964a13dc0cf9d977207` through GitHub. Its machine-check status is reported, not independently replayed here. This new research note is not Lean-formalized; the proof is a human-readable derivation from the established inputs. The exact reconstruction uses infinite limits in a specified order, not a practical finite-time method of computing zeros. A targeted literature search did not locate the specific construction; independent priority and expert review remain outstanding.

Sources: <https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207>, <https://en.wikipedia.org/wiki/Riemann_hypothesis>, and the references listed in the manuscript.
