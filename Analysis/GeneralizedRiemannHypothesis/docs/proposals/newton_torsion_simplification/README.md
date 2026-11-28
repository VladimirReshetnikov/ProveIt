# Newton divided differences for the theta-lift proof of RH and Dirichlet GRH

A paper-level replacement for the torsion-specialization lemma in the readable Alpöge–Claude proof. It answers the singly exponential ceiling question posed in the existing `cyclotomic-interpolation-and-theta-lifts` proposal, with a different one-shell Newton method. The required level is uniform in the dimension and degrees, and all chosen coordinates have one common exact primitive order. The mathematical proof is in the report; the Python tests are finite regressions, not a formal proof.

## Files

- `newton_torsion.tex`, `newton_torsion.pdf`: complete 9-page mathematical note.
- `LEAN_PLAN.md`: staged formalization and validation plan (not compiled code).
- `check_newton.py`, `checks.txt`: dependency-free exact cyclotomic and rational regression tests and their actual output.
- `source_manifest.tsv`, `verify_sources.py`: selected Git blobs and all ten proposal trees, with a local verification script.

## Reproduce

```sh
latexmk -pdf -halt-on-error newton_torsion.tex
python3 check_newton.py
python3 verify_sources.py /path/to/ProveIt
```

The source manifest pins commit `ef7d441dcb37ea944b7ac15731bb766f2e1354ea` and is intended for a Git checkout containing that commit. It was assembled using GitHub connector results; local Git verification requires a checkout and was not run here. The selected five central blobs match the independently verified upstream source, but the full current ProveIt readable directory has a different tree hash, so no whole-tree identity is asserted. See https://math.mit.edu/~drew/shortgrh/ for the original proof's verification record. No new Lean elaboration or kernel replay was possible here, and no repository files were modified. The TeX was compiled and the PDF rendered and visually inspected.
