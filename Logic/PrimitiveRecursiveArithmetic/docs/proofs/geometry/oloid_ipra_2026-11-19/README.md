# The solid oloid in intuitionistic primitive recursive arithmetic

Read **oloid.pdf** for the proof. The unit of length is the radius of either generating circle. The axial moment is about the line joining their centers, and both transverse moments are about lines through the centroid. All three refer to the homogeneous solid.

## Contents

| File | Purpose |
| --- | --- |
| `oloid.tex`, `oloid.pdf` | Article source and compiled paper |
| `figures/geometry.pdf` | Vector figure used by the LaTeX source |
| `lean/FORMALIZATION.md` | ProveIt revision, Lean module dependencies, finite-observation definitions, error bounds and remaining derivations |
| `lean/ChartAlgebra.lean` | Nine proposed object-theory sequents for the ruling geometry |
| `lean/EllipticReduction.lean` | Three polynomial certificates for exact differentials |
| `lean/Observations.lean` | Rational approximation programs for seven observables |
| `lean/check_lean_certificates.py` | Independent exact check of the twelve polynomial certificates as written in the Lean source |
| `code/check_identities.py` | Recomputes the chart derivatives, column moments and elliptic reductions |
| `code/check_values.py` | Certified rational enclosures, including outward-rounded decimals |
| `code/check_hull.py` | Independent floating-point comparison using polyhedra sampled directly from the two circles |
| `code/make_figure.py` | Regenerates the vector figure |

## Reproduction

Run these commands from this directory. The numerical enclosure program uses the Python standard library. The two symbolic checkers use SymPy. The polyhedron comparison uses NumPy and SciPy, and figure regeneration uses NumPy and Matplotlib.

```sh
python3 code/check_identities.py
python3 lean/check_lean_certificates.py
python3 code/check_values.py 16
python3 code/check_hull.py
latexmk -pdf oloid.tex
```

The figure is included, so LaTeX compilation does not require Python. To regenerate it, run `python3 code/make_figure.py` before compiling.

The exact identity and interval checkers and the polyhedron comparison were run during preparation. The Lean sources were not compiled. The paper gives the human proof in iPRA, and the roadmap describes the additional object-theory derivations needed for an end-to-end kernel check.
