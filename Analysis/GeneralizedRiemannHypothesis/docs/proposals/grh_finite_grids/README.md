# Finite-field grids in the theta-lift proof of Dirichlet GRH

Open **report.pdf** for the mathematical argument. The self-contained **report.tex** compiles with a standard TeX Live installation. The main proposal constructs an explicit Cartesian grid in the local Hecke depth argument. The two companion proposals count height-bounded Fourier frequencies at one finite place and control a principal minor by integrating block matrix equations.

## Source and checks

The study uses ProveIt revision `8f274fb25a0be551cbb53ee802033689da108138`, Lean 4.35.0, and mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The geometric and analytical proofs in the report are at the level of ordinary mathematics. Four Lean files contain twelve checked component theorems. A full replacement build and its net change in line count remain open.

| File | Checked contribution |
| --- | --- |
| lean/FrobeniusSamples.lean | Twisted interpolation, actual Frobenius samples at a primitive element, Vandermonde block formula and invertibility, and lowest-coefficient specialization |
| lean/GridMultiplicity.lean | Pointwise and summed order of vanishing on a fiber over any field |
| lean/HeightSeparation.lean | Local absolute value bound, separation by the height of a difference, and two-chart counting under local coding hypotheses |
| lean/HeightCounting.lean | Divisibility obstruction and finite dyadic summation |

## Reproduce

From the extracted archive directory, build the typeset report and run the tests.

```sh
latexmk -pdf -halt-on-error report.tex
python3 checks/check_depth.py
python3 checks/check_height.py
python3 checks/check_minor.py
python3 checks/check_sources.py /path/to/ProveIt
```

The depth and height tests need only Python's standard library. The minor test uses SymPy (tested with 1.14.0). The source check reads the pinned ProveIt checkout. It verifies the blob and line of every anchor in **evidence/sources.tsv** and the catalog in **evidence/proposal-catalog.tsv**.

To recheck the Lean files independently, set `bundle` to the extracted archive directory and run the following in a mathlib checkout at the revision above with its dependencies available.

```sh
lake exe cache get Mathlib.LinearAlgebra.Vandermonde Mathlib.Algebra.Polynomial.Degree.TrailingDegree Mathlib.Algebra.Polynomial.Div Mathlib.FieldTheory.Perfect Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots Mathlib.Algebra.MvPolynomial.Degrees Mathlib.Algebra.Polynomial.Roots Mathlib.Data.Finsupp.Weight Mathlib.NumberTheory.Height.Basic
for file in "$bundle"/lean/*.lean; do lake env lean "$file" || exit 1; done
```

The transcripts in **evidence/** are from executions of the distributed files. The 406, 236 and 585 source-line figures in the report count current source regions, including comments and declarations that a replacement would still export. They have different scopes and do not measure net deletions or build time.
