# What Dirichlet GRH settles

Read **report.pdf** first. Its editable source is **report.tex** (self-contained). From this directory with a standard TeX Live installation, run

    pdflatex -halt-on-error report.tex
    pdflatex -halt-on-error report.tex

## Computations

Under checks/, the Python scripts produce the supplied transcripts. The file abelian_fields.json gives the full 229-field list, with generators of each character group as local rational angles. The file fields.json gives the 207-field multiquadratic sublist described by fundamental discriminants.

    python3 checks/classify.py > fields-reproduced.json
    python3 checks/check_exterior.py > exterior-reproduced.json
    python3 checks/quadratic_input.py checks/check_exterior.py > quadratic-reproduced.json
    python3 checks/nonreal.py > nonreal-reproduced.json
    python3 checks/enumerate_fields.py quadratic-reproduced.json nonreal-reproduced.json > abelian-reproduced.json
    python3 checks/idoneal.py
    python3 checks/represent.py 1848 1849 100000000000000000001
    python3 checks/kummer_test.py
    python3 checks/cubic23.py
    python3 checks/check_euclidean_witness.py

The interior and nonreal character checkers use mpmath and SymPy. The discriminant -23 example uses mpmath. The exterior verifier uses
mpmath and NumPy. The representation, Kummer and
Euclidean examples use only the Python standard library (Python 3.11+ for
decimal logarithms). The Kummer output is finite data for the stated
equivalence. Its rows cannot verify a bound for every integer.

To reproduce the pinned source inventory, clone the source and run

    git clone https://github.com/lsernau/grh-lean.git
    python3 checks/check_repository.py grh-lean

The source inventory reads immutable Git objects and verifies the Git archive
digest. The full Lean/Mathlib builds and kernel replays are documented by
Andrew Sutherland at https://math.mit.edu/~drew/shortgrh/. They were not run
as part of this report. The optional Riemann95Transfer.lean illustrates how to
combine the two source declarations after aligning the toolchains. Its joint
build is untested.

Run the scripts with ordinary Python assertions enabled. Character keys in the JSON are triples [p, numerator, denominator]. They encode rational angles modulo one (the keys -2 and 2 encode the -1 and 5 generators at 2). A field is the fixed field of the intersection of its character kernels in the cyclotomic field of the displayed conductor.

The report links each published theorem to its source and distinguishes the
papers' computations from the ones in this archive. The full upstream
repositories and dependency caches are available at the pinned source links.

Numerical checks used mpmath 1.3.0, NumPy 2.3.5, and SymPy 1.14.0.

A separate numerical cross-check of the unique degree-eight field uses a determinant of Hurwitz zeta values. Run python3 checks/cyclotomic15-crosscheck.py and compare with checks/cyclotomic15-output.txt. The interval proof for this field is in the report.
