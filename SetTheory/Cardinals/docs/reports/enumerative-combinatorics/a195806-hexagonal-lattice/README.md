# A hexagonal-lattice proof of the triangular-array conjecture A195806

Research report dated September 20, 2026.

## Result and status

The 20-page article gives a complete elementary derivation of the six residue-class
formulas and the constant-coefficient recurrence currently marked conjectural in
OEIS A195806. It starts from the original triangular-array constraints, not from
interpolation. The main steps are an integral six-parameter bijection, four
independent translation intervals, a dihedral chamber reduction, and an exact
rational generating function.

The article also proves minimal quasiperiod 6 and minimal eventual homogeneous
constant-coefficient recurrence order 14, gives an exact centered formula and
reciprocity, and develops a two-bound refinement with its bivariate generating
function and leading volume.

This is an unrefereed research manuscript. It is not a proof-assistant
formalization. The source search did not establish first-in-literature priority.
General quasipolynomiality and D-finiteness were already established in the 2023
source; they are not claimed as new discoveries here.

## Indexing and the source correction

`A(n)` means the number of arrays with entries from `0` through `n`, inclusive.
The article adjoins `A(0)=1`; the OEIS entry starts at `n=1`, with `A(1)=16`.

The printed expression in Conjecture 11 of Kauers and Koutschan, after changing
19496 to 19469 in its final residue case, equals `A(n+1)`, not `A(n)` with this
bound indexing. The uncorrected expression is too large by `1/48` when
`n == 5 (mod 6)`. The main result proves the correctly indexed OEIS formulas;
it is not merely a counterexample to this printed numerical typo.

## Files

- `article.tex`: full self-contained LaTeX source, with bibliography.
- `article.pdf`: compiled, visually checked 20-page article.
- `verify.py`: standard-library-only exact verifier and data generator.
- `verify_symbolic.py`: optional independent SymPy checks, including definite
  integrals for the two-bound volume.
- `data/sequence.csv`: `A(n)` for `0 <= n <= 1000`.
- `data/two_bound_counts.csv`: `A(n,m)` for `0 <= n,m <= 20`.
- `data/verification.json` and `data/verification.txt`: actual main verification
  results and environment information.
- `data/symbolic_verification.json`: actual optional symbolic verification results.
- `sources.md`: dated source and indexing audit.
- `requirements-optional.txt`: optional symbolic dependency.
- `Makefile`: build, verify, and cleanup targets.

## Reproduce the checks

Python 3.10 or later is required. The main verifier has no external dependencies:

```sh
python3 verify.py
```

It writes reports and CSV files to `data/` by default. To choose another directory:

```sh
python3 verify.py --output-dir another_directory
```

For the independent symbolic companion:

```sh
python3 -m pip install -r requirements-optional.txt
python3 verify_symbolic.py
```

The recorded run used Python 3.13.5 and SymPy 1.14.0. Both programs use exact
arithmetic and require no network access when running.

The main verifier checks three identities of integer polynomials that imply
all-index generating-function statements. Separately it exhaustively enumerates
the original arrays for bounds 0, 1, and 2; compares the full lattice sum and
chamber sum through 100; compares the chamber sum and closed form through 300;
and compares rational-series coefficients and the closed form through 1000.
It also checks the two-bound rectangle, orbit properties, reciprocity, the
centered expression, and the exact printed-source correction. The included
reports give the complete scope. Finite tests are not substituted for the
mathematical proof.

## Build the PDF

Use a normal TeX Live or MiKTeX installation with pdfLaTeX, Latin Modern,
AMS packages, geometry, microtype, booktabs, fancyhdr, enumitem, and hyperref.
There is no BibTeX step: the bibliography is in `article.tex`.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

On systems with `make`, `make all` builds the PDF and runs the dependency-free
verifier. `make symbolic` runs the optional companion. `make clean` removes
LaTeX intermediate files, not the PDF or reports.

## Using the counting functions

```python
from verify import chamber_count, quasipolynomial, mixed_count

assert chamber_count(6) == 12469
assert quasipolynomial(6) == 12469
assert mixed_count(6, 6) == 12469

# The polynomial continuation accepts negative integers for reciprocity checks.
assert quasipolynomial(-10) == quasipolynomial(8)
```

`quasipolynomial(n)` uses Horner evaluation of the appropriate residue polynomial.
`chamber_count(n)` is the independent positive weighted sum. `mixed_count(n,m)`
uses two bounds: the six corner-adjacent noncorner positions have bound `n`, and
the three side midpoints plus three interior positions have bound `m`.

No third-party PDFs or font files are included in the archive.
