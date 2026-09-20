# OEIS A281434: exact computation and cubic-order growth

This archive contains a self-contained mathematical article, its LaTeX source,
two deterministic exact algorithms, regression tests, and generated data.

## Main conclusions

For n >= 1, with epsilon = 1 when n is odd and 0 otherwise,

    (7*n^3 + 39*n^2 + 26*n + 3*epsilon*(n-1))/24
        <= a(n) <=
    (2*n^3 + 3*n^2 + 4*n)/3.

Therefore a(n) = Theta(n^3). The sharper equivalent a(n) ~ (2/3)*n^3,
and the stronger conjecture that the deficit from the upper polynomial
is O(n), are NOT proved in this article.

The integer recurrence computes a prefix in O(N^4) integer arithmetic
operations and O(N^3) live integer coefficients. The modular implementation
is also exact: a nonzero residue certifies a nonzero coefficient, and every
zero residue inside the proved support envelope is independently checked
with an exact integer formula. It is not a probabilistic zero test.

## Files

- `article.pdf`, `article.tex`: article and source.
- `code/a281434.py`: standard-library exact recurrence, coefficient oracle,
  and optional NumPy modular implementation.
- `code/test_a281434.py`: ten regression-test groups.
- `code/run_experiments.py`: data and benchmark reproduction.
- `data/b281434.txt`: generated a(n), n = 0..100.
- `data/b352697.txt`: generated upper-bound deficits, n = 1..100.
- `data/selected_holes.json`: exact missing triples at selected indices.
- `data/benchmarks.csv`, `data/environment.json`: measured run information.
- `data/test_results.txt`: test output from the supplied implementation.
- `build.sh`, `build.ps1`: PDF build commands for Unix and PowerShell.

The b-files in this archive are computational artifacts of this report;
they are not assertions that OEIS has accepted the new terms.

## Running the algorithms

Python 3.9 or later is sufficient for the reference method.
The modular method additionally requires NumPy:

    python -m pip install -r requirements-optional.txt
    cd code
    python a281434.py 100 --method modular
    python a281434.py 80 --method modular --holes
    python a281434.py 100 --prefix
    python -m unittest -v test_a281434.py

The first command prints 676800. The second prints 347838 and reports the
missing triples (33,36,0) and (42,45,0). Triple coordinates are respectively
the powers of x^x, 1/x, and log(x), after factoring out x^(x^x).

To regenerate the data (these commands overwrite the corresponding files):

    python run_experiments.py --reference
    python run_experiments.py 20 40 60 80 100 101 150 151 200

The larger dense runs can require substantial memory. Runtime is hardware
and interpreter dependent; the included timings are individual measurements,
not guaranteed performance figures.

## Building the PDF

Install a LaTeX distribution with the packages used in `article.tex`.
From the archive root, run `bash build.sh` or `./build.ps1` in PowerShell.
The scripts execute pdflatex three times to resolve references and contents.

## Sources and provenance

The OEIS pages and NIST DLMF were consulted on September 20, 2026:

- https://oeis.org/search?q=id:A281434&fmt=text
- https://oeis.org/A352697
- https://oeis.org/A037237
- https://dlmf.nist.gov/26.8

Original OEIS terms are embedded in the regression tests with their sequence
identifiers. The article provides full source attribution. Its derivations,
algorithm implementations, and additional computed values are supplied here.
