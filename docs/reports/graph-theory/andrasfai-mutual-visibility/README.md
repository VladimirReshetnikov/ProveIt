# Mutual-visibility sets in Andrásfai graphs

**A proof of the generating-function conjecture in OEIS A391632, with cardinality refinements.**

Research report prepared for Vladimir Reshetnikov, 19 September 2026.
Mathematical derivation, article, and code by ChatGPT.

## Start here

Read `article.pdf` (19 pages). Its editable LaTeX source is `article.tex`.
The core result is an exact, weight-preserving bijection between mutual-visibility
sets of the n-Andrásfai graph and anchored closed walks of length 3n−1 in a
four-state labeled graph, for n ≥ 2. The exceptional first graph is handled
separately.

The scalar generating function is

    sum(a(n)*x^n, n>=1)
      = x*(4 - 19*x + 33*x^2 - 40*x^3 + 8*x^4)
        /(1 - 10*x + 29*x^2 - 32*x^3 + 8*x^4).

This is the formula attributed to Andrew Howroyd, 12 January 2026, in OEIS
A391632. The entry still marked it as conjectured when consulted on
19 September 2026. Source: https://oeis.org/A391632

The report also proves the full bivariate generating function, an exact binomial
formula for every cardinality, maximum-set classification, eventual polynomiality
at every fixed deficit from maximum, the exponential asymptotic, and a cardinality
central limit theorem. It includes linear-time recognition and exact uniform
sampling algorithms.

This is a self-contained proof with executable checks, not an independently
refereed or proof-assistant-verified result. The targeted literature search does
not certify exclusive priority for the proof or all its corollaries.

## Contents

- `article.tex`, `article.pdf`: the complete mathematical report.
- `code/visibility.py`: standard-library exact counts, coefficient enumeration,
  return-block formula, fixed-deficit counts, O(n)-time recognition, exact sampler.
- `code/verify.py`: independent shortest-path checks, actual closed-walk
  multiplicity checks, cross-validation of formulas, and sampler smoke tests.
- `code/exhaustive.cpp`: direct graph predicate versus flags for every subset;
  additionally checks equality of graph and cyclic-pattern obstruction families.
- `code/symbolic_certificate.py`: exact SymPy matrix/polynomial identities,
  fixed-deficit polynomials, and implicit-differentiation checks.
- `code/make_figure.py`: the exact distribution illustration in the article.
- `data/exhaustive.json`: actual C++ run for n=1,...,8 (9,586,980 subsets).
- `data/verification.json`: actual standard-library test results.
- `data/symbolic_certificate.txt`: actual symbolic results and approximate constants.
- `data/b391632_extended.txt`: 250 indexed terms, locally derived rather than an
  official OEIS b-file or submission.
- `data/visibility_coefficients.csv`: all coefficient rows for n=1,...,50.
- `data/sequence_table.tex`: the first 20 totals in tabular-row form.
- `data/environment.json`: the local verification environment, for provenance.
- `figures/cardinality_distribution.pdf`: vector figure needed to rebuild the PDF.
- `source_notes.md`: exact source provenance and the scope of the priority search.
- `Makefile`, `requirements.txt`, `SHA256SUMS.txt`: build/reproduction support.

## Run the core code

Python 3.9 or later is sufficient. No packages are required for these commands:

```sh
python code/visibility.py --n 20 --sample
python code/verify.py
python code/visibility.py --write-data data
```

The first command returns the total, the complete cardinality coefficient list,
and one reproducibly seeded sample. To use the module directly, add `code` to
Python's module search path and import `total`, `polynomial`, `is_visible`, or
`UniformSampler` from `visibility`.

The membership word has exactly 3*n−1 bits, with bit i indicating whether
vertex i is selected. The graph has vertices 0,...,3*n−2 and connection steps
1,4,7,...,3*n−2. Counts are for labeled subsets, including the empty set. They
are not counts modulo cyclic rotation.

## Reproduce the larger exhaustive check

With a GCC-compatible C++17 compiler:

```sh
g++ -O3 -std=c++17 code/exhaustive.cpp -o exhaustive
./exhaustive 8 > data/exhaustive.json
python code/verify.py
```

On Windows with MinGW, the executable is ordinarily `exhaustive.exe` and may be
run as `./exhaustive.exe`. The checker uses GCC/Clang bit-operation built-ins;
it is not written for unmodified MSVC compilation. Its optional integer argument
is the largest n to test (1 through 9). Runtime grows exponentially because it
explicitly examines every subset.

The Python test automatically checks the C++ JSON if it is present. Its separate
BFS test examines every subset through n=5 using the original shortest-path
definition; this test does not assume diameter two. All assertions should remain
enabled: run normal Python, not `python -O`.

## Optional symbolic and figure dependencies

```sh
python -m pip install -r requirements.txt
python code/symbolic_certificate.py
python code/make_figure.py
```

Only SymPy is needed for the symbolic script; only Matplotlib is needed for the
figure script. The pinned Matplotlib version requires Python 3.10 or later; the
standard-library counting and verification code remains compatible with Python 3.9. Versions used in the actual run are recorded in
`data/environment.json`. The requirements pin that tested environment, without
claiming that those are the newest releases.

The symbolic script proves finite polynomial identities by exact algebra.
It does not formalize the graph-to-automaton bijection. Printed decimal constants
are approximations; the article's asymptotic statements define their constants
algebraically.

## Rebuild the article

With a reasonably complete TeX Live installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Or run `make pdf`. The already included vector figure is sufficient; Matplotlib
is not required just to compile the article. The article uses standard packages
including New PX, AMS mathematics, TikZ, booktabs, cleveref, and hyperref. No font
files need to be copied into the project.

The delivered PDF was compiled twice after final edits and all 19 pages were
rendered and visually inspected. The final build emitted no overfull-box or
unresolved-reference warnings.

## Integrity

`SHA256SUMS.txt` records the hashes of all other deliverable files. From this
directory, `sha256sum -c SHA256SUMS.txt` verifies the extracted files. Re-running
tests or rebuilding the PDF can change hashes, especially timing and metadata.
No generated executable, TeX auxiliary file, Python cache, or downloaded
third-party paper is included.
