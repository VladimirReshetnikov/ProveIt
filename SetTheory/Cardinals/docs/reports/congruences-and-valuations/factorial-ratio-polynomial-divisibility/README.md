# Polynomial divisibility of height-one factorial ratios

Research article and reproducible exact certificates, September 19, 2026.

## Start here

Read **article.pdf** (20 pages). Its source is **article.tex**; the atlas table
loaded by the source is supplied in `data/atlas_table.tex`.

The manuscript gives a general rational-root criterion for uniform polynomial
divisibility of balanced integral factorial ratios. It applies the criterion to
Peter Bala's uniform-product conjectures for OEIS A211417 and A295431, proves
explicit multipliers for every product length, and certifies the least
multipliers in the eight particular examples. The article also contains an atlas
for the 52 sporadic height-one ratios, exact recurrences, generating functions,
and asymptotic expansions.

The main existence and classification proofs are conventional mathematical
arguments. The eight optimal-constant results additionally use finite exact
certificates. Neither a large numerical sample nor an unverified graph search is
being substituted for an all-index proof. See **STATUS.md** for the boundary
between the results offered here, earlier work, and unchecked questions of priority.

## Verify without trusting the generator

Python 3.10 or later is required; no third-party Python packages are needed.
From this directory run:

```sh
python code/verify_certificates.py
python code/test_research.py
```

Use `python3` in place of `python` on systems where appropriate.
The first command reads the supplied certificates and recomputes every graph
transition. It does **not** import or run the graph generator or its optimizer.
It checks the eight stated problems, all required primes, closure of every
state set, every integer potential inequality, and direct equality witnesses.
Its recorded output is:

```text
PASS: 8 cases; 60 prime certificates; 1685 states; 19277 exact transition inequalities.
All prime-coverage, potential, and sharpness checks passed.
```

The second command runs supplementary regression tests. Their output and exact
counts are in `data/test_results.json` and `data/regression_output.txt`.
The tests include 256-bit indices with the fixed random seed 20260919. Finite
regression tests supplement the proofs; they do not establish the all-index claims.

To regenerate the data and certificates before checking them:

```sh
python code/generate_artifacts.py
python code/verify_certificates.py
```

The parameter file for the atlas is an input, not a generated conjecture.
The generator checks its 52 rows for balance, height one, and nonnegativity of
the Landau step function at every breakpoint.

## Build the PDF

An ordinary TeX Live or comparable installation with pdfLaTeX is sufficient.
The source uses standard packages, including Latin Modern, amsmath, amsthm,
microtype, longtable, tcolorbox, listings, and hyperref. From this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Run once more if TeX requests a cross-reference update. Alternatively, run
`make pdf`. No network access or Python regeneration is needed to compile.
Keep `data/atlas_table.tex` next to the source in its supplied subdirectory.
Font files are not bundled.

## Files

- `article.tex`, `article.pdf`: complete manuscript, proofs, references, and atlas.
- `code/factorial_divisibility.py`: exact factorial-ratio and polynomial-factor
  classes; integrality testing; one-sided capacities; classification; explicit
  multiplier bounds; finite digit-graph certificate generation.
- `code/verify_certificates.py`: separate exact verifier for the eight delivered
  optimal-constant results.
- `code/test_research.py`: regression tests, recurrence checks, and checks of the
  displayed asymptotic coefficients.
- `code/generate_artifacts.py`: regenerates the supplied certificates, tables,
  and sequence terms.
- `data/certificates.json`: states, integer potentials, and equality witnesses
  for all 60 prime certificates.
- `data/sharp_constants.csv`: per-prime minima and witnesses.
- `data/sequence_U.csv`: exact values for indices 0 through 50 of
  `42*A(n)/((2*n+1)*(3*n+1)*(5*n+1))`.
- `data/sporadic_parameters.json`: 52 numerator/denominator parameter lists,
  transcribed with attribution from Gheorghe Coserea's OEIS table.
- `data/atlas_52.csv`, `data/atlas_table.tex`: the computed admissible-slope atlas.
- `data/minima_table.tex`: an alternate generated TeX table of the prime minima.
- `data/certificate_statistics.json`, `data/test_results.json`,
  `data/verification_output.txt`, `data/regression_output.txt`: verification record.
- `Makefile`, `STATUS.md`: build shortcuts and research-status notes.

CSV columns containing large sequence values should be read as exact integers
or text, not as floating-point spreadsheet cells.

## Using the library

From within `code/`, for example:

```python
from factorial_divisibility import A, Factor, classify, effective_bound

assert classify(A, (Factor(2, 1), Factor(3, 1), Factor(5, 1)))
assert not classify(A, (Factor(4, 1),))
assert not classify(A, (Factor(2, 1, multiplicity=2),))
cutoff, multiplier = effective_bound(A, (Factor(2, 1),))
```

Primitive factors must have positive slope and coprime slope/offset. Normalize
nonprimitive factors and treat their integer content separately; merge equal
roots and add their multiplicities. The explicit multiplier returned by the
library is a valid bound, not a claim of minimality. The valuation helpers take
primality as a caller precondition. The certificate generator presently handles
products of distinct positive-unit-offset factors `k*n+1`; the mathematical
classification theorem is more general than that optimizer.

## Attribution

The problem statements originate in Peter Bala's August 28, 2025 comments in
OEIS A211417 and A295431. The sporadic parameter data are attributed to Gheorghe
Coserea and the factorial-ratio classification is attributed to Bober and the
preceding work cited in the article. Full references and source URLs are in the
manuscript. The new proofs, derived tables, code, and certificate calculations
in this archive were prepared for the present research request.
