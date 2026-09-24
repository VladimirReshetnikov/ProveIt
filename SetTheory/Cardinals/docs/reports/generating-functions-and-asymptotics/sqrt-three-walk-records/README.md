# Exact Records in the Square-Root-of-Three Walk

**Research report and reproducibility package — September 19, 2026**

The article proves the four-phase record recurrence for

    S(N) = sum((-1)^floor(n*sqrt(3)), n=1..N),   S(0)=0,

in the corrected form displayed in Section 2, page 7, of Henk Bruin and
Robbert Fokkink, *On the records and zeros of a deterministic random walk*,
arXiv:2503.11734v2. That source attributes the experimental recurrence to
J. Arias de Reyna and J. van de Lune. The package also gives exact first
passages, a rational generating function, closed forms, sharp logarithmic
extrema, and an extension to every even integer trace D >= 4.

## Read first

Open **article.pdf** (17 pages). The complete editable source is
**article.tex**. It requires the two supplied PDF figures in `figures/`.
The central proof is in Sections 2–5; the infinite-family extension is
Section 8. Section 9 describes exactly what the software checks.

### Status and limitations

The selected recurrence is explicitly experimental in the inspected source.
The report supplies a mathematical proof of that recurrence, including
minimality of every claimed first passage. Computational tests corroborate
it but are not substituted for the proof. The argument has not been
independently refereed or verified in a formal proof assistant.

The literature check does **not** certify that no separate proof exists
elsewhere. Publication priority is not claimed as independently established.
The general conjecture about records for all quadratic irrational slopes
is **not** solved here. The known square-root-of-two record theorem is not
claimed as new. The source's conditional Ostrowski automaton is not separately
verified by this package.

## Main formulas

Put gamma = 2 + sqrt(3), mu = gamma^2 = 7 + 4*sqrt(3),
B(n) = floor(gamma*n), and F(n) = 4*B(n) - n + 7.

With the initial record R_0 = 0, all record positions in increasing order are

    R_(4q+j) = F^q(j),                 q >= 0, 0 <= j <= 3,
    S(R_(4q)) = q,
    S(R_(4q+j)) = -(3q+j),             1 <= j <= 3.

Here F^q is repeated composition, not exponentiation.

The essential endpoint identity is

    S(B(k)) = S(floor((2-sqrt(3))*k)) + 1 - 4*(k mod 2),   k >= 1.

The first-passage argument proves that the next eligible run has number
B(m)+2 and ends at F(m). This is the step that excludes unlisted earlier
records. Every orbit x_q = F^q(s) satisfies

    x_(q+2) = 14*x_(q+1) - x_q + 6.

The ordinary generating function for the full record-position sequence is

    (z + z^2 + z^3 + 4*z^4 - 3*z^5 + z^6 + z^7)
    / ((1-z)*(1-14*z^4+z^8)).

With natural logarithms,

    limsup S(N)/log(N) =  1/log(mu),
    liminf S(N)/log(N) = -3/log(mu).

The full article supplies all derivations, including the equivalence with
the original four-line recurrence, closed-form coefficients, and exact
prefix extrema.

## Software requirements

The computation and verification programs use only **Python 3.10 or later**
and its standard library. There are no network calls and no floating-point
floor decisions. Python integers and `math.isqrt` implement all mathematical
comparisons exactly. The optional plotting program additionally uses
Matplotlib; the already supplied figures make it unnecessary for reading or
rebuilding the article.

All commands below are run from this directory unless an absolute path is
used. The programs locate data files relative to their own location.

## Reproduce the checks

```sh
python3 code/verify.py
```

Default executed tests:

- D = 4: direct summation versus the shrinking algorithm, at every integer
  from 0 through 2,000,000; exact equality of the complete actual and predicted
  record lists over this interval.
- D = 6, 8, ..., 20: the same dense checks through 50,000 for each parameter.
- First 1,001 records for D = 4, with positions up to 286 decimal digits:
  endpoint values, predecessors, lift, and constant-coefficient recurrence.
- First 301 large records for D = 6, 10, 20; original four-phase recurrence
  and central generating function through 1,001 terms; general generating
  function through 301 terms for each even D = 4, 6, ..., 20.

The delivered run passed all checks. See `data/verification.json` for the
machine-readable results and `data/verification.txt` for the console log.
Elapsed time is an observation about this environment, not a portable
performance guarantee.

The large-endpoint checks evaluate the proved shrinking recursion; they do
not enumerate every earlier position up to a 286-digit integer. The proof
of minimality is in the article, not in those large-number tests.

A smaller trial run is available:

```sh
python3 code/verify.py --limit 100000 --general-limit 10000 --large-records 100
```

**Reproduction note:** running the verifier rewrites the CSV files and
`data/verification.json`. It does not rewrite `data/verification.txt` unless
its output is redirected there. Therefore a smaller run replaces the JSON
with smaller-scope results; preserve the shipped logs when comparing runs.
The general generating-function check still uses 301 terms for each tested
parameter, and CSV generation uses the fixed sizes described below.

## Use the exact calculator

```sh
python3 code/record_walk.py walk 2000000
python3 code/record_walk.py record 400
python3 code/record_walk.py extrema 2000000
python3 code/record_walk.py record 120 --D 6
```

Each command returns a JSON object. `record 400` asks for the record indexed
400, not the first 400 records. `extrema N` returns both running extremes on
the inclusive interval [0,N]. Record index zero is the initial pair (0,0).

For programmatic use, add `code/` to your Python module search path:

```python
from record_walk import EvenTraceWalk

walk = EvenTraceWalk(4)
print(walk.value(2_000_000))
print(walk.first_positive(100))
print(walk.first_negative(100))
print(walk.extrema(2_000_000))
```

The parameter D must be an even integer at least 4. General D describes the
slope (D+sqrt(D^2-4))/2, not sqrt(D-1). Only the particular subfamily D=4d has
the same increments as the slope sqrt(4d^2-1).

`value(N)` has O(log(N+1)) shrinking iterations for fixed D. This counts
arithmetic calls, **not** bit operations. Exact-integer costs grow with
operand size. `record(index)` uses a linear number of scalar-recurrence
iterations in the number of completed D-record blocks.

## Data files

- `data/sqrt3_records.csv`: record indices 0 through 1000, exact positions,
  and walk values. Columns: `record_index,position,S_at_record`.
- `data/sqrt3_walk_prefix.csv`: every position 0 through 20000, increment,
  partial sum, running minimum, running maximum. The increment at position
  zero is a placeholder 0, not a walk step.
- `data/even_trace_records.csv`: 101 records for each even D from 4 through
  20. Columns: `D,record_index,position,S_at_record`.
- `data/verification.json` and `.txt`: executed checks and limitations.
- `data/build_audit.json`: compilation and PDF audit details.

**Exactness warning for CSV readers:** record positions may have hundreds of
digits. Import the position column as text or arbitrary-precision integers.
Ordinary spreadsheet numbers or floating-point dataframe columns can round
them silently.

## Rebuild the article and optional figures

A recent TeX Live installation with `latexmk` and the packages named in the
article preamble is sufficient. In particular the article uses NewTX text
and mathematics, AMS packages, `microtype`, `tcolorbox`, and `hyperref`.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The Makefile wraps the same commands:

```sh
make pdf
make verify
make figures       # optional; requires Matplotlib
make clean         # removes TeX intermediates, not the PDF
```

To regenerate plots directly:

```sh
python3 code/make_figures.py
```

The figures are illustrative; floating-point plotting is not used by the
proof checks. No font files or copies of third-party papers are distributed.

## Source provenance

`sources.json` records the inspected primary source, its version and page,
and the scope of the status check. The bibliography in `article.tex` is
self-contained; no bibliography-processing step is needed.

Rebuilding the PDF or rerunning the checks changes file hashes, especially
metadata and elapsed-time fields, so no checksum manifest is distributed. The
archive was checked for CRC errors and the PDF was rendered and visually
inspected after its final build.
