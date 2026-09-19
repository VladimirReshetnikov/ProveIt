# Rational exponents, nonrational coefficient counts

**An explicit negative answer to a question of Richard Stanley**  
Research manuscript prepared with ChatGPT, September 19, 2026.

Read `research.pdf` for the complete argument. `research.tex` is a self-contained
LaTeX source, including its table and bibliography.

## Result

The construction answers the universal-rationality part of MathOverflow
question 431075 negatively. It gives positive integer exponents tending to
infinity with a rational ordinary generating function, but the counts of
coefficients equal to 1 in the successive products

    P_m(x) = product_{j=1}^m (1 + x^G_j)

have a generating function with a natural boundary on the unit circle.
In particular, the counting series is not rational, algebraic, or D-finite.

The core construction is

    a_0 = 2, a_1 = 1, a_n = a_(n-1) - 2 a_(n-2),
    T_0 = 0,
    b_n = T_(n-1) + 2^n - 1 + a_n,
    T_n = T_(n-1) + b_n,
    G_(2n-1) = 2^(n-1), G_(2n) = b_n.

For n >= 2, the exact counts are

    nu_1(2n-1) = 4,
    nu_1(2n)   = 4 + 4 * indicator(a_n > 0),

with nu_1(0), nu_1(1), nu_1(2) = 1, 2, 4.

**Scope and status:** these are proofs, not conclusions inferred from finite
sequence data. The manuscript is unrefereed, and a targeted search does not
establish priority conclusively. The exponents are not eventually increasing;
monotonicity is not a hypothesis in the source question. The result does not
classify all exponent sequences, settle an increasing-exponent variant, or
claim differential transcendence. No Lean formalization is included.

## Contents

- `research.pdf` and `research.tex`: article with full proofs, asymptotics,
  frequencies, correlations, a general sign-coding theorem, and a proof audit.
- `code/compact_check.py`: short, directly inspectable, standard-library check
  of the original products through 20 factors.
- `code/verify.py`: independent exact dense multiplication and weighted-support
  event sweeps; recurrence identities, bounds, parity, and general-control tests.
- `code/symbolic_verify.py`: optional exact SymPy verification of the displayed
  rational-function and closed-form identities.
- `data/verification.json`, `data/symbolic_verification.json`: recorded results.
- `data/environment.json`: versions actually used, not claims about latest releases.
- `data/block_table.csv`: exact data for 20 blocks (40 exponents).
- `data/exponents_bfile.txt`: G_m for 1 <= m <= 256.
- `data/trace_bfile.txt`: a_n for 0 <= n <= 128.
- `data/coefficient_counts_bfile.txt`: theorem-derived counts for 0 <= m <= 20000.
- `notes/source_status.md`: source, hypothesis, and priority notes.
- `Makefile` and `requirements-optional.txt`: build and optional test helpers.

The b-file-style data have no assigned or assumed OEIS identifiers. The long
count file and the later CSV rows are generated from the proved formula, not
from direct multiplication of every polynomial in the list.

## Reproduce the checks

Run these commands from this directory. Do not use Python's `-O` flag: the
verifiers deliberately use assertions and reject an optimized run.

The shortest independent check needs only the Python standard library:

```sh
python3 code/compact_check.py
```

The full standard-library checks are:

```sh
python3 code/verify.py
```

To reproduce the larger recorded check and the symbolic certificates:

```sh
python3 -m pip install -r requirements-optional.txt
python3 code/verify.py --numpy-dense 19
python3 code/symbolic_verify.py
```

The supplied full run used Python 3.13.5, NumPy 2.3.5, and SymPy 1.14.0.
Only the optional commands need NumPy or SymPy. Running `verify.py` refreshes
its JSON report and data files; the default run does not repeat the optional
38-factor check. Use `--numpy-dense 19` to reproduce that recorded range.

The 38-factor NumPy check stores a final vector of 9,698,330 signed 64-bit
integers (about 77.6 MB), in addition to temporary arrays. All coefficients
are computed exactly without saturation: their sum is 2^38, which is below
2^63 and bounds every individual coefficient. No floating-point sign tests
are used anywhere in the verifiers.

### Recorded verification ranges

| Check | Range | Result |
|---|---:|---|
| Direct Python-integer multiplication | 28 factors, degree 221,003 | passed |
| Independent NumPy int64 multiplication | 38 factors, degree 9,698,329 | passed |
| Exact weighted-support event sweep | 34 factors | passed |
| Recurrence, parity, bounds, GF coefficient identity | 4,000 exponents | passed |
| General sign-coding controls | all 256 words c_3,...,c_10 in {-1,1} | passed |
| Exact trace-sign statistics | first 100,000 signs | 49,998 positive; 50,002 negative |
| Symbolic identities | five cancellations and one polynomial gcd | passed |

At 38 factors, the largest polynomial coefficient was 34,368.
These checks validate implementations and finite instances. The proofs of
nonperiodicity and the natural boundary are in the article and do not depend
on a numerical experiment or recurrence-guessing procedure.

## Compile the article

Use a TeX installation with pdfLaTeX and the packages named in the preamble,
including `newpx`, `amsmath`, `amsthm`, `mathtools`, `microtype`, `booktabs`,
`enumitem`, `fancyhdr`, `titlesec`, `tcolorbox`, `listings`, `hyperref`, and
`cleveref`. Font files are not distributed with this archive.

```sh
pdflatex -interaction=nonstopmode -halt-on-error research.tex
pdflatex -interaction=nonstopmode -halt-on-error research.tex
pdflatex -interaction=nonstopmode -halt-on-error research.tex
```

Alternatively, `make pdf` builds the article, `make check` runs the
standard-library checks, and `make full-check` runs the larger and symbolic
checks. `make clean` removes only LaTeX auxiliary files, not the PDF.

## Source

Richard Stanley, “A conjectured rational generating function,”
MathOverflow question 431075, posted September 23, 2022:
https://mathoverflow.net/questions/431075/a-conjectured-rational-generating-function

The article's bibliography and `notes/source_status.md` distinguish this
question from the earlier, more specialized Fibonacci-exponent question.
