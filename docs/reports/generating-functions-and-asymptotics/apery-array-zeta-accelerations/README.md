# Apéry Arrays and Conjectural Zeta Accelerations

Research note dated September 20, 2026.

## Main result

The article proves the entire shifted-diagonal zeta(3) family described
conjecturally in OEIS A143007. It also proves both neighboring-diagonal
zeta(2) conjectures in A108625 and extends them to all nonnegative upper
and lower offsets. The arrays' main diagonals are the classical Apéry
sequences A005259 and A005258.

The proofs are self-contained finite telescoping identities, rational
lattice potentials, and explicit limit estimates. No computer test or
unproved conjecture is used to establish the theorems. The article also
derives rational error bounds, numerator and denominator recurrences,
and sharp fixed-offset asymptotic constants.

The consulted OEIS versions still describe the targeted formulas
conjecturally. This is not a claim that no proof has previously appeared
elsewhere. Apéry acceleration and its two-dimensional viewpoint are
classical; the article distinguishes this background from its direct
proof of the exact entry statements. This is an unrefereed research note,
not a record of an OEIS submission or a publication acceptance.

## Files

- `article.pdf`: complete typeset article (21 pages).
- `article.tex`: editable LaTeX source; bibliography included in the source.
- `verify.py`: exact tests and rational-interval generation; standard library only.
- `make_error_table.py`: generates the LaTeX error table from exact CSV fractions,
  with outward rounding of displayed bounds.
- `symbolic_certificates.py`: optional SymPy verification of five algebraic identities.
- `numerical_checks.py`: optional high-precision mpmath cross-checks and asymptotic ratios.
- `data/`: exact array prefixes, rational partial sums and bounds, test records,
  the generated table, and optional numerical output.
- `SOURCES.md`: source URLs, consulted revisions, and scope of attribution.
- `OEIS_NOTES.md`: concise mathematical summaries suitable for preparing a future
  explanatory note; nothing has been submitted.
- `Makefile`: build and verification targets.

## Build the PDF

A reasonably recent TeX Live installation with `newpx`, `amsmath`, `amsthm`,
`mathtools`, `microtype`, `booktabs`, `geometry`, `xcolor`, `enumitem`,
`fancyhdr`, `titlesec`, `hyperref`, and `cleveref` is sufficient.

Run in this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

A third pass may be needed after edits that change page breaks. Alternatively,
use `make pdf`. The supplied `data/error_table.tex` is required by the article
and is already included; Python is not required merely to rebuild the PDF.

## Exact verification

Python 3.10 or later is required by the scripts' annotation syntax.
The main verifier has no third-party dependencies:

```sh
python verify.py --max-index 40 --offsets 12 --output-dir data
python make_error_table.py
```

Run without Python's `-O` optimization flag, since the exact test assertions
must remain enabled. The recorded run passed 22,962 exact equalities:

- 12,800 cell, closed-edge, and diagonal-increment identities;
- 8,405 potential, symmetry, and independent-formula comparisons;
- 1,599 finite diagonal identities for offsets 0 through 12 and lengths 0 through 40;
- 156 denominator and numerator recurrence identities;
- 2 published-prefix comparisons.

The square and potential grids have coordinates at most 40. Shifted diagonal
checks can have a coordinate as large as 52. Finite verification checks the
implementation; the universal claims are proved in the article.

## Optional checks

With SymPy and mpmath installed:

```sh
python symbolic_certificates.py
python numerical_checks.py
```

The supplied records were generated with SymPy 1.14.0 and mpmath 1.3.0.
The symbolic test reduces each of five rational/polynomial expressions to zero.
The numerical test compares 36 exact partial sums against zeta values at
200 and 250 decimal digits, tests the predicted signs and proven bounds,
and records the ratios to the sharp leading error asymptotics. Numerical
comparisons are additional diagnostics, not rigorous interval arithmetic.

## Interpreting the exact interval CSV

`data/certified_intervals.csv` stores each partial sum `S` and bound `B` as
integer numerator/denominator pairs. `error_sign` is +1 for zeta(3), and
is the mathematically proven sign of zeta(2)-S for the signed families.
The two interval endpoints are `S` and `S + error_sign*B`; order them
increasingly. The exact interval, not its decimal display, is the certificate.

The field `certified_absolute_error_exponent` is the largest nonnegative
integer d with B <= 10^(-d), or -1 when B > 1. It does not itself certify
a particular correctly rounded decimal string. The displayed `bound_decimal`
column is rounded for readability; the article's table instead rounds
upward, and the exact fraction is authoritative in both cases.

All array indices in this package are square-array coordinates. They are
not flattened antidiagonal sequence indices. In particular, C(m,n) is
not symmetric: its first coordinate is the lattice dimension parameter,
and its second coordinate is the radius.
