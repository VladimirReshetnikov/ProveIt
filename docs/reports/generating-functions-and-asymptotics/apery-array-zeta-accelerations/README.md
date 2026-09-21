# Apéry Arrays and Conjectural Zeta Accelerations

Research note dated September 20, 2026; merged edition September 21, 2026.

## Provenance

This package is the union of two independently prepared archives that
proved the same three theorems by the same argument:

- `apery-array-zeta-accelerations` — the base of this merged edition, source
  of the presentation, the Legendre/Rodrigues appendix and row generating
  functions, the zeta(2)/A005258 recurrence, both Casoratians, the
  numerator-array inheritance argument, the fixed-row asymptotics, the
  sharper neighbouring-entry error bounds, the crystal-ball geometric
  setting, and the OEIS revision numbers.
- `apery-shifted-diagonal-families` — folded in here and no longer a separate
  archive. It contributed the David (arXiv:2303.09318v3) priority
  acknowledgement, the all-offset shifted-diagonal recurrence with its
  companion and Wronskian, the two-variable row recurrence, the certified
  decimal-digit test, the random-monotone-path regression tests, the wider
  contiguity range, the compact-route appendix, the simplified sharp error
  constants, and the q_n-integer / r_n-non-integer caveat.

The shared theorem is proved once, in the base's presentation. The two
write-ups are not offered as alternative proofs, because they are not: the
telescopers, edge weights, path lemma, diagonal-step cancellation and Laplace
saddles are the same. The other package's repackaging of the cubic certificate
into an antisymmetric and a symmetric part is recorded as a remark in
Section 3, where it belongs.

## Main result

The article proves the entire shifted-diagonal zeta(3) family described
conjecturally in OEIS A143007. It also proves both zeta(2) families — the
superdiagonal and subdiagonal families — labelled conjectural in the formula
field of A108625 for k = 0, 1, 2, ... . The arrays' main diagonals are the
classical Apéry sequences A005259 and A005258.

The proofs are self-contained finite telescoping identities, rational
lattice potentials, and explicit limit estimates. No computer test or
unproved conjecture is used to establish the theorems. The article also
derives rational error bounds, certified decimal prefixes, numerator and
denominator recurrences, a three-term recurrence along every shifted cubic
diagonal, and sharp fixed-offset asymptotic constants.

The consulted OEIS versions still describe the targeted formulas
conjecturally. This is not a claim that no proof has previously appeared
elsewhere. Apéry acceleration and its two-dimensional viewpoint are
classical; David's conservative-matrix-field paper already contains closely
related lattice constructions and, up to duality and sign conventions, the
same conjugate polynomials. The article distinguishes that background from
its direct proof of the exact entry statements. This is an unrefereed
research note, not a record of an OEIS submission or a publication
acceptance.

## Files

- `article.pdf`: complete typeset article (27 pages).
- `article.tex`: editable LaTeX source; bibliography included in the source.
- `verify.py`: the union exact-arithmetic suite and rational-interval
  generation; standard library only.
- `verify_independent.py`: a second, independent implementation of the same
  mathematics in the other package's transposed naming convention
  (A108625 written `U(n,m)` with the dimension first). Kept deliberately:
  the independence is the point.
- `make_error_table.py`: generates the LaTeX error table from exact CSV
  fractions, with outward rounding of displayed bounds.
- `symbolic_certificates.py`: optional SymPy verification of the article's
  five algebraic identities.
- `symbolic_certificates_independent.py`: optional SymPy verification of
  seven further identities, in the transposed convention.
- `numerical_checks.py`: optional high-precision mpmath cross-checks and
  asymptotic ratios.
- `asymptotic_diagnostics.py`: optional mpmath comparison of the array and
  error asymptotics at 420 working digits.
- `data/`: exact array prefixes, rational partial sums and bounds, certified
  decimal prefixes, test records, the generated table, and optional
  numerical output.
- `SOURCES.md`: source URLs, consulted revisions, prior-art audit, and the
  explicit list of what is and is not claimed.
- `OEIS_NOTES.md`: concise mathematical summaries suitable for preparing a
  future explanatory note; nothing has been submitted.
- `requirements-optional.txt`: versions used for the optional checks.
- `Makefile`: build and verification targets.

## Build the PDF

A reasonably recent TeX Live or MiKTeX installation with `newpx`, `amsmath`,
`amsthm`, `mathtools`, `microtype`, `booktabs`, `geometry`, `xcolor`,
`enumitem`, `fancyhdr`, `titlesec`, `hyperref`, and `cleveref` is sufficient.

Run in this directory:

```sh
latexmk -pdf -interaction=nonstopmode article.tex
latexmk -c
```

or, without latexmk, two or three `pdflatex` passes. Alternatively use
`make pdf`. The supplied `data/error_table.tex` is required by the article
and is already included; Python is not required merely to rebuild the PDF.

## Exact verification

Python 3.10 or later is required by the scripts' annotation syntax.
Neither verifier has third-party dependencies:

```sh
python verify.py --max-index 40 --offsets 12 --output-dir data
python make_error_table.py
python verify_independent.py
```

Run without Python's `-O` optimization flag, since the exact test assertions
must remain enabled. The recorded run of the union suite passed 34,910 exact
equalities:

- 9,216 four-corner contiguity identities, 1 <= m,n <= 48;
- 6,400 closed-square and diagonal-increment identities, 1 <= m,n <= 40;
- 7,008 termwise telescoper identities, 1 <= m,n <= 16, endpoints included;
- 8,405 potential, symmetry, and independent-formula comparisons;
- 1,599 finite diagonal identities for offsets 0 through 12 and lengths 0
  through 40;
- 600 random monotone lattice paths, 300 per potential, fixed seed 20260920;
- 840 row-recurrence identities;
- 670 shifted-diagonal recurrence, companion-recurrence and Wronskian
  identities;
- 156 main-diagonal denominator and numerator recurrence identities;
- 2 published-prefix comparisons;
- 14 certified decimal prefixes and interval-intersection checks.

The independent reimplementation reports its own total of 25,840 checks over
its own ranges. Both totals are honest; only the union suite's is quoted in
the article. Finite verification checks the implementation; the universal
claims are proved in the article. The exact bounds prove the rational
enclosures; the finite regression tests themselves do not prove the
infinitely quantified mathematical results.

## Optional checks

With SymPy and mpmath installed (`pip install -r requirements-optional.txt`):

```sh
python symbolic_certificates.py
python symbolic_certificates_independent.py
python numerical_checks.py
python asymptotic_diagnostics.py
```

The supplied records were generated with SymPy 1.14.0 and mpmath 1.3.0.
The two symbolic tests reduce five and seven rational/polynomial expressions
to zero, respectively. The numerical test compares 36 exact partial sums
against zeta values at 200 and 250 decimal digits, tests the predicted signs
and proven bounds, and records the ratios to the sharp leading error
asymptotics; `asymptotic_diagnostics.py` does the same for the array growth
constants at 420 digits. Numerical comparisons are additional diagnostics,
not rigorous interval arithmetic.

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

## Interpreting the certified decimal prefixes

`data/certified_digits.csv` (union suite) and
`data/decimal_certificates.json` (independent implementation) record, for
each family and offset at N = 60, the exact rational endpoints L and R and
the largest d with

    floor(10^d * L) == floor(10^d * R),

computed by integer division. That test, not the interval width, is what
certifies a decimal prefix: an interval can be very narrow and still straddle
a decimal boundary. The independent file uses only the largest-coordinate
bound and therefore certifies one place fewer for zeta(3) at k = 0 and k = 3;
both counts are correct for their respective bounds.

## Index conventions

All array indices in this package are square-array coordinates. They are
not flattened antidiagonal sequence indices. In particular, C(m,n) is
not symmetric: its first coordinate is the lattice dimension parameter,
and its second coordinate is the radius. `verify_independent.py` keeps the
other package's letters — the same array is called `U(n,m)` there, still with
the dimension first — so that the two implementations stay textually
independent. The article uses `T`, `C` for the arrays and `Phi`, `Psi` for
the two potentials; the letters `U` and `V` are deliberately not used, since
the OEIS entries call their own arrays `T` and `U` is a natural name for
A108625.
