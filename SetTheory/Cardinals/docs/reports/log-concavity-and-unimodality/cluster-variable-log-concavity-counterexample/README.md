# Single curves do not force log-concavity

Research note, 19 September 2026.

## Main result

An unpunctured annulus with one marked point on each boundary and a single
unit-weight simple lamination curve has a geometrically realized initial
extended exchange matrix

    [ 0 -2 ]
    [ 2  0 ]
    [-1  2 ]

Mutations 2, 1, 2, with the two chosen initial mutable variables specialized
to 1 and the single frozen generator retained as q, produce

    1 + 3 q^2 + 2 q^3 + 4 q^4 + 2 q^5 + q^6.

The positive consecutive coefficients 3, 2, 4 violate log-concavity and form a
strict valley. A fixed seed and fixed curve give infinitely many such examples.
The manuscript proves the geometric realization, not just an arbitrary-matrix
calculation. It also develops recurrences, positive weighted walks, a finite
sum, Fibonacci row sums, and exponential/Gaussian asymptotics.

The target is Conjecture 1 in arXiv:2508.04396v3, with that version's definitions.
The same example conflicts with its general unpunctured-surface unimodality
statement. The final publisher text has not been independently checked, and
there is no claim of exhaustive priority verification or external peer review.
A polygon-only restriction is not settled here.

## Files

- `article.pdf`: the complete 15-page article.
- `article.tex`: self-contained LaTeX source, including the bibliography.
- `verify.py`: dependency-free exact polynomial and matrix verifier.
- `minimal_check.py`: a small, separate fixed-seed recurrence check.
- `verification.txt`: output from the executed full verifier.
- `data/certificates.json`: explicit matrices, mutation steps, coefficient
  sequences, and positive-triple certificates.
- `data/coefficients_d2.csv`: coefficients (including zeros) for 0 <= n <= 40,
  in long format with fields n, degree, coefficient.
- `data/row_sums_A001519.txt`: n and P_n(1), for 0 <= n <= 100; uses the same
  indexing as OEIS A001519, namely 1, 1, 2, 5, 13, ... .
- `data/verification.json`: machine-readable check summary.
- `source_audit.md`: exact source versions, relevant definitions, and limits
  of the literature/status check.
- `Makefile` and `build.ps1`: optional build helpers.

## Run the checks

Python 3.10 or later; no third-party modules, internet access, CAS, or database
connection is required.

```text
python verify.py
python minimal_check.py
```

Regenerate the deterministic data files:

```text
python verify.py --write-data
```

The full verifier checks 201 shear-orbit matrices (including both mutation
involutions), 972 linear/walk/positivity/Fibonacci cases, 396 comparisons
against the nonlinear recurrence and actual extended-matrix mutations,
156 positive finite-sum cases, and fixed-seed failures through n = 160.
All calculations in this verifier use exact integers. These finite tests
corroborate, rather than replace, the manuscript's proofs for all indices.
They do not formalize the topological realization in a proof assistant.

## Build the PDF

A full TeX Live or MiKTeX installation with `latexmk` is sufficient:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

On PowerShell, `./build.ps1` runs both verifiers and then builds the PDF.
On systems with Make, `make all` does the same using `python3`.

The source uses ordinary TeX-distributed packages, including newtxtext,
newtxmath, amsmath, amsthm, mathtools, microtype, geometry, booktabs,
listings, titlesec, hyperref, and cleveref. No external illustrations, font
files, bibliography processor, or shell escape is needed.

## Important indexing and interpretation details

P_0 = P_1 = 1 are the two initially specialized mutable variables. The first
new arc has polynomial P_2. For parameter d, the reference matrix is mutated
d - 1 times to certify the chosen initial triangulation; its mutable variables
are then taken as the independent initial variables. They are set to one only
for that seed's c-polynomial specialization. Newly created variables are never
reset to one along the subsequent mutation chain.

There is exactly one frozen generator q. The powers q^2, q^3, and so forth
are powers of that generator, not independent variables to be identified
again with q. The initial row (-1, 2) comes from one connected curve by a legal
flip from the row (1, 0); relative primality is not used as a connectedness test.
