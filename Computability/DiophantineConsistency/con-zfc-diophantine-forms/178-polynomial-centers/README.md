# Polynomial centers for Diophantine consistency

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026, with AI assistance.

Start with **report/report.pdf**. Its editable LaTeX sources and a single-file
edition are in `report/`.

## Main result

The literal equation in `whole_product/equation.json` has **ten strictly
positive integer variables, exact degree 208, and 116 live binary arithmetic
operations**: 71 multiplications, 24 additions, and 21 subtractions.

An exact polynomial center for the whole Pell product lowers the norm defect
in the ten-positive-variable branch. Whole-expression centers already occur
in the eleven-integer branch of source packages 153, 154 and 165; the present
contribution is the explicit quotient center and its new positive-domain bound.
A signed coefficient-majorant proof establishes the necessary transport bound
before any positivity assumption about the encoded computation. The complete
ordinary proof, composed with the named inherited arithmetic and refutation
calibrations, gives in ZFC:

> The equation has no solution in its stated domain if and only if Con(ZFC).

All four fixed integer coefficient payloads and a finite independent
reconstruction are supplied. The formula contains no variable exponent,
factorial, division, floor or unspecified universal predicate.

## Alternative points

| Component | Domain | Variables | Exact degree | Operations |
|---|---|---:|---:|---:|
| compact/trace_inverse85 | positive integers | 10 | 232 | 85 |
| compact/square_transport85 | positive integers | 10 | 232 | 85 |
| compact/lower_center87 | positive integers | 10 | 228 | 87 |
| compact/centered_transport88 | positive integers | 10 | 224 | 88 |
| compact/quotient_center96 | positive integers | 10 | 220 | 96 |
| **whole_product** | **positive integers** | **10** | **208** | **116** |

`direct/` provides a separate C222-calculus route without K215 simulation or
Jones's universal equation. Its selected direct quartics include:

| Endpoint | Domain | Variables | Quadratic rows | Collected monomials | Height |
|---|---|---:|---:|---:|---:|
| natural203 | nonnegative integers | 203 | 155 | 8,237 | 799,349,232 |
| natural203_sparse | nonnegative integers | 203 | 155 | 8,263 | 207,116,893 |
| natural203_reduced | nonnegative integers | 203 | 155 | 49,682 | 481,920 |
| radical233 | unrestricted integers | 233 | 169 | 10,379 | 12,874 |
| radical234_sparse | unrestricted integers | 234 | 170 | 4,858 | 13,448 |

The 204-natural intermediate is retained. Each direct polynomial is the sum
of the squares of its literal quadratic residual list, with all collected
coefficients supplied separately. The natural reduction carefully distinguishes
canonical-witness completeness from a pointwise zero-set bijection.

## Reproduce

Python 3.10 or later and the standard library suffice:

```sh
python3 -B verify_all.py
python3 -B -O verify_all.py
```

The top-level checker authenticates the source bindings and all finite
component checks, reconstructs the fixed numerals, and checks the literal
report tables. It creates no consistency witness and does not assert that
the equations are unsolvable. The unbounded proofs are separate.

To rebuild the PDF with a standard TeX Live installation:

```sh
sh build_report.sh
```

The builder keeps intermediate files in a temporary directory. PDF metadata
can change between engines; canonical mathematical data are the JSON graphs,
coefficient bytes, and residual lists. `report/report.tex` is a single-file
LaTeX edition of the complete article.

## Contents and scope

- `whole_product/`: principal degree-208 graph, unbounded proof, exact sparse
  algebra, producer, two independently implemented graph checks, and receipts.
- `compact/`: five comparison graphs, their proofs, the fixed coefficient
  reconstruction, immediate parent proofs, and source licenses.
- `direct/`: direct quartics, exact projection and inverse certificates,
  source equations, natural-domain proofs, and independent coefficient checks.
- `report/`: article, complete finite coefficient recipe, literal circuit,
  all 155 residuals of the principal natural quartic, and compiled PDF.
- `verification/`: root replay receipts and independent internal reviews.
- `SOURCE_SNAPSHOT.json`: immutable repository boundary and important file bindings.
- `MANIFEST.sha256`: final file identities.

The comparison snapshot is ProveIt
`fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb`. This is an additive submission
for `docs/incoming`; no remote repository files were changed.

This package establishes measured improvements relative to inspected sources,
not a global simplest-equation theorem. The main ten-variable construction
retains native/K215 ancestry. The direct quartics use the separately identified
C222/ZF/ZFC calibration. The inherited proof-assistant developments were not
rebuilt, and the new polynomial bridge is not newly formalized end to end.
The included reviews are AI-assisted internal reviews, not outside human
peer review. The work neither assumes nor proves Con(ZFC).
