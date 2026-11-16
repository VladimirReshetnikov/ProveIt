# Gauss hypergeometric function in intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, 16 November 2026.

## Main deliverables

- `report.pdf`: compiled research report.
- `report.tex` and `sections/*.tex`: complete LaTeX source.
- `theorem_inventory.csv`: 104 source-row coverage ledger.
- `lean/HypergeometricFinite.lean`: finite algebra development plus explicitly
  marked planned theorem declarations.
- `lean/HypergeometricIPRA.lean`: object-theory migration interface.
- `lean/FORMALIZATION_PLAN.md`: detailed path to `Prf PRAAx` derivations.
- `code/validate_finite.py`: exact-rational and high-precision regression tests.
- `evidence/validation.json`: deterministic test output.
- `evidence/package_audit.txt`: PDF, inventory, computation, and Lean status audit.
- `SOURCE_MANIFEST.md`: consulted sources and repository integration points.

## Mathematical scope

The report separates four levels.

- **A — exact finite/formal algebra.** Pochhammer identities, coefficient
  recurrence, termination, formal differentiation, the Gauss ODE, formal
  uniqueness, Frobenius recurrences, Euler/Pfaff and certified algebraic
  pullbacks, contiguous identities, finite continued fractions,
  Chu–Vandermonde, Jacobi/Legendre/Chebyshev specializations, the cubic radical
  equation, and the Glasser/Fuss–Catalan family.
- **B — effective analysis.** Strict-disk convergence, termwise
  differentiation, Euler's integral, beta/incomplete-beta/elliptic reductions,
  Gauss/Kummer/Bailey summations, and pathwise equality, each as a first-order
  theorem schema for fixed primitive-recursive names carrying explicit
  moduli, bounds, and apartness witnesses.
- **C — conditional branch/contour results.** Connection formulas, Barnes
  integrals, global Kummer forms, monodromy matrices, and infinite continued
  fractions under displayed finite certificates.
- **D — not proved here.** The isolated modular values in MathWorld equations
  (18)–(24), the global modular-lambda inversion, the finite-monodromy
  classification, and source-page mentions lacking a printed formula.

The 104 inventory rows have status counts:

```text
A      16
A/B    32
A/C    11
B      20
C      14
D      11
```

These are source claims, not 104 logically independent theorems.

## Formalization status

The human arguments are developed for the stated finite/effective contracts.
The Lean files are **not claimed to be compiled or kernel checked**.  The
finite companion uses explicit `axiom` declarations in a namespace named
`Planned` instead of hiding missing work behind `sorry`.  A result should only
be called formally proved in iPRA after it has been implemented as a closed
`Prf PRAAx` derivation, built in the `IPRADerivations` library, transported by
`pra_iff_native`, and audited with no `sorryAx`.

## Exact validation

Run:

```sh
python3 code/validate_finite.py \
  --output evidence/validation.json --dps 100
```

The current evidence reports 780 exact checks, all passing.  The exact layer
uses only Python integers and `fractions.Fraction`.  If `mpmath` is present,
the program additionally checks MathWorld equations (18)–(24) to high
precision.  Those numerical checks are not proofs and do not alter their D
status.

## Rebuild

A standard TeX Live installation with the packages in `report.tex` is enough:

```sh
make pdf
make validate
make checksums
```

or simply:

```sh
make all
```

The PDF build runs `pdflatex` three times to settle the table of contents and
cross-references.  `make clean` removes only LaTeX build auxiliaries.
