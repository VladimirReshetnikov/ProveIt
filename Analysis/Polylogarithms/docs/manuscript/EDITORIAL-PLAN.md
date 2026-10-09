# A unified manuscript of special values and experimental discovery

Completed: see [the manuscript](polylogarithms.pdf),
[the source ledger](EDITORIAL-LEDGER.md) and [validation](VALIDATION.md).
The plan below records the organizing decisions made before consolidation.

The canonical deliverable will be `polylogarithms.tex` and its rebuilt PDF.
Its organizing question is how exact transformations expose the arithmetic
structure of special values, and how computation suggests the next theorem.

1. Foundations: branches, nested sums, iterated integrals, shuffle/stuffle,
   MZVs, harmonic and Nielsen polylogarithms.
2. Cyclotomic coordinates: Clausen values, characters, the polygamma DFT,
   parity and algebraic coefficient fields.
3. Algebraic arguments: vertical lines, arctangent integrals, golden and
   cubic ladders, Bloch elements and the limits of ladder counting.
4. Gaussian and Eisenstein depth: exact reductions, the proven even-weight
   odd-Euler-sum family, experimental odd-weight directions, doubles,
   triples and mixed cube-root points.
5. Gamma values and certificates: rational grids, trig-root phenomena,
   exact row combinations, domain conditions and conjectural completeness.
6. CM polygamma: row sums, modular forms, periods, class-field structure.
7. Zeta jets and integration: Stieltjes antiderivatives, moments,
   negative-order polygamma, rational and character coordinates.
8. Parameter differentiation: harmonic-number master identity, explicit
   tables, functional-equation duality and finite rank experiments.
9. Herglotz arithmetic: finite dilogarithm sums, rational families,
   quadratic units, Kronecker limit formulas and conditional Stark values.
10. Discovery and proof: computational conventions, numerical controls,
    certificate boundaries, literature problems and an integrated agenda.

The source-to-manuscript ledger must account for all 39 source documents.
Earlier reports that are wholly subsumed by later articles are merged at
result level, not repeated. External literature-search inputs supply leads,
not accepted mathematics. Historical numerical receipts remain explicitly
historical unless rerun here. No Lean formalization is claimed.

## Corrections already identified

- Replace gamma completeness attributed to Koblitz--Ogus by relative
  completeness and the open Rohrlich conjecture.
- Replace negative-PSLQ independence and non-elementarity claims throughout
  by bounded experimental observations.
- A zero canary coefficient is a diagnostic, not a proof. Independence of
  the Champernowne constant from the period basis is not known.
- Correct the external `6 Li_2(1/3) - Li_2(1/9)` constant to
  `pi^2/3 - log(3)^2`.
- Preserve the corrected sign of the `Gamma_1(1/3)` mixed logarithm.
- Audit the Herglotz collapse criterion: `F(1/7)` already contradicts its
  printed necessary condition.
- Audit the Herglotz cotangent derivative at even denominators: the
  underlying paper uses a cotangent function assigned value zero at integers.
- Remove the assertion that counting a finite set of cyclotomic relations
  proves that a base has no higher ladder of any kind.

## Acceptance

Complete result-level coverage ledger; corrected unified prose and notation;
reproducible focused numerical and symbolic checks; converged LaTeX build;
reference and layout checks; visual review; current README; merge fresh
`origin/main`, commit with detailed message, non-forced push to `main` and
verify remote ancestry and SHA. Work remains active until these are achieved.
