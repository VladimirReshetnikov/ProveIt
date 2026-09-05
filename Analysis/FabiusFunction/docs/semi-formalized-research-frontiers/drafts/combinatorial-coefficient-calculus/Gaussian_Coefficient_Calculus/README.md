# Gaussian Coefficient Calculus

*q-Binomial Kernels, Newton Bases, Bell Polynomials, Parameter Jets,
Inversion, and Asymptotics* — a consolidated companion volume to
[`../Combinatorial_Coefficient_Calculus/`](../Combinatorial_Coefficient_Calculus/).
Assembled 2026-09-04.

## What this package is

One document replacing the three independently written q-binomial
coefficient-calculus reports that arrived on 2026-09-04 (`q_binomial_coefficient_calculus/`,
`q_binomial_coefficient_calculus-2/`, `q_binomial_coefficient_calculus-3/`, all
deleted after the merge; Git history retains them). It keeps one statement and
one proof of every result that two or three reports shared, adds each report's
unique layer in the same notation, and records the dictionary between the
reports' symbols in its provenance appendix.

- `Gaussian_Coefficient_Calculus.tex` — 4,760-line book-class source, 19
  chapters and three appendices. Loads `docs/fabius-notation.tex` by relative
  path; no other dependency.
- `Gaussian_Coefficient_Calculus.pdf` — 89 pages A4, built with three
  `pdflatex` passes; the log passes `scripts/logcheck.py` and
  `scripts/audit_overfull.py` with zero overfull boxes.
- `verification/source1/`, `source2/`, `source3/` — the three exact
  verification programs shipped by the sources, unchanged, with the reports of
  their recorded runs (10,912, 2,693 and 10,267 exact checks respectively).
  `source2` needs SymPy (`requirements.txt`); the others use only the standard
  library. `source3`'s optional final experiment uses `mpmath`.

## Structure

| Chapters | Content | Origin |
| --- | --- | --- |
| 1–5 | Setting and partition-profile kernel; Gaussian polynomials, finite models, negative upper index; convolution, Vandermonde companions, inversion, linearization, weighted transforms, quantum-plane binomial; symmetric functions, the master formula and its ramified kernel; partial fractions and Dilcher identities | spine (first report) with second- and third-report additions |
| 6 | Newton bases on arbitrary nodes: universal node formulae, divided differences, the Gaussian Newton pair, the affine-geometric master connection, the q-integer Newton expansion | third report, second report |
| 7 | Jackson differentiation, geometric Taylor basis, stencils, iterated product rule, the path form of the divided-difference chain rule | spine, third report |
| 8–9 | q-Stirling arrays with affine-geometric closed forms, colored and type-B nodes, normal ordering, q-Dobinski; q-Eulerian polynomials and the Stirling–Eulerian bridge | spine, third report |
| 10–11 | Weighted Bell and Riordan composition; Lagrange inversion with product data, slot trees, area-type q-Catalan, coupled inversion and Good-determinant entries | spine, second and third reports |
| 12–15 | Divisor-sum coefficients; cumulants and jets at q=1; cyclotomic structure, q-Lucas, all-order root jets in two coordinates; weighted and differentiated sums | spine, third report |
| 16–17 | Gaussian filters with full error and noise analysis; the geometric-uniform moment application (Rvachev case); multinomials and factorial ratios | spine, third report |
| 18–19 | Three asymptotic regimes with the uniform double-scaling theorem; computation, the three verifiers, normalization audit, crosswalk to the canonical manuscript, analytic checklist | third report, spine, second report |
| A–C | Formula atlas; formula-selection guide; provenance, notation dictionary, reproduction | spine, third report, editorial |

## Relation to the canonical volume

The canonical manuscript is under concurrent editing by other sessions, so
this consolidation was filed beside it rather than folded in. Folding is a
follow-up: the crosswalk table in chapter 19 names the manuscript labels the
extension attaches to (`thm:newton-expansion`, `thm:bell-symmetric-functions`,
`thm:merged-binomial-inversion`, `thm:merged-weighted-binomial-translation`,
`eq:merged-bell-normalization`, `thm:lagrange-burmann`), all of which exist in
the current manuscript. No Lean files were added; the results here are
candidates for the manuscript's formalization register.

## Build

```text
pdflatex -interaction=nonstopmode -halt-on-error Gaussian_Coefficient_Calculus.tex
```

three times, from this directory. Run each verifier with
`python verify_identities.py` inside its `verification/sourceN/` directory.
