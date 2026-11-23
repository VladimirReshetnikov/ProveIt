# Analytic geometry in intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, 22 November 2026.

Start with **report.pdf**. Its complete editable source is **report.tex** with
the component chapters in **sections/**.

## Mathematical outcome

The report contains **71 numbered geometry and analysis results**, plus
**7 foundational results**. One foundational result is an external
computability obstruction, expressly not an internal iPRA consistency claim.
The count is of named theorem/lemma/proposition/corollary blocks; definitions,
subclaims, examples, and Lean certificates are not counted again.

| Area | Number of results | Main coverage |
|---|---:|---|
| Affine and metric geometry | 30 | Lines and planes, exact intersection classification, affine coordinates, Gram/Cauchy–Schwarz identities, Euclidean metric, projections/reflections, cross products, skew lines, circles, triangle centers, power, and shoelace area |
| Conics and quadrics | 24 | Rational classification including degeneracy and empty loci, principal axes, quadratic solver, parametrizations, foci/directrices, tangents/polars, optical laws, asymptotes, quadric forms, ruled surfaces, and ellipsoid support |
| Coordinate systems | 9 | Explicit finite sine/cosine sums, addition/derivative estimates, polar/cylindrical/spherical coordinates, oblique metric, locus transformations, and Jacobian identities |
| Polynomial tangency and arc length | 8 | Taylor and divided-difference bounds, graph/parametric tangents, a bounded-bisection implicit function, singular examples, and an explicit polygonal arc-length modulus |
| Foundations | 7 | Rational coding, bounded loops, square-root construction, quantitative name operations, expression transfer, and the zero-test obstruction |

The scope is the mathematical spine of the requested analytic-geometry page
and selected immediate linked topics. The full source-to-result inventory is
`artifacts/theorem_inventory.json`; the report contains a human-readable ledger.
Supplementary deductions are marked. This is not a claim that every theorem
on every linked page has been proved.

## Exact interpretation

The theory is first-order intuitionistic PRA with symbols for specified
primitive-recursive definitions, their defining equations, successor axioms,
and quantifier-free induction.

- Rational inputs have exact, decidable comparisons and primitive-recursive
  operations on natural-number codes.
- Irrational lengths and algebraic intersection points are explicit rational
  expressions with constructed nonnegative square roots, each carrying an
  approximation contract.
- General represented-real assertions are schemas for each **fixed PR input
  family**, with numerical parameters, error bounds, and any required
  apartness certificates. There is no universal total PR evaluator.
- A rational coefficient classification is not an arbitrary-real sign test.
  In particular, singular factorizations do not automatically supply a
  disjunction selecting a component at a crossing.

## Formalization status

The archive contains **four Lean source files** with explicit definitions and
a completion path:

- `lean/ObjectCertificates.lean`: **24 candidate closed derivations in the
  actual ProveIt `Prf PRAAx` proof type**, using its `ipra_ring` infrastructure.
- `lean/ExactCodes.lean`: signed integers, positive-denominator rationals,
  geometric records, intersection and square-root programs, name contracts.
- `lean/AnalyticPrograms.lean`: polynomial evaluation/partials/bounds, finite
  trigonometric approximants, bounded bisection, and the arc-length observer.
- `lean/BridgeSpec.lean`: explicit object-language interfaces and typed
  outstanding bridge obligations. No instances are asserted for them.

**These new Lean sources are uncompiled.** No Lean/Lake executable was available
in the authoring environment. There are no `sorry`, `admit`, or unproved axiom
declarations, but that does not establish successful elaboration or a completed
formalization. The human proofs and executable evidence have their stated,
separate status.

The pinned repository is
`VladimirReshetnikov/ProveIt` at
`bbb85238dac533fc4b7b84a750cca864fe35fed5`.
The target toolchain is `leanprover/lean4:v4.32.0`, with Mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997`.
Eighteen inspected source/blob receipts are in `lean/consulted_sources.json`.
The report distinguishes existing repository build claims from checks
actually rerun here. The repository and dependency caches are not duplicated
in the ZIP.

## Verification performed

- **15,625** exact conic-classification certificate cases, all coefficient
  sextuples in `[-2,2]^6`, covering 12 output classes; a corrupted certificate
  is rejected.
- **2,249** exact-rational geometric formula cases over nine families.
- **4,255** finite analytic checks: dyadic roots, trigonometric tails,
  polynomial remainders, implicit-root intervals, chord refinements, and
  invalid-input guards.
- **47 scalar polynomial identities** checked independently by SymPy:
  28 equations across the actual 24 Lean candidate statements and 19
  supplemental equations across 13 mathematical formula families.
- LaTeX compilation, cross-reference checks, PDF text/bounds checks, and
  visual inspection of rendered pages.

The numerical counts are **finite regression evidence, not universal proofs**.
The symbolic check does not validate Lean types, proof terms, positivity
hypotheses, or constructive branch conditions.

## Reproduce

From this directory:

```sh
python3 code/conic_classifier.py
python3 code/check_affine_metric.py
python3 code/check_analytic.py
python3 code/check_symbolic.py
python3 code/build_inventory.py
bash build.sh
```

The first three numerical scripts use the Python standard library. Symbolic
checks require SymPy (tested with 1.14.0). Recreating the saved illustrative
figure additionally uses Matplotlib and NumPy:

```sh
python3 code/make_figures.py
```

The report builds with standard TeX Live packages, `latexmk`, and `pdflatex`.
It explicitly selects Latin Modern/Computer Modern/AMS font maps to support
minimal TeX installations whose global font-map cache is incomplete.

To attempt the separate Lean gate in an installed pinned ProveIt checkout:

```sh
bash lean/check_in_proveit.sh /absolute/path/to/ProveIt
```

See `lean/README.md` for the remaining formalization stages and acceptance
criteria. `SHA256SUMS` records the delivered files; build products and new
validation runs will naturally change their hashes.

## File layout

| Path | Contents |
|---|---|
| `report.pdf`, `report.tex`, `sections/` | Complete readable report and LaTeX sources |
| `lean/` | Four Lean files, generation source, endpoint index, source receipts, build gate |
| `code/` | Exact reference algorithms, independent checks, inventory and figure generation |
| `artifacts/` | Validation results, theorem inventory, build log and status records |
| `sources/` | Pinned repository metadata and consulted web-source ledger |
| `figures/` | Reproducible mathematical illustration in PDF and PNG |
| `SHA256SUMS` | Integrity manifest |

No repository changes or external publication were made as part of producing
this research packet.
