# Normalized residue bounds and polarized equality certificates

Research iteration 19 for Vladimir Reshetnikov and ProveIt, 25 October 2026,
prepared with AI assistance. Start with the enclosed PDF; editable native
LaTeX sources are in `report/`.

## Results

Every selected equation has a zero in its stated integer domain exactly when
there is a finite ZFC refutation, by the ordinary proofs and identified
inherited calibrations. Thus ZFC proves its unsolvability equivalent to
Con(ZFC). This does not assert consistency or decide solvability.

All new endpoints use unrestricted integers and exact degree four.

| Direct quartic | Variables | Quadratic residuals | Collected terms | Coefficient height |
|---|---:|---:|---:|---:|
| Balanced principal | 244 | 176 | 5212 | 3968 |
| Minimum selected dimension | 243 | 175 | 19517 | 7680 |
| Sparse | 250 | 182 | 4770 | 6709 |
| Dimension and height tradeoff | 246 | 178 | 21537 | 6144 |
| Lowest selected height | 247 | 179 | 10422 | 3840 |

The balanced principal improves the newest incoming common-remainder
252-variable, 182-row, 5340-term, height 128446 equation in all four measures.
Its complete 176 residuals are printed in the report. Two additional 247-variable
technical checkpoints are retained because they support exact comparisons
and the height-one source handoff.

| Coefficients only plus or minus one | Variables | Collected terms |
|---|---:|---:|
| Minimum selected dimension | 528 | 20816 |
| Compact | 534 | 18543 |
| Balanced | 580 | 12001 |
| Sparse | 620 | 8318 |
| Sparser | 717 | 7176 |

Every nonzero coefficient is exactly plus or minus one, with constant one.
The 534-variable point improves the previous 571-variable/19833-term compact
point in both measures. Four matched-source replays separately isolate the
new polarization improvement from the change of arithmetic source.

The scalar contribution is a theorem, not a new numerical endpoint: degree
300 is the exact minimum in the precisely specified inherited fixed-frame,
constant-weight, integer-center family. The unchanged attaining eleven-integer
300-degree, 148-operation equation is included with its authentic numerical
ports. The theorem is not a lower bound for arbitrary eleven-variable
Diophantine representations or different carriers and budgets.

## Main mechanisms

1. Normalize all eleven remainder certificates to one common denominator,
   retain the acyclic odd-square radix bootstrap, and use a single quadratic
   norm bound. Exact integral coordinate transformations and monic projections
   then expose further dispensable variables.
2. Polarize a prescribed square as a product of two aliases of the same
   logical value. A nonnegative quartic equality penalty replaces a
   three-coordinate cycle, eliminating its dummy while preserving all zeros.
3. Use a full highest-homogeneous-component argument to prove the scalar
   fixed-frame obstruction. A nonzero square in the degree 300 component
   prevents further center-only cancellation.

Actual coefficients, all selected literal equations, frozen certificates,
independent checkers and deterministic generators are supplied. There are no
unknown coefficient ports or variable-exponent operations in the final
polynomials. `ENDPOINTS.json` identifies the exact data, and `CLOSURE_MAP.md`
explains inherited proof and executable dependencies.

## Reproduce offline

Python 3.10 or later with its standard library suffices:

    python3 -B verify_release.py

The verifier authenticates the exact sealed inventory, makes a disposable
copy, and runs all 16 steps in `VERIFY_PLAN.json`. These include ordinary and
optimized-Python checks, source and historical-baseline bindings, every
expanded coefficient, deterministic reconstruction, deliberately corrupted
controls, the scalar theorem and literal-numeral checks, and byte-for-byte
regeneration of the printed principal equation. It verifies that the original
release was not modified. To save a new receipt outside the package:

    python3 -B verify_release.py --output ../new_verification.json

For file identity alone:

    python3 -B verify_release.py --integrity-only

To rebuild the PDF, use a working copy with ordinary TeX Live installed:

    sh report/build_report.sh

The build uses three passes and rejects overfull boxes and unresolved
references. Rebuilding generates auxiliary files and changes PDF metadata;
use a fresh extraction for strict inventory verification afterward.

## Scope and attribution

Comparison snapshot: ProveIt commit
`5d22cbf6bf2a344b6abe876e757b3fdc496d4adc`. Eight incoming archive identities
were authenticated, and 44 incoming direct polynomials were independently
recollected coefficient by coefficient. Relevant source files and licenses
are retained; full unrelated historical releases are not duplicated.

These are ordinary mathematical proofs of the stated ZFC equivalences,
not new end-to-end Lean/Rocq certificates, global-minimality claims or
literature-wide priority claims. Finite script success does not replace
the unbounded arithmetic arguments or the inherited logical calibration.
No upstream repository was changed by preparing this archive.
