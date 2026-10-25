# Wider budgets and contracted incidence equations for ZFC consistency

Research iteration 20 for Vladimir Reshetnikov and ProveIt, 25 October 2026.
Start with the PDF in `report/`; its editable native TeX sources are adjacent.

## Results

All selected coordinates range over unrestricted integers. In ordinary ZFC,
each equation has a zero exactly when there is a finite syntactic ZFC
refutation. Negating gives the requested equivalence of unsolvability with
Con(ZFC), without asserting or proving consistency.

| Direct quartic | Variables | Quadratic residuals | Collected terms | Height |
|---|---:|---:|---:|---:|
| Balanced principal | 238 | 175 | 5236 | 3968 |
| Dimension tradeoff | 237 | 174 | 18569 | 7680 |
| Factorial-free power branch | 239 | 175 | 5137 | 3968 |

The principal improves the incoming Shared Factorial Error 240-variable
point in all four measures. Compared with the prior Round19 principal, it
removes six variables but adds 24 terms at unchanged height. The 239-variable
alternative removes five variables and 75 terms at unchanged height. Every
coefficient is supplied, and all 175 principal residuals are printed in the
report. Technical 241- and 242-variable systems are retained as height-one
source checkpoints, not additional claimed frontier points.

| Quartic with coefficients only plus or minus one | Variables | Terms |
|---|---:|---:|
| Minimum selected dimension | 503 | 24193 |
| Compact | 505 | 20491 |
| Balanced compact | 512 | 18255 |
| Balanced sparse | 557 | 11999 |
| Sparse | 617 | 8318 |
| Sparser | 713 | 7176 |

Every nonzero coefficient is exactly plus or minus one, with constant one
and exact total degree four. The 505-variable equation improves the old
528-variable/20816-term point in both measures; 512/18255 improves the old
534/18543 point. Five fixed-source comparisons separately isolate the new
structural operations from changing the source arithmetic polynomial.

Two eleven-integer alternatives have degree/operation pairs **298/147** and
**300/145**. The first saves three operations over the incoming rebased
298/150 equation and improves both degree and cost over Round19's 300/148
point. The second saves three operations at unchanged degree in the old
frame. A new restricted minimum theorem shows degree 298 is exact in the
specified rebased fixed-frame, constant-weight, integer-center family. It
does not contradict the prior degree-300 minimum for the different old frame
and is not a global lower bound for eleven-variable Diophantine equations.

## New mechanisms and proof boundaries

- A wider common norm shares factorial error and low-digit errors. Its signed
  bootstrap rules out zero and unit radix cases before interpreting the
  recovered digits; negative-radix branches are treated explicitly.
- The factorial-free branch uses F=t^t at an even cofinal horizon. Equality of
  factor counts and positivity of all coefficients at that common degree
  permit exact product recovery at this smaller evaluation base.
- Replacing an equality dummy d by a product a*u with an already anchored
  unit alias preserves a nonnegative quartic penalty. Internal tree-edge
  contraction removes further flow coordinates, with an exact inverse.
- New polynomial centers differ from the inherited centers by explicit
  integral shears. Exact complete homogeneous-component calculations certify
  degree, and the native handoff retains the required sign/divisibility order.

The final equations contain no variable exponent, floor, factorial primitive,
uncomputed coefficient port or unspecified universal predicate. Mathematical
semantic notation is confined to the ordinary proofs. `CLOSURE_MAP.md`
explains retained source proofs, authentic numerical payloads and code paths.

## Reproduce offline

Python 3.10 or later and its standard library suffice:

    python3 -B verify_release.py

This authenticates the exact sealed inventory, copies it to a disposable
directory, and runs all 17 steps in `VERIFY_PLAN.json`. Optimized steps also
set PYTHONOPTIMIZE=1 so subprocesses inherit that mode. Checks include every
coefficient, exact source transformations and bindings, deterministic
reconstruction, literal text parsing, corruption controls, the scalar
numeral recipes and degree proofs, and the printed principal equation.
The original archive/extraction is not modified by this command.

To save a receipt outside the package:

    python3 -B verify_release.py --output ../new_verification.json

For file identity alone:

    python3 -B verify_release.py --integrity-only

Rebuild the PDF in a working copy with an ordinary TeX Live installation:

    sh report/build_report.sh

Use a fresh extraction for strict inventory verification after generating
TeX auxiliary files or replacing a PDF. Different TeX metadata need not give
the same PDF bytes even when the mathematical pages are identical.

## Scope

The comparison snapshot and archive identities are in `provenance/`.
Ordinary unbounded mathematical proofs compose with the named inherited
arithmetic and refutation calibrations. Finite tests authenticate actual
artifacts; they do not replace those proofs. No new end-to-end Lean/Rocq
certificate, global minimality or worldwide novelty claim is made.
