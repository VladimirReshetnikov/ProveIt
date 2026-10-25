# Affine-exposure direct quartics, round 18

The new algebraic step finds three affine consequences hidden in a
quadratic residual basis, then projects their unit coordinates. It reduces
the incoming 282-coordinate direct quartic to 279 coordinates. Removing
one additional, already affine row yields 278 coordinates at a support
tradeoff. Matched sparse parents similarly reduce to 284 and 306.

| Directory | Integer variables | Rows | Degree | Monomials | Height |
|---|---:|---:|---:|---:|---:|
| integer278 | 278 | 188 | 4 | 12,884 | 12,227 |
| integer279_balanced | 279 | 189 | 4 | 5,483 | 7,200 |
| integer279_sparse | 279 | 189 | 4 | 5,202 | 12,662 |
| integer284_sparse | 284 | 194 | 4 | 4,270 | 10,864 |
| integer306_sparse | 306 | 216 | 4 | 3,870 | 14,512 |

All unknowns range independently over the unrestricted integers. Each
equation is the sum of squares of its complete residual list. `PROOF.md`
gives the ordinary universal proof; `report_section.tex` is the report
section. No global optimality, proof of consistency, worldwide priority,
or newly kernel-checked end-to-end theorem is claimed.

## Files and source boundary

- `sources/`: exact three incoming parents and the attributed upstream
  coordinate-shear certificates. They are authenticated by the endpoint
  manifest and `SOURCE_PROVENANCE.json`.
- `certificates/`: every coordinate shear, residual row operation and
  unit affine projection, in execution order. No optimizer is required.
- Each endpoint supplies `equation.json`, `expanded_polynomial.json`,
  `METRICS.json`, `RESTORATION.json`, `variables.tsv`, `residuals.txt` and
  an includable complete `residuals.tex`.
- `build.py`: deterministic finite-certificate builder.
- `check.py`: independent all-integer algebra/expansion checker, importing
  no producing or search code.
- `export_readable.py`: readable lists and affine maps, with both text
  and TeX parsed back to the full coefficient lists.
- `affine_rank.py`: optional exact modular rank obstruction. The final
  188 quadratic residual parts are linearly independent over Q, ruling
  out a further affine consequence in this particular row span only.

The named parent source archive is the incoming Cofinal Anchors/Height
One round-17 ZIP in ProveIt at the pinned snapshot. Its ordinary arithmetic
and C222/ZF/ZFC calibration closure remains inherited, not replaced by a
hash or finite computation. The enclosing round-18 delivery retains that
source archive/closure. The six coordinate preconditioning shears are
credited prior work. New claims concern the exposed identities, their
projections, frozen residual-basis certificates and their exact endpoint
composition. Upstream V-R1 semantic acceptance is not assumed.

## Offline reproduction

Python 3.10 or newer, standard library only. Paths are independent of the
current working directory; replace `/path/to/quartic` as needed.

```sh
python -B /path/to/quartic/check.py --rebuild
python -O -B /path/to/quartic/check.py --rebuild
python -B /path/to/quartic/export_readable.py --check
python -O -B /path/to/quartic/export_readable.py --check
python -B /path/to/quartic/affine_rank.py
```

The checker verifies every coordinate inverse, row inverse, unit projection,
identically zero deleted row, absent deleted coordinate, renumbering and
liveness, the full published original-coordinate restoration maps, every
original-row pullback identity, every quartic coefficient and each metric.
Five altered-artifact controls must be rejected. `--rebuild` constructs all
three mathematical files afresh in a temporary directory and requires
byte equality, without writing into the release. Normal and optimized
receipts are included.

To build the three mathematical files into a new directory, use

```sh
python -B /path/to/quartic/build.py --output /new/directory
```

This last command deliberately does not copy the source/certificate/proof
closure. Verification normally runs against the delivered component,
where the readable exports and restoration maps are also present.

The bounded exploratory search was stopped after selecting the frozen
Pareto tradeoffs; its optimality is not asserted and its execution is not
a reproduction dependency. Finite checks are not consistency tests.
