# Integration plan: do not replace the current default

## Intended seam

The inspected standard scanner supports:

```python
completed = scan.eliminate(update_budget=allowance)
```

If it pauses, its remaining arrays describe a valid, partly reduced complex.
Preserve them. The existing production adaptive path already attempts scalar
profile and degree-gap shortcuts. The proposed full-transfer path belongs after
those cheap cases decline, not before all sparse work and not as a replacement
for the existing shortcut.

At that seam:

1. Check the common-disk certificate on the **actual processed PD prefix**, and
   bind it to the input/order metadata. The full diagram must already be validated
   as a connected plane diagram. Check that its frontier equals `scan.points`.
2. Compact the live complex with `snapshot(scan)`. Compute its binary contraction,
   then run `reduce_complex(..., cyclic_order=certificate.cyclic_order)`. The
   routine checks all distinct matching types against that order and preserves
   off-diagonal undotted maps.
3. Install new `mid`, `deg`, `out`, `inc`, and `live` together only after success.
   Update counters and invalidate the old composition-result cache. If geometry
   declines, continue ordinary cancellation on the same pre-transfer state.

`src/radical_scan.py` implements this discipline as a separately tested prototype.
Its local allowance `max(256, 4*live)` is an experimental control. It is not asserted
to outperform the production adaptive policy or to be constant-factor competitive.

## Keep this as a separate research package initially

A suitable repository destination is a new research subdirectory under
`Topology/UnknotRecognition/`, not overwriting `fast/fastunknot`. To test against a
complete checkout, place this package's `src` and the checkout's `fast` directory on
`PYTHONPATH`, with the checkout preferred over `reference_upstream`. The experiment
helper currently prepends the fixture deliberately, so an upstream trial must
explicitly change that import-selection line and record the checkout commit.

Run the pinned-source audit first, then the package tests, then the entire upstream
suite and cross-checks. Keep the fixture and upstream measurements distinguishable.
No upstream integration run was performed in the supplied results.

## Metadata and API obligations

- Only the ordinary list-based `FastScan` arrays are covered. Component ownership,
  shared templates, weights, rank caps, grading shifts beyond raw homological
  degree, and Rust representations require separate adapters.
- `update_budget` means candidate Schur update pairs. Do not conflate it with a
  clock budget, coefficient-composition count, or radical-series factor limit.
- Keep the complete frontier size. Four local crossing slots do not imply a
  four-point global frontier or a nilpotence exponent independent of width.
- Never silently discard positive maps after residue prediction. They can become
  scalar maps after closure/delooping.
- A nonempty source-derived prefix certificate alone is not validation of the full
  classical input. The supplied driver validates closure, connected plane geometry,
  and (for a recognition verdict) one-component strand structure.
- Budget failures, invalid geometry, and algebraic failures remain distinct. An
  exhausted budget must not become `KNOTTED`, `UNKNOT`, or a zero homology result.

## Acceptance criteria before changing production defaults

Require source-equivalence audit, complete-checkout correctness regression, paired
whole-pipeline timings including prefilters and order search, and measurements on
representative difficult knots and certified unknots. Report adverse cases and
counts of actual full-transfer calls. In this release's seven diagram timing cases,
that adaptive count is zero; timing noise there cannot justify a default change.

The supplied grid generator gives structurally certified unknots through arbitrary
sizes, but those inputs are not automatically difficult for a recognizer with a
descending-diagram or other structural prefilter. They isolate a width theorem,
not a universal hard-instance theorem.
