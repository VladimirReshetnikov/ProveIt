# ProveIt integration notes

Suggested placement: a new research contribution beneath `Topology/UnknotRecognition/`, with this directory retained intact for reproducibility. No changes to the main production defaults are recommended from these measurements alone.

## Local checkout mode

```sh
export PROVEIT_FAST=/path/to/ProveIt/Topology/UnknotRecognition/fast
python integration/check_upstream_ast.py "$PROVEIT_FAST"
export PYTHONPATH="$PWD/src:$PROVEIT_FAST"
python -m unittest discover -s tests -v
python experiments/verify_examples.py --external
python -m closure_reset examples/figure_eight.json --check-d2
```

The AST audit checks the retained fixture against the local core source. The expected blob pins are recorded in `provenance/sources.json`. This audit was not executed against an upstream checkout in the current runtime.

Then run the checkout's complete maintained test suite and its own paired raw and end-to-end comparisons. The delivered audit/benchmark scripts intentionally select the bundled reference fixture for reproducibility; use an explicitly adapted copy for checkout benchmarking and record that change.

## Interfaces

`closure_reset.driver.recognize_pd(pd, *, max_objects=None, seconds=None, check_d_squared=False, reset=True, frontier_test=True)` returns a verdict, rank cap, trace events, and statistics. The current order is the PD input order. `frontier_test=False, reset=False` provides the comparison full-scan arm.

`jet.certify_jet(scan, group)` requires a valid exact chain complex and a whole direct-sum group. It rejects units, mixed matchings, empty matchings and external attachments. It does NOT itself establish Q^2=0; the driver inherits validity from the exact scanner. Its rank formula requires the matching completed by the actual suffix to be a knot. The driver reconstructs and checks that premise.

`jet.first_jet_survivors(A,B)` implements the general scalar-homology formula and verifies A^2=0 and AB+BA=0. A matrix-only call is not a knot certificate and cannot infer omitted homological degrees.

`pure.certify` supplies stronger closure-uniform bounds for common-coefficient blocks. Their all-classical-closure applicability is not extended to arbitrary mixed-coefficient blocks with multicomponent completions.

## Safety boundaries

Only total rank/capped recognition survives resets. Do not feed reset degree counts into the exact homology/window APIs. Do not reduce integer multiplicities modulo two. Do not infer an unknot from an inconclusive checkpoint. Resource exhaustion is UNKNOWN. Preserve the geometric realization of every matching; checking an arbitrary pairing's labels is not enough.

The replay routine repeats the exact scan with d-squared checking and compares JSON event data. It is not independent of the scanner and is not a formal proof assistant certificate.

The production Fitting splitter can potentially expose more eligible blocks, but this package does not call it or assume it succeeds. Any such extension needs whole-block verification, cost accounting, API tests, and new paired timings.
