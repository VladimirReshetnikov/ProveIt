# ProveIt integration notes

## Pinned interface inspected

Repository: `VladimirReshetnikov/ProveIt`
Commit: `0090314cfcc21e1f28ecbc6e8ce4d3f2d99ee743`
Existing API: `fastunknot.braid.braid_certificate(strands, word, *,
backend="free-product", use_braid_reduction=True, check=None)`.
The root README and `braid.py`, `braid_reduction.py`, and `__init__.py` were
inspected. This package does not assume that later API versions are identical.

## Suggested placement

Preserve this research bundle initially in a new directory such as
`Topology/UnknotRecognition/research/ranktwo_kernels_20261007/`.
The Python `ranktwo` package can remain separate during evaluation. An
integration can instead relocate its modules under `fastunknot` after adjusting
relative imports and keeping the verifier independent of the optimizer.
Do not overwrite the existing `braid.py`: it solves a different problem.

For explicit braid inputs, retain already decisive cheap gateway results.
On an inconclusive result, run one deterministic AVL pass under the existing
resource budget, replay its certificate, and retry the existing braid gateway.
Then feed the reduced word to the existing diagram conversion and exact
fallback. `integration/fastunknot_adapter.py` implements only this gateway
wrapper and returns `reduced_input` rather than guessing a PD-constructor API.

Keep the original input and the reduction transcript in the returned evidence.
Exact B_s equality preserves both closure and endpoint data. It is not safe to
substitute a cyclic-normal-form or closed-knot equivalence test for the local
checker. Preserve the exponent/central-lift guard.

## Run the real upstream smoke test

This test was supplied but **not executed** during artifact creation:

```sh
PYTHONPATH="$PWD/src:/absolute/path/to/ProveIt/Topology/UnknotRecognition/fast" \
  python integration/upstream_check.py
```

It predicts 16 sleeves for which the inspected raw gateway is inconclusive
before shortening and decisive afterwards. This is narrower than a claim
about the performance of the complete recognizer.

## Required before enabling by default

Run the real smoke test and the complete upstream suite. Compare original and
reduced-input verdicts and exact homology ranks on the existing examples.
Measure paired end-to-end timings with the pass disabled/enabled, including
barrier words and inputs on which no shortening occurs. Record preprocessing
time, output crossing count, peak memory, fallback choice, limits, and result.
Audit certificate association after every later reduction. Check all budget
exceptions at the pipeline boundary. A timeout is not a knot verdict.

The current adapter contract tests inject a fake gateway. They test call order,
replay, preservation of existing decisions, and exception propagation, but not
upstream compatibility. The full pipeline and Rust port were not run here.

## Asymptotic labels

Use `O(n log(n+2))` word-RAM for the deterministic one-pass primitive,
`O(n log²(n+s+2))` for its conservative bit bound, and `O(n)` word-RAM for
certificate replay. A hash backend must retain the expected-time qualification.
Repeated saturation has a conservative quadratic bound.
Only the explicitly defined small-core input class has the proved
quasi-polynomial recognition bound. The general pipeline remains exponential
in the worst case under the supplied proof.
