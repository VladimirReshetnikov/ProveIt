# Opt-in integration contract

## What was delivered

`adapter.py` takes a validated source braid and a callback:

```python
from integration.adapter import recognize_with_backend

result = recognize_with_backend(
    strands, word,
    decide=my_safe_factor_backend,
    seconds=remaining_global_budget,
    descend=True,
)
```

The callback signature is `decide(factor: Braid, seconds: float | None) -> dict`.
Its status must be `UNKNOT`, `KNOTTED`, or `UNKNOWN`. The adapter checks this
contract, memoizes literally equal factors, and accepts only if every factor
is established trivial. It does not certify arbitrary callback claims.
Unexpected callback exceptions propagate rather than being converted into a
false verdict; wrap the host's specific resource-limit exceptions as UNKNOWN.

The callback must **not recursively re-enter the same kernel stage on an
unchanged factor**. Use a direct exact-backend entry point or a stage-disable
flag. If a decomposition has just one unchanged factor, unrestricted recursion
would never make progress.

This adapter has five controlled unit tests. It was not run against an installed
production `fastunknot`, and no production default was changed.

## Suggested placement

Keep input validation and the source-braid/diagram binding first. An immediate
Bennequin violation can still reject before any data structures are built.
The existing exact at-most-three-braid branch should remain available and can
avoid the tiny-input overhead observed here. On larger unresolved source
braids, an opt-in linear descent can expose a small-strand decision or more
singleton cuts. The all-cut kernel then passes its **new factor braids**, not
the original whole source, to the chosen backend.

A planar diagram and a cached braid with the same number of crossings are not
thereby proven equivalent. Preserve the loader's existing source-binding
checks. If descent precedes cutting, first replay descent on the original
braid, then replay the cut certificate on the resulting braid.

## Certificate compatibility

The new schemas are:

- `linear-endpoint-descent-v1`: local original-position moves and final order;
- `artin-singleton-cuts-v1`: all singleton cut indices and projected factors.

The old `singleton-markov-descent-v1` schema is not overwritten or reinterpreted.
Dispatch its verifier separately. Converting the new trace into a sequence of
full intermediate old words can reintroduce quadratic cost; retain the local
representation instead.

The standalone `Braid.checked` API intentionally rejects multi-component
closures. The old low-level helper may have accepted some links. Therefore a
blind drop-in replacement of that public helper changes its domain and is not
recommended without a deliberate compatibility decision.

## Budget semantics

One remaining global budget is passed to factor calls. A timed-out factor is
never assumed trivial. A later conclusive knotted factor can still reject in a
policy that continues after a local cap. The adapter returns UNKNOWN once its
remaining global time is exhausted. The current implementation has cooperative
checks around backend calls, not hard wall-time interruption of preprocessing
or individual bit operations. Add the host's budget callback to long loops
before promising the host's normal interruption granularity.

## Required production validation

Run the complete maintained suite, independently replay all new certificates,
and check the final status against the unmodified recognizer on the same valid
inputs. Preserve the old path as an A/A control. Use paired full-pipeline timings
with the same parsing, source construction, filters, deadline, and worker policy.
Include stabilized words, no-cut cores, internal-cut examples, inputs settled
before this stage, knotted connected sums, and exhausted budgets. The saved
stage-only and raw-cube experiments do not substitute for these measurements.
