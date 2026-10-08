# Run-encoded twist continuation frontend

This is an additive research interface. The existing `fastunknot` and
`fastunknot.twist` commands keep their established defaults.

Run from the `fast` directory using Python 3.10 or later:

```sh
python -m fastunknot.twist.continuation input.json
python -m fastunknot.twist.continuation input.json --mode homology --method tail --check-d2
python -m fastunknot.twist.continuation input.json --mode homology --method streaming
python -m fastunknot.twist.continuation input.json --mode profile
```

The input is a JSON object with integer strand count and signed run pairs:

```json
{"strands": 3, "runs": [[1, 1001], [2, -1], [1, 1], [2, -1]]}
```

Generator indices are unsigned, one-based, and less than the strand count.
Exponents are nonzero signed integers. An optional outer `braid` object is
accepted. `-` as the input filename reads standard input. This command accepts
run-encoded braids; it does not convert PD codes, grids, or words.

## Modes and defaults

The default is `--mode recognize --method tail`.

| Mode | Behavior |
|---|---|
| `recognize` | Check that the original closure has one component. Apply the established Seifert/Rasmussen structural certificate directly to the run counts. If it is inconclusive, use the selected exact backend. |
| `homology` | Compute the full reduced homological profile using the selected backend, even when a cheaper structural certificate would already decide whether the input knot is trivial. Links are supported. |
| `profile` | Return only the original one-component braid's structural certificate. `INCONCLUSIVE` means the criterion did not decide the knot. |

The available methods are:

| Method | Exact calculation |
|---|---|
| `tail` | For a selected run longer than its context, compute a finite reference complex and apply the proved exact degree recurrence. Otherwise use the ordinary macro backend. The largest run is selected by default; `--run-index j` selects a zero-based index explicitly. |
| `streaming` | Enumerate successive degree layers and send columns directly into exact elimination. Homology mode computes all degrees. Recognition may stop once finalized homology dimensions already sum to more than one; such an output explicitly reports a lower bound and `homology_complete: false`. |
| `macro` | Assemble the original twist macro complex and compute its full homology. |

The tail result stores its exact profile as a `points` dictionary and at most
one constant interval. Both `start` and `end` are **inclusive**. The points and
interval are disjoint. Quantum grading is forgotten throughout. The degrees
use the existing twist macro convention.

A shortened reference may be a link even when the original braid is a knot.
Recognition always uses the original exponent parity and component count.
`--check-d2` in tail mode checks the finite reference complex; the returned
scope says so explicitly.

## Resource ceilings and exit codes

Common default ceilings are 250,000 macro states, 1,000,000 total basis elements,
and 20,000,000 rank/check XORs. Tail applies these algebraic ceilings to its
finite reference calculation. `--seconds` is an optional cooperative deadline
that includes structural checking and the chosen backend.

`--max-matrix-bits` defaults to 1,000,000,000 and applies to the assembled matrix
envelope of tail/macro. The streaming method has its own live-storage options:

| Flag | Default |
|---|---:|
| `--max-live-matrix-bits` | 1,000,000,000 |
| `--max-live-states` | 250,000 |
| `--max-layer-basis` | 1,000,000 |
| `--max-live-columns` | 2,000,000 |

The streaming Python API exposes its additional geometry and map-cache caps.
These are mathematical storage envelopes, not process RSS guarantees. Exhaustion
returns `UNKNOWN`; it is never interpreted as a knot verdict. Structural
certificates may settle recognition without allocating a macro complex, even
when the algebraic state or basis ceiling is zero.

Exit status is 0 for a completed calculation or profile, 2 for invalid input or
configuration, and 3 for `UNKNOWN`. JSON input and output obey Python's decimal
integer digit limit. The direct Python APIs can accept much larger integers;
their optional output-expansion cap prevents accidental enumeration of a long
homology interval.

## Python API

```python
from fastunknot.twist.continuation import compute
from fastunknot.twist.core import Budget, Run
from fastunknot.twist.streaming import StreamBudget
from fastunknot.twist.tail import profile_dimension, expand_profile

runs = [Run(1, 10**100 + 1)]
answer = compute(2, runs, mode="homology", method="tail", budget=Budget())
profile = answer["homology"]["degree_profile"]
assert profile_dimension(profile, 0) == 1
# expand_profile(profile, max_terms=1000) would raise ResourceLimit.

streamed = compute(2, [Run(1, 3)], mode="homology", method="streaming",
                   budget=StreamBudget(), check_d2=True)
```

Use the in-memory Python profile for `profile_dimension` and `expand_profile`.
As with ordinary degree dictionaries, JSON serialization converts integer
dictionary keys to strings; convert `points` keys back to integers after a JSON
round trip before using those Python helpers.

Run `python -m unittest discover -s tests -p 'test_twist_tail.py' -v` and
`python -m unittest discover -s tests -p 'test_twist_continuation.py' -v` from
`fast` for the recurrence and frontend suites. The portable audit and benchmark
scripts are `tools/audit_slope.py` and `tools/benchmark_tail.py` at package root.
They write their raw results under `results/`, replacing the corresponding files.
