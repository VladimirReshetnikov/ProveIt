# Experimental upstream adapter

The adapter uses `fastunknot.scan.ScanComplex`, NOT the separate optimized
`FastScan` implementation. It was prepared from inspected source interfaces but
was not executed against a full upstream checkout in this environment.

## Load paths

Put both this archive root and ProveIt's `Topology/UnknotRecognition/fast`
directory on PYTHONPATH. For example, on a POSIX shell:

```bash
export PYTHONPATH="$PWD:/path/to/ProveIt/Topology/UnknotRecognition/fast"
python - <<'PY'
from fastunknot.diagram import Diagram
from integration.upstream_adapter import window_probe
print(window_probe(Diagram.from_braid(3, [1,2]*4), depth=2, seconds=10))
PY
```

On Windows, use semicolons rather than colons in PYTHONPATH.

## Mandatory acceptance gates

1. Run all current upstream Python tests unchanged, then with an opt-in window
   stage enabled. Run its existing Python/Rust cross-checks as well.
2. Compare the adapter with the bundled independent cube oracle on at least the
   explicit `results/validation.json` corpus. Normalize signs through the
   upstream PD `signs()` routine.
3. Preserve all preexisting validation, simplification, and factorization.
   Test unsimplified and simplified diagrams, mirrors, and factors.
4. Force both time and object caps. They must return `UNKNOWN` and fall through
   to the old exact backend, never produce `UNKNOT` from incomplete agreement.
5. Check retained matching multiplicities for several pivot policies and verify
   every asserted binomial stage bound whenever the geometric certificate says
   `nice=True`.
6. Benchmark actual fallback survivors, with the feature both off and on. Do not
   use the backend-only speed ratios as end-to-end production measurements.

## Assumed mutable interface

The controller reads `objects[id] == (matching, unshifted_degree)`, `out`, `inc`,
`stats`, `points`, and `algebra.stats`; calls `add_crossing(slots, reduce_now=True)`,
`_set(source,target,value)`, and `linear_ranks()`; and deletes all adjacency
references when it discards an object. Reaudit this contract after upstream
changes. `SOURCES.json` records the inspected file blobs.

`ScanLimit` belongs to the upstream package, not the reference implementation;
the adapter passes the correct exception class explicitly. Errors such as an
overlapping-window rank disagreement are not swallowed as ordinary limits.

Keep the adapter opt-in until these gates pass. There is no Rust port, Lean
formalization, or direct FastScan adapter in this archive.
