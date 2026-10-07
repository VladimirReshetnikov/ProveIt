# Opt-in integration (no production files changed)

The package is a research overlay, not a replacement recognizer. The completed
validation is against a numerical source-excerpt harness. The full Python suite,
Rust port, process races, and full recognition pipeline were **not executed** here.

Suggested repository location for this entire package:
`Topology/UnknotRecognition/research/component-entropy-20261007/`.

First validate against the actual checkout without modifying it:

```sh
python integration/check_repository.py \
  --fast-root /path/to/ProveIt/Topology/UnknotRecognition/fast \
  --scan-examples --output results/local_integration.json
```

This command has not been run here. It records source hashes, checks the algebra,
and optionally compares direct closed-PD scans with a check of d-squared after
each crossing. These scans compare unreduced dimensions, not recognition verdicts.
Resource-limited examples are reported as budget exhaustion. Non-PD example files
and the crossing-free special case are skipped. The ordinary repository unit suite
must also be run before adoption. A hash mismatch calls for a fresh interface audit;
it is reported rather than silently treated as the audited revision.

For application code, import the kernel module from this package and wrap a **new,
not-yet-used** scanner:

```python
from fastunknot.scan_fast import FastScan
from component_kernel import ComponentAlgebra

scanner = FastScan(max_objects=20000)
scanner.algebra = ComponentAlgebra(
    scanner.algebra,
    max_entries=1 << 18,
    min_pairs=256,
    check=scanner._check,
)
# Now use scanner.add_crossing(...) as usual.
```

The two modules must be importable (for example, add this package's `code/` to
`PYTHONPATH`). A production patch can copy `code/component_kernel.py` into
`fast/fastunknot/` and use a relative import. Do not change default constructor or
CLI behavior until the complete cross-check and paired scanner benchmarks pass.
There is deliberately no automatic patch or global monkey-patch.

The adapter delegates geometry, circle numbering, transfer, and shape/result
caches to the existing `Planar`. It only replaces sufficiently dense composition
calls. Each scanner owns its adapter and stage cache; clear occurs at stage entry.
The current policy is a heuristic, not a wall-time guarantee. Existing result
cache hits and identity shortcuts remain outside this kernel. A dense-allocation
limit falls back to the existing exact composition, never to a knot verdict.
The check callback propagates the scanner's deadline/race exception. Cache keys
are not transferable between scanners or different circle-numbering conventions.

Before default enablement, collect per-case compressed call counts, cache hits,
plan compilation time, peak RSS, total recognition time, and paired A/A controls.
Include hard unknots, trivial-Alexander knots, connected sums, long braids, and
random closures. Cases with zero compressed calls are informative, not failures.
An entry-count cap is not a byte cap; measure Python allocation overhead.

The dense-domain ceiling is **per plan**, not a whole-scanner or RSS limit.
Several cached plans and the original geometry/result caches can coexist.
A separate aggregate cache or process-memory policy is required for a hard
whole-process memory limit.
