# Integration and provenance notes

This continuation adds one compressed-string optimization to the existing
recognition path and two independently callable geometric certificate APIs.
The new geometric APIs do not supply a diagram-level knot verdict.

## Exact baseline

The repository checkout is commit
`1be2abc8cc743c1a3b5cb7fdfeb650697f8e2d5b`. The last relevant subtree baseline
used for the endpoint comparison is
`38e65c9c2e2bfd42b9f71f1a1a7af15a3f8a3005`.
Their `Topology/UnknotRecognition/fast` trees are identical, with tree object
`e7222244bb0d7f35cf7f34f83228b350240e4d13`.

The archived `fast/endpoint_research/baseline_compressed_lcs.py` was checked
byte-for-byte against the original `fastunknot/compressed_lcs.py` at that
baseline commit. Its SHA-256 is
`90d27e3aee4d51fe0d526495dc9cbe316ab7dac280dae120060d480c5f278191`.
The paired endpoint benchmark substitutes this one archived module while
sharing the current word arena and replay code. It is not a comparison
between two complete historical repository checkouts.

All paths below are relative to `Topology/UnknotRecognition`.

## Modified existing files

| File | Change |
|---|---|
| `fast/fastunknot/compressed_lcs.py` | Calls the endpoint arithmetic-progression shortcut after the existing periodic and sparse shortcuts. The integration hook is active only for operands of at least 128 letters. |
| `fast/tests/test_lcs_periodic.py` | Keeps intentional general-fallback tests meaningful by disabling the new shortcut in those tests. |
| `fast/tests/test_lcs_sparse.py` | Makes the same adjustment for intentional sparse-fallback cases. |
| `fast/fastunknot/normal_surface.py` | Corrects the existing optional worker's subprocess communication after Python 3.12.14 exposed loss of pending stdin writes on timeout retries. One communication thread owns all pipe I/O; foreground cancellation and deadline checks retain bounded polling. |
| `fast/tests/test_normal_surface.py` | Retains the original 500,000-byte regression unchanged and adds full-duplex traffic and cancellation while stdin is blocked. |

The two geometric APIs do not change the recognition-stage order, package
export list, or command-line verdict options. The separate subprocess
compatibility correction below repairs the existing optional engine wrapper.

## New implementation and research files

| Component | New files |
|---|---|
| Endpoint shortcut | `fast/fastunknot/compressed_endpoint.py`; `fast/tests/test_compressed_endpoint.py` |
| Endpoint reproduction | `fast/benchmark_compressed_endpoint.py`; `fast/benchmark_endpoint_lcp_ablation.py`; `fast/endpoint_research/baseline_compressed_lcs.py`; `fast/endpoint_research/lcp_endpoint_variant.py`; `fast/endpoint_research/benchmark_lcp_original.py`; `fast/endpoint_research/endpoint_lemmas.tex` |
| Normal-disc certificate | `fast/fastunknot/normal_disk_certificate.py`; `fast/tests/test_normal_disk_certificate.py` |
| Normal-disc reproduction | `fast/certificate_research/fixtures.py`; `fast/certificate_research/benchmark.py`; `fast/certificate_research/results/layered_torus_*.json`; `fast/certificate_research/results/normal_disk_benchmark.json` |
| Cover assembly API | `fast/fastunknot/regular_cover_gluing.py`; `fast/tests/test_regular_cover_gluing.py` |
| Cover reproduction and proofs | `fast/regular_cover_research/README.md`; `fast/regular_cover_research/oracle.py`; `fast/regular_cover_research/reproduce.py`; `fast/regular_cover_research/theorem_notes.tex` |
| Recorded comparison results | `fast/results/endpoint_ap_20261008.json`; `fast/results/endpoint_ap_lcp_ablation_20261008.json`; `fast/results/regular_cover_gluing_20261008.json` |
| Article package | `research/20261008_compressed_certificates/article/` and this note; the final package manifest records the compiled article and other delivery files. |

## API boundaries checked during integration

**Endpoint overlaps.** Import from `fastunknot.compressed_endpoint`.
`occurrence_summary(arena, root, pattern)` computes the exact occurrence
summary. `endpoint_overlaps(arena, x, y)` returns a complete list of overlap
progressions when its structural certificate succeeds. An empty list is a
completed empty answer; `None` means that this shortcut did not establish
its structural certificate and the existing complete matcher remains in
use. Arena resource exceptions propagate. This hook can affect the existing
compressed group-certificate path when that path reaches LCS; it creates no
new topological verdict.

**Normal discs.** Import from `fastunknot.normal_disk_certificate`.
`normal_disk_certificate(triangulation, coordinates)` certifies a supplied
surface; it does not search for one. `audit_normal_disk_certificate` returns
relative evidence with status `CERTIFIED_COMPRESSING_DISK`, while
`verify_normal_disk_certificate` provides the Boolean wrapper.
The checker reconstructs the finite manifold data from face pairings and
checks the vector, rank, Euler characteristic and essential boundary.
Coordinates are rows
`[T0,T1,T2,T3,Q01|23,Q02|13,Q03|12]` of actual Python integers; Boolean
coordinates are rejected. This API does not certify a correspondence
between the supplied triangulation and a knot diagram. A compressing-disc
certificate for an arbitrary supplied torus-boundary manifold is therefore
not promoted to `UNKNOT` or a solid-torus assertion.

**Cover assemblies.** Import from `fastunknot.regular_cover_gluing`.
`RegularCoverAssembly` validates an immutable prepared model.
`compare_assemblies` and `verify_certificate` concern complete families of
isomorphisms over the same labelled base. `transport_witness` evaluates a
chosen family member; `verify_transport` checks its original gluing and
marking equations. `canonicalize_assembly` returns an unmarked key and a
transport to canonical phases. Its key does not preserve additional named
points or boundary lifts. Local block covers must be connected and regular,
with the regular `2m`-point action for `D_m`, and attachments must glue full
boundary preimages by coherent right-group phases. Natural nonregular
dihedral actions and arbitrary per-lift attachments are outside the API.
Signed hexadecimal strings are accepted for this module's integer inputs;
its wire schema is distinct from the normal-disc schema.

Read-only import inspection confirms that neither geometric module is
imported by the current verdict pipeline or by the top-level public export
list. Both geometric implementations use the standard library. Regina is
used only by the optional independent normal-disc benchmark/oracle arm.

## Existing worker compatibility correction

The integration run reproduced
`test_communication_retains_input_across_polls` failing in 3.002 s under
Python 3.12.14. The subprocess retained unsent input after
`TimeoutExpired`, but its selector registered stdin on the next call only
when that call supplied a truthy `input` argument. Retrying
`communicate(None)` therefore stopped sending the pending bytes; passing
the original payload again is prohibited once communication has started.
The original 500,000-byte delayed-reader test was not weakened.

The wrapper now calls the public `Popen.communicate(payload)` API once in
a dedicated I/O thread. The calling thread polls an event at intervals of
at most 50 ms, runs the caller's cancellation callback, and checks the same
absolute deadline before and after communication. On success, failure, or
cooperative cancellation it kills the child if still running, reaps it,
joins the I/O thread, and closes all three pipes. Caller exceptions,
including `TimeoutError`, propagate unchanged; launch and pipe `OSError`
failures keep the existing `NormalWorkerError` behavior. This uses no
private stdlib attributes or platform-specific process API.

Focused validation passed four tests in 0.584 s: the unchanged delayed
reader, the existing local/global cancellation case, simultaneous large
stdout/stderr traffic with pending input, and local/global cancellation of
a child that never reads its 500,000-byte stdin payload. The cancellation
tests verify that children are reaped and all pipes are closed. This is a
worker reliability correction, not an algorithmic speedup measurement.
The complete `tests.test_normal_surface` module then ran 10 tests in
0.620 s: seven passed and three optional Regina tests skipped because that
dependency was absent. The full project suite is recorded separately.

## Reproduction commands

Run these commands from `Topology/UnknotRecognition/fast`:

```bash
python -m unittest tests.test_compressed_endpoint -v
python -m unittest tests.test_normal_disk_certificate -v
python -m unittest tests.test_regular_cover_gluing -v
python -m unittest tests.test_normal_surface -v

python benchmark_compressed_endpoint.py \
  --output results/endpoint_ap_20261008.json
python benchmark_endpoint_lcp_ablation.py \
  --output results/endpoint_ap_lcp_ablation_20261008.json

python -m certificate_research.benchmark \
  --output certificate_research/results
python -m certificate_research.benchmark \
  --output certificate_research/results --native

python regular_cover_research/reproduce.py \
  --output results/regular_cover_gluing_20261008.json
```

The two normal-disc benchmark commands are alternatives: the second adds
Regina cross-checks and explicitly limited native subprocesses. It requires
the project's optional `normal` dependency; the standard-library benchmark
does not. Optional native unit tests skip when Regina is absent. Endpoint
benchmarks retain resource-limit statuses as incomplete outcomes. Native
normal-disc measurements retain timeouts and resource failures without
treating them as completed speedup denominators.

The LCP ablation JSON retains a `source_archive_map` that resolves its
original module and harness digests to the corresponding archival files.
Use `benchmark_endpoint_lcp_ablation.py` for reproduction: the archived
`benchmark_lcp_original.py` preserves its historical location assumptions
and is retained for provenance.

## Practical review points

1. Preserve the distinction between a completed empty endpoint answer,
   structural shortcut failure, and a resource exception.
2. Retain independent replay for any group certificate produced through
   the accelerated string path; an internal query timing is not an
   end-to-end knot-recognition complexity bound.
3. Before using the normal-disc API for a diagram verdict, add checked
   diagram-to-finite-exterior correspondence and the relevant topological
   inference. The present API intentionally stops at relative evidence.
4. Before using cover keys in hierarchy memoization, verify the extracted
   regular actions, peripheral framings, coherent full-preimage attachments,
   and retention of all external markings needed by later operations.
5. Compare source digests and the final package manifest with the recorded
   measurements. Package source, fixtures, proofs and result JSON; exclude
   generated Python bytecode and temporary LaTeX build files.

This integration review read the API and import boundaries and verified the
archived baseline bytes. It did not rerun the full suite; the final package's
validation summary records the final suite run and its exact result.
