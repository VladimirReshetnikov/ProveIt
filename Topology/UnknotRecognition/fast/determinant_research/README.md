# Boundary determinant research

`boundary_tait.py` validates matching coverage, inherited face colors and
spherical completion before interpreting a terminal quotient as a native
boundary observation. Its default algebra is the fraction-free integer kernel
in `fastunknot/terminal_determinant.py`; `arithmetic='rational'` retains the
exact rational kernel from report 26 as an independent reference. This
interface is not enabled by ordinary recognition dispatch.

The integer kernel eliminates the interior once, retains its null directions
and common determinant scale, then computes small integer quotient determinants
with checked exact division. `prepare_kernel(verify=True)` independently
replays the source binding using rational Schur elimination. It is 1.229 times
faster than the previous rational observer across the small native corpus and
19.223 times faster on a 73-vertex stage with 200 actual prefix queries. These
are observer timings, not full-recognizer speedups. A tested policy that waits
for four distinct queries before preparing the kernel wastes substantial work
on larger interiors and is not enabled.

Run `python -B benchmark_integer_terminal.py` from `fast/` to reproduce this
comparison. The earlier modular experiment below remains a historical record
of the rational default at its own pinned checkpoint. See the synthesis
article's fraction-free terminal section for the scaling formula, independent
replay and bit-complexity limits.

`terminal_plan.py` adds a field-plan traversal for the kernel protocol in the
dynamic-terminal delivery. It validates every merge, including descendants
whose values are forced to zero. Once the number of non-root blocks is less
than the prime-specific interior nullity, it skips all algebra in that cone.
An optional callback propagates interruption; counters are collected only
when requested. Preparing prime kernels and reconstructing integers belong
to the caller, and the delivered high-level adapter does not yet implement
the production deadline contract.

From the repository root, reproduce the native audit and benchmark with:

```sh
python -B Topology/UnknotRecognition/synthesis/data/audit_dynamic_terminal.py
python -B Topology/UnknotRecognition/synthesis/data/benchmark_dynamic_terminal.py
```

The driver recovers the immutable archive from its arrival commit, verifies
its digest and manifest, and uses its classes inside a temporary directory.
It compares 4,503 native queries with the maintained observer and independently
rebuilt completions, checks 24 native graph certificates, and tests the new
traversal against 15,840 integer quotient determinants. The saved query stream
comes from actual `FastScan` states.

The seven-arm benchmark includes fresh input and geometry setup, kernel
preparation, plan compilation and signed reconstruction. It records values
and all metadata. Small stages are batched to reduce timing noise. Direct
integer quotients are 1.245 times faster than rational evaluation on the
aggregate small-input corpus; dynamic modular evaluation is about 3.6 times
slower. Zero-cone pruning removes 77 field updates but does not improve the
aggregate time. These are observer measurements, not full-recognizer timings.

The `*_initial.py` files and initial audit JSON in `synthesis/data` are frozen
source snapshots for verifying the initial measurement record. They are not
alternate entry points: running one in the current tree would load current
dependencies. `dynamic-terminal-source-audit.json` maps the original paths
to their verified snapshots. The final benchmark above uses current sources.

See the synthesis article's dynamic-terminal section for the rank-two identity,
singularity cases, zero-cone proof, complexity accounting and remaining global
recognition obligations.
