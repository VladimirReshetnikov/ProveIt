# Integration contract and review gates

## Placement

Keep this delivery as a non-disruptive research package first. The adapter
imports `fastunknot.interval_orbits` and `fastunknot.interval_orbit_verify`
only when called. Add the package root and the maintained `fast` directory
to `PYTHONPATH`, or run the supplied native smoke script.

The inspected dense integration baseline is
`0441aad3967b69621edabfdb85367d465b4fb32f`. Use `provenance.json` to check
individual module hashes. Do not assume a moving `main` still has the same API.

## Inputs and outputs

`analyze_port_incidence_sparse(size, pairings, ports, ...)` takes the maintained
`IntervalPairing` objects. Pairing endpoints are inclusive and zero-based.
Port endpoints are half-open. Empty, overlapping, and repeated ports are legal.
All integers are exact Python integers, not booleans. For the package's
large-integer JSON format, decode with `sparse_ports.codec.loads` first.

A complete histogram is a list of `[mask, positive_multiplicity]` pairs in
minimal-extraction order, with an explicit sparse encoding marker. It is
**not** compatible with array indexing into the old dense histogram. A dense
conversion must be explicit and separately bounded by a port limit.

`max_entries`, `max_calls`, and `max_cycles` are optional local resource caps.
Calls and cycles are shared across discovery and the certificate pass.
Exhaustion yields `INCONCLUSIVE`, reason, and statistics, with no histogram
or certificate. Arbitrary callback exceptions propagate except where an
invalid-value exception is interpreted by a verifier as rejection.

## Verification

The verifier reconstructs each physical marked union, adds the deterministic
coning rows, and delegates every local proof to the maintained independent
orbit checker. It never calls sparse recovery or the native orbit producer.
It then verifies minimal residuals and total mass independently.

Contract tests in this delivery use injected literal count proofs to isolate
orchestration. They are not substitutes for actual maintained trace replay.
Run `native_smoke.py` to test the latter. Extend it with malformed source rows,
changed endpoints, missing/duplicate/unused proof indices, both native proof
versions, cycle limits during proof production, and genuine normal-arc data.

## Promotion gates

1. Genuine maintained smoke tests and full maintained suite, at recorded hashes.
2. Native normal-arc fixtures with independently checked geometric provenance.
3. Paired component timings including real proof production and replay costs.
4. Dense/full-support negative controls and memory/serialized proof sizes.
5. Whole-recognition benchmarks only after a sound dispatcher actually uses
   this interface. No current ordinary-dispatch speedup is asserted.

The signed generic module has no combined native certificate adapter yet.
A future wrapper must bind the separate parity bits and both-sheet port lift.
The generic continuation operators cover only coning, union re-marking,
and disjoint unions. They do not cover arbitrary boundary attachment maps.

## Suggested synthesis insertion

A short maintained article insertion can state: the dense `2**r` output is an
implementation cost, not an intrinsic lower bound for interval-incidence
profiles; weighted AHT theory gives polynomially many occurring types, and
a sparse nonnegative-zeta reduction can recover them through existing
unweighted count proofs. Reference the delivery's Section 6 for the explicit
support accounting, Sections 3--5 for recovery and verification, and Section 9
for the exact scope of continuation reuse. Preserve the distinction between
local polynomial work and a complete quasi-polynomial recognition theorem.
