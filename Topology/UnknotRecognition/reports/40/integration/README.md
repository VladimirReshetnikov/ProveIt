# Integration notes — opt-in research backend only

## Proposed location and source target

Preserve this package initially under a new named directory such as
`Topology/UnknotRecognition/proposals/port_registers_20261008/`.
Do not assume that a particular numbered report slot is unused. No remote files
were changed by this research session.

The inspected `scan_fast.py` blob is
`6c731d0f4d2c2c8bbe513e6b7495cf5dbdc8dc88`, verified at repository commit
`81a387aada56bb180649a98c21c078cb89efcfde`.
Only a targeted source subset was read. No complete checkout was available in
the working container; no upstream full-suite or production PD run was performed.

## The narrow adapter actually provided

`portkh.explicit.from_closed_fastscan(scan)` reads the interned-list fields
`points`, `mid`, `deg`, `out`, and `live` from the inspected API. It expects the
maintained scanner's valid-state invariants. It refuses an open frontier,
non-scalar coefficients, inconsistent live count/array lengths, different live
matching identifiers at the closed frontier, and maps into deleted objects.

It constructs a zero-length-register audit presentation from an already
explicit scalar matrix. This is NOT the native compressed producer required
for an asymptotic improvement. Its fixtures have the inspected field layout,
but a fixture is not a full upstream integration test.

Example at a genuinely closed, scalar stage:

```python
from portkh.explicit import from_closed_fastscan
from portkh.complexes import analyze

presentation = from_closed_fastscan(scan)
result = analyze(presentation)
# Compare result["homology_dimension"] with the existing engine for auditing.
# Do not turn this into a new default recognition branch.
```

The adapter trusts the scanner's assertion that `points` describes its current
frontier; it does not reconstruct planar geometry or authenticate a diagram.
A forged API-shaped object is not topological provenance. The independent cube
oracle produces its own small scalar complexes and is not an imported PD parser.

## Preserve the topology and error contract

The rank-two criterion needs a valid one-component classical knot diagram and
proven equivalence to its unreduced closed Khovanov homology over F_2. Never use
`rank_two` on arbitrary abstract examples as a knot certificate. Never interpret
resource exhaustion, conversion failure, or a declined admission test as proof
of nontriviality. The backend returns `topological_verdict: null` deliberately.

The solver does not preserve tangle-relative chain maps. Do not pass it residue
matrices at an open frontier and discard dotted maps or matching types. In
particular, the scalar generalized inverse is not a substitute for a certified
cobordism-category cancellation. Common-disk radical assumptions remain separate.

## Why the default should not change yet

The explicit bridge was slower on all four measured small knot cubes. Complete
closed scalar cancellation often already leaves zero differential, so a late
adapter may be redundant. The new consumer helps only when an earlier native
producer avoids allocating the virtual repeated objects in the first place.

A useful producer must expose:

1. Template dimensions and the cost of proving/constructing those templates.
2. Raw and minimum fixed-base port counts, register widths, accepted-domain
   counts, and all data needed to evaluate coordinates exactly.
3. Homological typing and a certified relative path to the final closed scalar
   complex; output equivalence cannot be inferred from coincident ranks alone.
4. Measured producer cost, failed-attempt overhead, peak descriptor storage,
   and a valid fallback state at every transition.

The tensor-amplification theorem is an admission warning: retaining a fixed
base under tensoring with an identity can multiply the minimum port count.
An output register of small width does not defeat this rank lower bound.

## Validation gates before production adoption

Run the complete maintained suite and production PD corpus at an identified
commit. Compare with ordinary scans under several crossing orders. Include
unknots, nontrivial knots, links where supported, intentionally malformed inputs,
small/sparse controls, and families large enough for the native descriptor to
matter. Measure the entire attempted conversion and fallback, not just the
small-core arithmetic. Preserve the existing standard backend until the
conversion exhibits a real advantage without weakening certificates.

The bundled replay checker shares implementation with the solver. For a smaller
trusted computing base, independently verify rank-minor identities, register
reachable-space closure, parity contractions, and the small core. A future Lean
formalization and a native Rust implementation are research tasks, not delivered
or tested features of this package.
