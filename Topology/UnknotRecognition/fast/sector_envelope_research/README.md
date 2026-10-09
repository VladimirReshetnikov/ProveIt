# Exact minimum envelopes for low-dimensional normal sectors

These scripts reproduce the finite audit and controlled enumeration timings
for `fastunknot.sector_envelope`. They are explicit research tools and do not
change the ordinary recognizer's dispatch.

Run from `Topology/UnknotRecognition/fast/`:

```sh
python -B -m unittest discover -s tests -p 'test_sector_envelope*.py' -v
python -B -m sector_envelope_research.audit --fresh-regina --output OUTPUT/audit.json
python -B -m sector_envelope_research.benchmark --output OUTPUT/benchmark.json
```

The audit's default input is `../reports/57/results/discovery_corpus.json`.
Use `--corpus PATH` when running from a delivery containing a relocated copy.
The Python standard library is sufficient except for `--fresh-regina`, which
uses Regina to regenerate selected complete standard-surface enumerations.
The retained run used Regina 7.4.

The finite selection is declared in the audit source: every occupied support
of a frozen standard or quadrilateral vertex surface, every allowed support
of size at most two, and 64 deterministic full-sector draws per triangulation.
On at most three tetrahedra it instead includes all compatible supports. The
audit compares every selected sector of matching nullity at most two against
the complete frozen standard-ray list, with forbidden coordinates set to
zero. Larger-nullity sectors are counted and skipped explicitly.

`fixtures.py` adds a single tetrahedral ball to the boundary of the existing
Fibonacci layered solid-torus family. The base face pairings follow the
incoming dual-certificates report's `fibonacci_fixture.py`. This cap preserves
the solid torus and supplies a second independent allowed quadrilateral
coordinate. Cap types 1 and 2 have a genuine interior minimum switch; cap type
0 is a control without an interior switch. The audit saves a two-tetrahedron
example whose interior standard ray is independently certified as an
essential disc and is absent from the quadrilateral-ray list.

`baseline_normal_sector.py` is the exact unchanged source from ProveIt commit
`66098968e88bba797143ac1bf7ad0ac4c5f697df`, loaded under a private module name
to keep its enumeration policy independent of the new explicit method. Its
file hash and all timed source hashes appear in the benchmark record.

Timings include both reused-kernel enumeration and a complete kernel build
followed by enumeration. The default contains 13 paired cohorts, one warm-up
and five alternating AB/BA rounds per scope, and duplicate A/A arms on one
control. Large new-only capacity points are labeled separately. Every timed
output is compared by an exact canonical ray hash. Fixture construction,
output hashing and JSON serialization are outside the timed region. Run the
benchmark after other CPU-intensive local work finishes.

These are local sector-enumeration results. They do not supply a complete
sector search, prove a logarithmic search parameter, or establish a general
quasi-polynomial unknot recognizer.
