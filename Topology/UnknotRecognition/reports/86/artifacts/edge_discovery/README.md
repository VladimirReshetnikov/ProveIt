# Edge-defect research: reproduction and contracts

The production implementation, tests, and research driver are frozen after
**13 focused unit tests passed**. The exact log is `focused-tests.log`.
The implementation changes no maintained default-recognizer route.

The longer `implementation_audit.md` records the derivations, full fixture
counts, benchmark interpretation, and remaining mathematical hypotheses.

## Files to integrate

All three files are additive under `Topology/UnknotRecognition/fast/`:

```text
fastunknot/normal_weight_defect.py
tests/test_normal_weight_defect.py
normal_orbit_research/weight_defect.py
```

Retained evidence in this directory:

| File | Contents |
|---|---|
| `benchmark.json` | Clean seven-round paired timings, deterministic counters, fresh verification timings, and all successful normal-vector certificates. |
| `regina-audit.json` | 138 independently enumerated standard vertex surfaces, 12 meridians, 11 subspace coverage queries; native layered-family constructions and certificates; explicit large-coordinate external-audit omissions. |
| `enumeration.json` | Complete arrangement construction for k=0,1,2 on the eight-tetrahedron obstruction. |
| `cone-audit.json` | Producer-independent topology replay for the genus-two, genus-one, and disc surfaces at edge increments 0,2,4. |
| `first-witness.json` | The new 47-piece standard vertex meridian and its independent native disc certificate. |
| `focused-tests.log` | The thirteen-test frozen implementation verification. |
| `implementation_audit.md` | Detailed implementation audit and interpretation. |

`layer_probe.py` was an intermediate prototype. The maintained research
driver contains its complete replacement and should be used for integration.

## Commands

Run from `ProveIt/Topology/UnknotRecognition/fast/` with the standard-library
Python environment:

```bash
python -m unittest tests.test_normal_weight_defect -v
python -m normal_orbit_research.weight_defect family --output family.json
python -m normal_orbit_research.weight_defect enumeration --output enumeration.json
python -m normal_orbit_research.weight_defect benchmark --rounds 7 --output benchmark.json
```

The optional independent audit requires Regina:

```bash
python -m normal_orbit_research.weight_defect regina --output regina-audit.json
```

The `all` mode runs the family, full enumeration, benchmark, and optional
Regina audit sequentially and therefore also requires Regina:

```bash
python -m normal_orbit_research.weight_defect all --rounds 7 --output all-results.json
```

In the recorded environment Regina was installed in a separate dependency
directory; the exact external-audit invocation was:

```bash
PYTHONPATH=/workspace/scratch/09ebd0ee5016/deps python -m normal_orbit_research.weight_defect regina --output /workspace/scratch/09ebd0ee5016/algorithm_notes/regina-audit.json
```

That installation path is an environment detail, not a required project path.
The non-Regina implementation has no new third-party dependency.

## Public contracts

Every source is a **supplied finite one-vertex triangulation** with exactly
one torus boundary and first Betti number one. The existing native validator
enforces finite-manifold conditions; the exact cocycle producer enforces
rank one. Every positive result concerns that triangulation. The code does
not bind it to a knot diagram or decide knottedness by exhaustion.

```python
from fastunknot.normal_weight_defect import (
    one_edge_defect_search,
    weight_defect_search,
    discover_in_weight_subspace,
)
from fastunknot.normal_disk_kernel import verify_normal_disk_count_certificate

# Complete for standard vertex meridians with edge cancellation support <= 1.
answer = one_edge_defect_search(triangulation)

# General direct arrangement implementation, preserving the same vertex promise.
answer = weight_defect_search(triangulation, max_defect=2)

# A supplied set of validator global-edge root labels.
answer = discover_in_weight_subspace(triangulation, defect_edges=[30])

if answer['status'] == 'DISC_FOUND':
    assert verify_normal_disk_count_certificate(
        triangulation, answer['coordinates'], answer['certificate'])
```

The last example's root label 30 is specific to the canonical obstruction
fixture. The support cardinality is invariant; edge labels and early-return
search ordering depend on the serialized triangulation.

All discovery calls internally invoke the independent verifier before
returning a positive. The returned certificate is the existing binary
normal-disc certificate; no discovery transcript is needed for positive
replay. The general arrangement emits every unrestricted standard vertex
ray in the selected weight space and may emit additional restricted rays.
`NO_VERTEX_DISC_UP_TO_EDGE_DEFECT` and
`NO_VERTEX_DISC_IN_WEIGHT_SUBSPACE` are restricted exhaustion statements and
have no independent exhaustion certificate. Resource limits return
`INCONCLUSIVE` without any absence claim. Caller cancellation exceptions
propagate. Input triangulations are not modified.

`max_bases` is global over the query. For the general arrangement it counts
begun (dimension-1)-hyperplane intersections. For the optimized one-edge
method it counts one baseline attempt plus all begun row-edge incidences,
including arithmetically rejected incidences. `max_subspaces` is available
on the general method and counts entered edge sets. Native component-query
limits use the existing `max_orbit_cycles` parameter. Preparation and
independent replay are outside the two combinatorial search counters.

## Why the prefilters preserve the stated promise

The Euler prefilter rejects a vector only if its **total** Euler
characteristic is nonpositive. A primitive standard vertex disc has Euler
characteristic one, so the promised target is retained. This prefilter may
skip a disconnected vector consisting of a disc plus components with
negative Euler characteristic. The search does not claim to inspect every
mixed surface containing a disc.

For an oriented essential meridian in a one-vertex rank-one source, the
signed edge-intersection cocycle is plus or minus the primitive generator.
Its unsigned weights therefore have the form b+2z with nonnegative integer
z. The optimized one-edge method's positive-even-offset test is a necessary
condition for the promised target. The coherent ray handles support zero.
If b is supported entirely on the sole exceptional edge, every such weight
vector lies on that same coherent ray, so this exceptional case is also
covered by the baseline. The argument uses the **standard vertex disc**
promise; an arbitrary meridian disc with small cancellation support has not
been shown to yield a standard vertex meridian with equally small support.

The general sparse-row matching theorem for k>1 is **not implemented** in
the optimized routine. The implemented general-k method retains all small
weight subspaces and enumerates their arrangements. The row-matching
improvement is implemented only for k=1.

## Benchmark protocol and environment

The retained benchmark runs on CPython **3.12.14**, x86_64 Linux
**6.18.44**, glibc **2.39**. The interpreter was
`/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python`.
The optional engine reports Regina **7.4** (installed distribution 7.4.1).
No machine-independent wall-clock guarantee is inferred.

Four canonical supplied triangulations have 8,16,40,72 tetrahedra. They are
the coherent obstruction followed by 0,8,32,64 Fibonacci boundary layers.
For each source, every arm gets one excluded warm-up, followed by seven
measured rounds. Arm order is shuffled by RNG seed 261012084. Each arm
performs its own cocycle preparation and all required positive checking.
Discovery times include the native component observer and internal
independent replay. A fresh independent replay is additionally timed and
reported separately. The final retained timing run did not run concurrently
with this task's heavy audits.

The arms are coherent-only radius zero, existing seeded Q-sector search,
general all-subspace radius one, optimized global one-edge search, and
supplied-edge search. All positive arms return the **same exact coordinate
vector** at each size. Coherent-only exhaustion is not compared as a
successful recognition time. The original seeded sector already contains
the new disc; the improvement is not additional sector coverage on these
fixtures. Its matching nullity remains three, while its kernel size grows.
The recorded performance difference therefore includes a substantial
reduction in exact algebra/setup work on this structured family.

## Limits of independent external auditing

Regina independently enumerated 138 standard vertex surfaces on eight
sources with 1 through 8 tetrahedra. The audit checked exact local
reconstruction on every surface and the meridian recovery promises where
applicable. Regina also verified disc and coherent-surface topology for
the layered family through eight extra layers.

The larger layered surfaces have rapidly growing normal coordinates.
Regina's installed documentation says that `isConnected` and `isOrientable`
explicitly build normal discs; `isCompressingDisc` may cut and retriangulate;
`countBoundaries` builds boundary arcs. External surface-topology checks
are therefore omitted above 10,000 normal pieces, and the result JSON
records this explicitly. Native binary normal-coordinate certificates and
exact extremality checks remain in force for the larger cases. An initial
unbounded external audit terminated with exit code 137; no claims are based
on its unretained partial result.

## Supplementary polynomial vertex-disc certificate

`vertex_gate.py` and `test_vertex_gate.py` are separate supplementary
artifacts. They do not change the frozen discovery implementation or any
reported discovery benchmark. **Seven additional focused tests pass**;
the exact log is `vertex-gate-tests.log`.

The gate certifies that an entire supplied primitive admissible normal
surface is an essential disc. It reuses only the finite-manifold and
normal-coordinate validators. It does not require one vertex or first Betti
number one: multiple boundary vertices are explicitly supported. There are
no imports or calls to normal-component or disc-discovery algorithms.

Its independently replayable certificate contains a nonzero original
matching minor of order s-1, where s is the number of positive coordinates.
The source vector is itself in the matching kernel, so this establishes
nullity exactly one on its support. Every connected component has an
integral coordinate vector proportional to the source. The verified gcd-one
condition and Bezout's identity force those proportionality factors to be
integers; their sum is one, so the source is connected.

The checker also verifies Euler characteristic one and that the boundary
edge-intersection parity cocycle is nonzero modulo boundary-vertex
coboundaries. The latter implies nonempty boundary. Classification of
compact connected surfaces then makes the surface a disc, and the nonzero
class makes its boundary essential on the torus. Orientability and component
orbit computation are unnecessary. With several boundary vertices, raw
nonzero edge parity is insufficient; the explicit cohomology quotient is
essential and is covered by a counterexample regression test.

The producer selects a rank minor by its own sparse rational elimination.
The verifier reconstructs that minor from the supplied source equations and
evaluates it by fraction-free Bareiss elimination. It does not call the
producer or its rank-selection routine. Binary elimination independently
computes the boundary coboundary span and its rank increase after adjoining
the source parity vector. All proof fields and source bindings are checked
strictly. These are polynomial computations in the binary input size; they
do not depend on a bound for an orbit trace.

From the directory containing the supplementary scripts, after adding the
repository's `Topology/UnknotRecognition/fast` directory to `PYTHONPATH`:

```bash
python -m unittest test_vertex_gate -v
python vertex_gate.py verify --input vertex-gate-r0.json
python vertex_gate.py verify --input vertex-gate-r64.json
python vertex_gate.py produce --input vertex-gate-r64.json --output regenerated-r64.json
```

The source JSON contains `triangulation` and `coordinates`; the producing
command adds a `certificate`. Both retained inputs already contain that
certificate and can be replayed without any witness discovery. A false gate
result means that this particular rank certificate did not certify the
supplied vector; it is not a knot or manifold verdict.

`vertex-gate-audit.json` retains fresh production and independent replay
measurements at 8,16,40,72 tetrahedra. Replay took approximately
0.00101,0.00416,0.0523,0.284 seconds, respectively. These are single recorded
gate measurements, not a repeated benchmark. At 72 tetrahedra the matching
minor has order 216, and the compact JSON certificate occupies 2,789 bytes
excluding the separately supplied triangulation and normal vector. The
surface represents 308,061,521,170,163 normal pieces. Its complete CLI replay
passes. The supplementary gate is not presented as faster than the existing
specialized unit-ray observer; its purpose is a transparent polynomial
verification bound.

The frozen supplemental source hash is
`17841f495497db26c1c5e87d12977336bc7815d1621142114ce08455f1503d87`.
