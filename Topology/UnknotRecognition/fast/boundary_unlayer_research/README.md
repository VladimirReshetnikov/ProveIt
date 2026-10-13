# Certified inverse boundary layers: research audit

This package audits the optional native removal of a boundary tetrahedron
whose deletion is independently certified as the inverse of a boundary
layering. It preserves source provenance, exact labelled successors and
finite allowances. No quasi-polynomial bound on unknot recognition follows.

From `Topology/UnknotRecognition/fast`, using a Python environment with Regina:

```sh
python -B -m boundary_unlayer_research.audit --output /tmp/boundary-unlayer-audit.json
python -B -m boundary_unlayer_research.audit --supplied-reductions --diagrams \
  --output /tmp/boundary-unlayer-full-audit.json
python -B -m boundary_unlayer_research.audit --diagram-scan-only \
  --output /tmp/boundary-unlayer-diagram-scan.json
python -B -S -m boundary_unlayer_research.replay /tmp/boundary-unlayer-full-audit.json
python -B -m boundary_unlayer_research.replay --regina /tmp/boundary-unlayer-full-audit.json
```

The basic audit reconstructs every labelled deletion independently with
Regina and checks finite orientable one-vertex torus-boundary topology. Its
source families are layered solid tori with 1, 2, 4, 8 and 16 tetrahedra,
two independently relabelled controls, and the retained three-layer trefoil
and figure-eight collars. For the first family, every predecessor is the
exact smaller layered-torus array. For the collars, every predecessor must
equal its retained labelled source. Regina also recognizes the solid-torus
controls; matching first homology alone is not used to identify manifolds.
The homeomorphism premise comes from the independently checked inverse
layering, not merely the Regina validity or homology observations.

With `--supplied-reductions`, each of the nine supplied sources is processed
with peeling disabled and enabled under two fixed search methods: depth-first
Euler branching and the conflict-based transversal search. These 36 arms
retain both improvements and regressions. Each arm repeatedly runs its fixed
full Euler query, extracts and verifies a positive ray, crushes, and
restarts until there is no torus component, a complete negative endpoint,
or an allowance is exhausted. Each arm has a default exploratory 20-second
discovery limit. Node, pivot, anchor and fallback allowances (plus candidate
allowances for transversal search) are shared across that arm's successors.
Partial chains survive timeout and receive independent
replay. Recorded work counts exclude work interrupted before a search call
returns. Such interruptions explicitly set `unreturned_query=true` and
`work_complete=false`; the recorded work is then a lower bound. Discovery
times are diagnostic and are not benchmark evidence.

The comparison concerns a complete reduction, not a single Euler decision:
canonical positive normal surfaces can change when the triangulation changes.
A supplied-source terminal or negative outcome is conditional on separately
authenticating the original source as a classical knot exterior. It is not a
native diagram recognition certificate. The retained forward collars remain
outside the diagram-chain schema, even though their inverse steps now have
their own independently checked packets.

With `--diagrams`, genuine small diagram recognitions use the conflict-based
transversal policy with the option disabled and enabled; their chains and
any final recognition certificates are independently checked. The separate zero-node scan adds further small
braids and records where the boundary faces lie after native vertex
reduction. A diagram run with no inverse layer is a valid control and is
reported as such.

Every final run pins all native Python sources, this package's source files,
and the immutable fixture inputs before and after its work. Outputs belong
outside this package, so they do not become their own source dependencies.
The separate replay imports neither the inverse-layer producer nor the LP
search producer, and its default mode requires no Regina. Native manifold
validation and packet replay establish its topological premises; retained
Regina observations are not regenerated in this mode. Add `--regina` to
repeat the independent labelled deletions and oracle topology checks.
Positive query observations are checked against original
STANDARD matching and canonical minima, and full negative masks are checked
explicitly. Bounded or timed-out queries remain inconclusive.
The default replay requires all nine inverse families, all 18 supplied
comparisons (36 arms), and exactly the three genuine diagram comparisons
(six arms), with complete diagram outcomes. `--allow-partial` explicitly
allows the smaller basic or scan audit modes; those are not publication
evidence for the full experiment.

The paired benchmark has a fixed protocol, declared before timing: supplied
layered tori with 1, 4 and 8 tetrahedra using depth-first search, plus genuine
circle, trefoil and figure-eight diagrams using conflict-based transversal
search. Each case has one warmup per arm, three alternating paired rounds,
and one baseline/baseline control pair. Every timed call includes fresh
reduction or recognition, independent replay, complete proof serialization
and result hashing. Input `Diagram` objects are prepared before warmups;
their native recognition runs still reconstruct and verify the exterior.
No Regina work is inside timed calls. Only the diagnostic
`discovery_seconds` field is removed for stable result hashes, which must
match the exact source and search method in the full audit.

```sh
python -B -S -m boundary_unlayer_research.benchmark \
  --audit /tmp/boundary-unlayer-full-audit.json --output /tmp/boundary-unlayer-timings.json
python -B -S -m boundary_unlayer_research.timing_replay \
  --audit /tmp/boundary-unlayer-full-audit.json --benchmark /tmp/boundary-unlayer-timings.json
```

All partial timed outcomes are retained. A paired ratio is reported only
when all three pairs complete the same conditional outcome or authenticated
diagram verdict and match their audited result hashes. Supplied-source
ratios do not establish a speedup for diagram recognition. The baseline
control ratio is retained separately and does not measure a preprocessing
benefit. Run timings only after other CPU work has stopped.
