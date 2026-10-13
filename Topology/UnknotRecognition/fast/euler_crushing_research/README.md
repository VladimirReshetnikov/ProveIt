# Exact Euler LP and crushing experiments

Run the audit from `fast/` with a Python environment containing Regina:

```sh
python -B -m euler_crushing_research.audit --output /tmp/euler-crushing-audit.json
```

`fixtures.py` reconstructs the 22 retained supplied sectors from
`projective_port_research.native.cases`: all 16 compatible supports on the
two-tetrahedron source and six longer capped sources. It adds eight sectors
with an interior vertex and eight with multiple boundary vertices. These
extra sectors include empty supports, uniform quad assignments, and fixed
seed partial assignments. No fixture is chosen from an LP result.

For each source, the audit freshly enumerates every original standard
vertex normal surface in Regina and saves its full coordinates and Euler
characteristic. The source enumeration is cached across sectors. Positivity
for a sector is determined independently by filtering this complete list
for positive Euler, a nonlink surface, and quadrilaterals in the allowed
support; native triangle potentials and LP objectives are not used.

Each sector runs both exact LP strategies without anchor or pivot caps and
independently replays the resulting Euler certificate. The Q-corner
comparison stops at its first positive ray; a negative result requires the
complete quadrilateral exhaustion certificate to pass the independent
verifier on the entire original allowed support. Every positive LP point
undergoes full-source support extraction and crushing. Regina separately
checks the extracted support rank and compares all labelled quotient face
gluings, component boundary Euler lists, and selected successor. The same
quotient comparison checks the positive Q witness.

An additional control is a canonical annulus-plus-disc sum with positive
Euler and support nullity two. Direct crushing must reject it; source
support descent must produce an independently crushable primitive ray.

The output saves full witnesses, certificates, exact ranks, original-source
oracle lists, and SHA-256 pins for the maintained modules and research
runners. The final source-pin comparison rejects concurrent source changes;
rerun after all runner edits have finished. This audit records no timings.
These are supplied solid-torus sectors, without diagram provenance. The
finite audit does not establish a polynomial simplex bound, a small global
anchor or sector family, or general quasi-polynomial recognition.

Run the timing experiment and bounded trefoil probe after the audit, with
other CPU-intensive tasks stopped:

```sh
python -B -m euler_crushing_research.audit --output ../synthesis/data/euler-crushing-audit.json
python -B -m euler_crushing_research.benchmark --output ../synthesis/data/euler-crushing-benchmark.json
python -B -m euler_crushing_research.probe --output ../synthesis/data/euler-crushing-probe.json
python -B -m euler_crushing_research.check_evidence
```

The benchmark compares adaptive disc search, the retained sequential
crushing driver, fair Q-corner search, and fair Euler LP search on two
complete positive diagram cases. It randomizes nine paired four-arm
repetitions, batches three recognitions per timing, and saves three
adaptive A/A controls. Full source construction and internal certificate
checks are timed; each arm's deterministic result is independently checked
outside the timer. Only the historical driver is loaded from its pinned
commit; shared dependencies use the current pinned sources.

The trefoil probe gives each crushing arm the same sector and Q-basis
caps, with separate LP pivot and anchor caps and a cooperative time ceiling.
It records progress and replays any returned partial chain. Its single
observations are not a repeated recognition benchmark. A cancellation has
no returned partial proof, and neither cancellation nor inconclusiveness
is a knot verdict.

The evidence checker replays saved certificates, compares the saved Regina
quotient records, recomputes timing arithmetic and source hashes, and
generates the article's timing table. It does not rerun oracle discovery.
After rebuilding the article PDF, run it with `--publication` to pin the
final article, PDF, tests, logs, and evidence. Source changes require fresh
audit, benchmark, and probe records before publication.
