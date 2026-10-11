# fastunknot 0.3.0: braid and structural certificates with optional shared backends

`cocycle_span.minimize_cocycle_span` now handles a single global vertex with
a direct primal/dual certificate: every potential is a uniform height shift,
so the optimum is the original sum of spans. This takes linear arithmetic
work, including independent replay, without allocating the flow network.
The proof schema and multiple-vertex solver are unchanged. The API still
makes no topology or unknot claim by itself.

`pachner32.pachner_32(triangulation, tetrahedron, [vertex_a, vertex_b])`
performs one 3–2 move about an interior edge in three distinct tetrahedra;
`pachner32_verify.verify_pachner_32(before, after, certificate)` independently
checks the replacement. One such move escapes the retained genus-two
coherent-family obstruction and produces a 36-piece coherent normal disc.
Greedy simplification found no additional labels beyond the existing extended
search on the tested diagram corpus, so it has not entered the recognition
schedule. Theory, limits and measurements are in
[`coherent_escape.tex`](../synthesis/coherent_escape.tex). Reproduce with
`python -B -m normal_orbit_research.coherent_escape audit --output FILE`
or `benchmark --rounds 5 --output FILE`; audit mode requires Regina.

The explicit `pachner23.pachner_23(triangulation, tetrahedron, face)` API
performs one canonical 2–3 move on a finite torus-boundary triangulation.
Its result contains a fresh `triangulation`, a selected-face `certificate`,
and work statistics; `pachner23_verify.verify_pachner_23` independently checks
the old/new formal boundary maps. It is not part of the recognition schedule.
The `coherent_family_verify.inspect_one_vertex_family` checker verifies an
exact rank-minor certificate for all primitive coherent-height vectors on a
one-vertex triangulation. A retained eight-tetrahedron solid torus has a
unique such vector of genus two, although a separately certified 51-piece
normal compressing disc exists. This is a candidate-family obstruction,
not a negative knot certificate. See
[`coherent_obstruction.tex`](../synthesis/coherent_obstruction.tex), and run
`python -B -m normal_orbit_research.coherent_obstruction replay --record ../synthesis/data/coherent-obstruction-certificate.json`
for producer-free proof replay without Regina.

Orbit queries can now return independent local proofs with
`count_orbits(..., record_certificate=True)`. Replay with
`fastunknot.interval_orbit_verify.verify_orbit_certificate(size, pairs, proof)`.
Version one preserves classical merging; version two permits the exact
Fine–Wilf threshold. Use `integer_codec.json_safe` for huge binary integers.
Incomplete queries return no count or certificate.

`fastunknot.interval_incidence.analyze_port_incidence` counts components meeting
each subset of supplied half-open marked intervals. It shares repeated unions
and stores each orbit proof once. All orbit queries share one `max_cycles`
allowance; the explicit default cap of 12 ports controls the dense `2**r`
histogram. Its independent verifier checks source binding, every distinct orbit
proof and forward subset sums. These signatures record set incidence, without
cyclic order, slopes or attaching maps. All 831 maintained tests pass with Regina.
Theory and measured gains/regressions are in
[`orbit_certificates.tex`](../synthesis/orbit_certificates.tex). Reproduce with
`python -B benchmark_orbit_certificates.py --output FILE`,
`python -B normal_orbit_research/benchmark_trace_cost.py --output FILE`, and
`python -B normal_orbit_research/audit_certificates.py --output FILE`.

`fastunknot.interval_orbits.count_orbits` now counts equivalence classes of
binary-encoded interval pairings without expanding their points. The default
uses the sharp Fine–Wilf periodic merger; `periodic_rule='aht'` retains the
classical threshold. `max_cycles` counts begun cycles, and exhaustion returns
no count. Optional callbacks provide cooperative cancellation.

`fastunknot.normal_surface_orbits.normal_surface_topology` validates a supplied
finite, compact, connected, orientable triangulation with one torus boundary
and admissible seven-coordinate normal surfaces. It returns component and
orientation counts, boundary count, total Euler characteristic, and whether a
connected supplied disc has essential boundary. All three orbit queries share
one allowance. It does not certify correspondence with an input knot diagram.
Ordinary recognition does not dispatch this interface. The theory and remaining
geometry obligations are in [`interval_orbits.tex`](../synthesis/interval_orbits.tex).
All 805 maintained tests pass with Regina. Reproduce the component measurements
with `python -B benchmark_orbits.py --output results/orbits.json`; the committed
run is `results/orbits_20261008.json`, with shuffled classical/sharp/A/A arms.

The existing normal-surface worker also stages UTF-8 request and result streams
in temporary files. This avoids losing partially written pipe input after a
timeout, while preserving cooperative deadlines and child/stream cleanup.

Explicit overlap search now skips donors whose lengths cannot exceed the
best guaranteed shortening already found, and stops a donor scan when its
upper bound is attained. This preserves the complete selected witness and
independent replay, while reducing work for repeated long donors. See
[`exposure_residual.tex`](../synthesis/exposure_residual.tex) for the proof,
controlled measurements, and an independently verified continuation of the
Whitehead report's stalled Gordian residual. The exposure handoff remains an
offline experiment: the existing search already recognizes that input faster.
Reproduce the pruning audit with
`python -B exposure_research/benchmark_bounds.py`.

Compressed substring queries also bound matches by the directed signed-letter
pairs shared by both words. This handles some expensive cases with identical
alphabets. Whole-donor search rejects impossible pair sets, including the
cyclic seam and inverse orientation, before allocating inverses or matching.
Uniform words reuse their exact metadata to avoid redundant pair extraction.
All 687 tests pass. The complete exact fallback and independent relator replay
remain in place; a general subexponential bound is still unproved. See
[`lcs_transitions.tex`](../synthesis/lcs_transitions.tex) for the proofs and
controlled results. Reproduce them with `benchmark_lcs_transitions.py` and
`benchmark_donor_pair_shortcut.py`, each taking `--output PATH`.

Compressed substring queries now use exact shared-alphabet run bounds and
process extension witnesses as soon as they are checked. Letters absent from
the other word act as barriers; once a witness reaches a proved global or local
bound, the remaining candidates are skipped. Same-alphabet queries retain the
complete fallback. All 687 tests pass, including exponentially long inputs
where tables are forbidden once optimality is already proved. See
[`lcs_bounds.tex`](../synthesis/lcs_bounds.tex) for the proof and scope.
Reproduce the isolated component audit with
`python -B benchmark_lcs_bounds.py --output results/lcs_bounds_local.json`.

When whole-donor search would stall, compressed group search now finds partial
cyclic overlaps over all donor rotations and both signs. The exact compressed
longest-common-substring primitive uses dyadic overlap progressions and at most
six periodic extension candidates per progression. Shared-letter counts give
safe pruning and early completion bounds. Existing independent relator replay
checks every emitted move. The integrated suite has 687 passing tests; the
local query has a polynomial bound, while general recognition remains unproved.
See [`compressed_lcs.tex`](../synthesis/compressed_lcs.tex) for proofs and limits.

Compressed whole-donor search now batches consecutive copies in a version-4
`relator_power` certificate. Both literal and compressed verifiers independently
check the entire removed prefix. Exact uniform-letter summaries make equality
and prefix queries on pure powers constant work, and ineligible donor pairs are
pruned before allocating inverses. On supplied pure-power presentations this
turns repeated subtraction into Euclidean division; the general recognition
bound remains unproved. The integrated suite has 687 passing tests with Regina,
including a genuine Gordian trace accepted by both verifiers, forged macro
rejection, and a compressed `2^500` replay without expansion.
The proof and limits are in [`relator_powers.tex`](../synthesis/relator_powers.tex).
Reproduce the component-controlled audit with
`python -B benchmark_relator_power.py --output results/relator_power_local.json`.

When compressed group search would stall above the explicit-letter cap,
`--group-relators` now enables exact whole-donor deletion without expansion.
A fully compressed substring matcher uses arithmetic-progression occurrence
tables and a safe first-letter probe. It searches every cyclic target position
for the donor's recorded spelling or inverse; arbitrary donor rotations and
partial overlaps are handled by the later complete cyclic fallback. Accepted moves use the existing
independent relator certificate replay. Work and storage limits remain
inconclusive, and no general subexponential bound is claimed.
See [`compressed_matching.tex`](../synthesis/compressed_matching.tex) for the
proof and boundaries. Reproduce the matched measurements with
`python -B benchmark_compressed_match.py --output results/compressed_match_local.json`.
The supplied exponential presentation family now completes in two moves;
existing knot-corpus paths and timings remain essentially unchanged.

Compressed group search now batches powers of a selected Whitehead automorphism
when the move repeats or expanded length exceeds four times allocated grammar
size. An exact weighted-median gap profile chooses the first minimizing power
without expanding the words. Version-3 certificates are checked independently
by compressed substitution or literal elementary replay. The explicit search
policy is unchanged. This removes exponential unit descent on a supplied
compact presentation family; a general subexponential recognition bound remains
unproved. See [`whitehead_powers.tex`](../synthesis/whitehead_powers.tex).
Reproduce the matched historical comparisons with
`python -B benchmark_whitehead_power.py --output results/whitehead_power_local.json`.
Use `--case survivor-02 --rounds 21 --queries-only` for a focused timing audit.
Saved primary and follow-up results retain all raw samples and censoring status;
no speedup on the current knot corpus is claimed.


This research continuation adds a linear signed Seifert-graph certificate before
the established recognition pipeline and three optional Khovanov backends.
The new front end completely decides homogeneous input diagrams after validation.
When inconclusive it continues the original stages. Disable it with `--no-seifert`
or `use_seifert=False` to retain the previous stage order.

If the initial Reidemeister I/II pass removes crossings but does not finish,
the pipeline repeats the structural check before matrix filters. Cancelling
pairs can expose homogeneity. Evidence under `seifert_after_reduction` describes
the reduced diagram: replay `reidemeister_trace` with `fastunknot.simplify.replay`
before passing that certificate to `verify_seifert_certificate`. An unchanged
diagram is not checked twice. The integrated suite now has 687 passing tests
with the optional Regina dependency installed.

`--group-adaptive` starts the optional group search with explicit words, then
switches once to SLPs before a substitution would exceed its letter allowance.
The switch preserves the current presentation, completed moves and remaining
work/time budget. It automatically uses compressed replay after a handoff;
without a handoff, replay stays explicit. `--group-switch-letters 4096` enables
an earlier optional threshold; Python callers use `use_group=True,
group_adaptive=True, group_switch_letters=4096`. Always-compressed search and
adaptive search are mutually exclusive.

The default switch threshold equals the hard letter cap. It preserves all
fifteen current corpus traces and their explicit representation. In 375 whole
queries its timing is near the explicit controls; earlier switching on Gordian
costs 1.641 seconds versus the explicit control's 1.251 seconds. With hard caps
of 64/60 letters on two small cases and 4096/8192 on Gordian, the adaptive stage
instead recovers verified certificates in all twenty measured probes where
explicit search exhausts the cap. Those exhaustion times are not speedups.
See [`results/adaptive_group_20261008.json`](results/adaptive_group_20261008.json)
and [`adaptive_group.tex`](../synthesis/adaptive_group.tex) for complete scopes,
the bounded explicit-prelude argument and the unresolved asymptotic limits.

```sh
python -B -m fastunknot recognize normal_research/gordian.json \
  --group-adaptive --group-relators --group-seconds 3 \
  --group-max-work 10000000 --seconds 5
python -B benchmark_adaptive_group.py --output results/adaptive_group_local.json
```

`--group-compressed-search` enables optional compressed group discovery and
replay. Exact generator counts, unique-occurrence masks and weighted Whitehead
graphs are computed from shared word grammars. Elimination and Whitehead moves
stay compressed; optional relator-overlap matching expands only when the total
length fits its 200,000-letter cap. Above that cap the overlap probe is skipped,
and failure to finish remains inconclusive. Python callers use
`use_group=True, group_compressed_search=True`; the standalone producer is
`fastunknot.compressed_search.compressed_certificate`.

The compressed word checker now indexes assertions by the symbols they mention.
It first tries a bounded 64-step DAG walk, then switches to the polynomial
split-and-compaction algorithm if unresolved. The cap preserves the polynomial
equality bound even when the represented words are exponentially long.
Standalone `WordArena(equality_probe_steps=0)` disables the direct probe.

Cancellation now uses a separate bounded prefix walk and reuses its proved
prefix in the polynomial fallback. Bisection compares only the still-unproved
interval. `WordArena(prefix_probe_steps=0)` disables this direct walk while
retaining the improved bisection rule; the default cap is 64 steps.

In the latest 375-query comparison, Gordian's compressed-search median drops
from 2.461 to 1.922 seconds with the prefix changes, including independent replay.
Fourteen smaller cases total 185.27 versus 245.18 ms in summed medians.
Explicit search remains faster at 1.259 seconds and 51.50 ms respectively.
The direct walk resolves 895 of Gordian's 971 prefix queries; equality calls
fall from 3,035 to 271. Some synthetic kernels still favor suffix-only bisection,
so this is not a uniform speedup. All measured queries complete successfully. Synthetic
summary and elimination operations handle lengths above 2^1024 with 3,077
allocated nodes, but this is not a hard-knot benchmark or a search-step bound.
Explicit search remains the default. To reproduce the optional experiment:

```sh
python -B -m fastunknot recognize normal_research/gordian.json \
  --group-relators --group-compressed-search --group-seconds 10 \
  --group-max-work 10000000 --seconds 12
python -B benchmark_compressed_search.py --output results/compressed_search_local.json
```

See [`results/compressed_prefix_20261008.json`](results/compressed_prefix_20261008.json)
for the current prefix comparison,
[`results/indexed_equality_20261008.json`](results/indexed_equality_20261008.json)
for the previous equality improvement, and
[`results/compressed_search_20261008.json`](results/compressed_search_20261008.json)
for the initial capacity experiment. The article gives the equality scheduling
and fallback invariants, DAG multiplicity proof and remaining global limits.
`python -B benchmark_compressed_prefix.py --output results/prefix_local.json`
reproduces the latest comparison using the recorded pre-change kernel from Git history.

`--group-compressed` enables only exact SLP-based replay of group certificates.
Its deterministic word kernel supports equality, slicing, inversion and free
reduction without expanding the represented strings. Recognition still searches
with explicit relators. The existing certificate formats remain unchanged;
Python callers select `group_compressed=True` together with `use_group=True`,
or call `verify_group_certificate(diagram, certificate, compressed=True)`.

This is an experimental capacity extension. In constructed proof traces, it
checks intermediate words with 90-bit lengths using 904 grammar nodes, while
the explicit checker exhausts its letter cap. On the present knot corpus it
costs more: Gordian's median whole query rises from 1.236 to 1.417 seconds.
Explicit replay remains the default. The node/assertion ceiling is 100,000;
standalone verification accepts `max_nodes`, `max_work`, and a `stats` dictionary.
In compressed mode `max_letters` bounds the initial presentation only.

```sh
python -B -m fastunknot recognize normal_research/gordian.json \
  --group-relators --group-compressed --group-seconds 2 \
  --group-max-work 10000000 --seconds 4
python -B benchmark_compressed_words.py --output results/compressed_local.json
```

See [`compressed_words.tex`](../synthesis/compressed_words.tex) for the
split-and-compaction equality proof, exact boundary cancellation, validation,
and the distinction between polynomial word operations and unbounded search
or grammar growth. Raw whole-query and constructed-capacity measurements are
in [`results/compressed_words_20261008.json`](results/compressed_words_20261008.json).

`--group-relators` adds exact relator-overlap substitutions to the group
certificate stage and enables it. It uses suffix automata to avoid expanding
all cyclic rotations. The search chooses Whitehead moves first at six or
fewer surviving generators and overlaps first at larger rank, with safe
fallback when either search stalls. This empirical dispatch rule preserves
all twelve original survivor traces and also certifies the two previously
stalled mirrors.

The 141-crossing Gordian example now has a **native, independently checked**
certificate with 140 generator eliminations and one overlap substitution.
In five paired runs it finishes at a median 1.212 seconds including replay,
versus 1.708 seconds through Regina. Older controls time out at four seconds.
It needs larger allowances than the default short probe:

```sh
python -B -m fastunknot recognize normal_research/gordian.json \
  --group-relators --group-seconds 2 --group-max-work 10000000 --seconds 4
```

Python callers use `use_group=True, group_relators=True, group_seconds=2,
group_max_work=10000000`. Replay a saved version-two certificate with
`verify_group_certificate(diagram, certificate, max_work=10000000)`.
Version-one certificates remain supported. This stage has no Regina dependency.
See [`relator_overlap.tex`](../synthesis/relator_overlap.tex) for the
normal-closure proof, suffix-automaton algorithm and conditional complexity
bound. The mode remains optional and does not establish general
sub-exponential recognition.

`--group` (Python: `use_group=True`) tries a bounded knot-group certificate
search after invariant filters. Exact generator eliminations and Whitehead
changes of basis reduce a full Wirtinger presentation; an independent checker
reconstructs and replays the trace before accepting a one-generator,
relation-free presentation. For a validated classical knot this proves
unknottedness. Stalling or local exhaustion falls back to the remaining
recognizers, and a global deadline still yields `UNKNOWN`.

```sh
python -B -m fastunknot recognize examples/hard_unknot_8.json --group
python -B benchmark_group.py --output results/group_local.json
```

Search and replay share `--group-seconds 0.05` per attempt. The standalone
`fastunknot.group_certificate.group_decide` also accepts `max_letters` (default
200,000) and `max_work` (default 2,000,000 per search/replay); `seconds=None`
removes only the wall cap. `group_certificate` produces a trace, and
`verify_group_certificate(diagram, certificate)` independently checks it.
Certificates contain the actual normalized PD used by that stage; when the
pipeline has reduced or factored the input, its earlier evidence supplies
the connection to the original diagram.

In seven paired whole-query rounds this stage certified all twelve maintained
Khovanov-only survivors. Ten improved, with the largest gains about 2.3x and
3.3x. The sum of their median costs fell from 60.8 to 39.2 ms, including replay.
Two survivors and the already cheap RIII examples regressed, so the stage is
**disabled by default**. No general sub-exponential bound is established:
word expansion and stalled searches remain obstacles. See
[`group_certificates.tex`](../synthesis/group_certificates.tex) for the theory,
new-preprint convention audit, benchmarks and limitations, and
[`results/group_20261008.json`](results/group_20261008.json) for raw measurements.

`--regina` (Python: `use_regina=True`) adds an optional complete external
normal-surface recognizer after cheap invariant filters, on undecided diagrams
with at least 32 crossings. Install the extra in the interpreter running the
recognizer:

```sh
python -m pip install '.[normal]'
python -B -m fastunknot recognize normal_research/gordian.json --regina --seconds 4
```

Each attempt runs in a fresh subprocess, with a default two-second local
allowance including native import and startup (`--regina-seconds`). Missing
dependencies, native failures and local timeouts are inconclusive and continue
the existing RIII/Khovanov pipeline. A global deadline yields `UNKNOWN`; every
interrupted worker is killed and reaped. `max_objects` bounds Khovanov, not
Regina's memory. Python's `regina_seconds=None` disables the local cap.
`fastunknot.normal_surface.regina_decide` offers the standalone query without
the pipeline's crossing threshold.

This is explicitly an **external-engine verdict**, not an independently
verified normal-surface certificate. Evidence records input digest, engine and
distribution versions, simplification and triangulation sizes, and elapsed
time. Serialized external verdicts do not inherit the built-in runtime bound.
The default remains dependency-free and does not call Regina.

In five paired runs, the portfolio decided Haken's 141-crossing Gordian unknot
every time (median 1.788 seconds including validation and child startup); both
default controls exhausted their four-second allowance every time. GST,
Monster and Conway stayed on the existing fast paths. These are censored
completion comparisons, not a general speedup or asymptotic theorem. See
[`normal_research/README.md`](normal_research/README.md),
[`normal_surface.tex`](../synthesis/normal_surface.tex), and
[`results/normal_surface_20261008.json`](results/normal_surface_20261008.json).

An optional complete test for **projection graphs of treewidth at most two**
is enabled by `--treewidth-two` or `use_treewidth_two=True`. It first certifies
that the crossing graph excludes a K4 minor, then computes the exact integer
determinant. On this class, the structural classification as connected sums
of two-strand torus knots makes determinant one sufficient for `UNKNOT`.
Arbitrary determinant-one knots do not pass this rule. No supplied braid or
rational-tangle presentation is required.

```sh
python -B -m fastunknot recognize examples/trefoil.json --treewidth-two --no-braid
```

The local allowance defaults to 0.1 seconds (`--treewidth-two-seconds`);
exhaustion continues the existing recognizer, while a global deadline yields
`UNKNOWN`. Python's `treewidth_two_seconds=None` removes the local cap.
`fastunknot.treewidth_two.treewidth_two_certificate` provides the uncapped
standalone producer, returning `None` outside the class.
`verify_treewidth_two_certificate` independently replays the graph order and
recomputes the determinant with Fox matrices and rational elimination.
The producer has polynomial bit cost on this class; it does not implement
the published linear-time generalized-diagram algorithm. A capped probe
followed by Khovanov fallback does not inherit the polynomial bound.

`benchmark_treewidth_two.py --output FILE` measures validation plus complete
recognition on fresh PD inputs with paired controls. The recorded run improves
three mixed-sign two-strand unknot cases by 1.085–1.142x, but slows several
cases already handled cheaply by Seifert certificates. It remains optional.
See [`treewidth_two.tex`](../synthesis/treewidth_two.tex) for the theory and
[`treewidth_two_20261008.json`](results/treewidth_two_20261008.json) for raw
measurements. The general subexponential recognition goal remains open.

New RIII trace entries include `triangle`, the three dart indices of the
chosen face in the original input diagram. Crossing indices alone can name
two different legal faces. Replay validates the specified face and accepts
older crossing-only RIII records only when the face is unambiguous. R1/R2
records retain their existing format.

The report 27 causal RIII search is available with `r3_search="clustered"`
or `--r3-search clustered`. It tracks the union of all touched darts and admits
up to `r3_births` independent starting moves (default 1). `r3_search="adaptive"`
first gives the historical search half the remaining trial allowance, then
switches to clustered search if stalled. Both share `r3_budget` trials per
input crossing (default 10); `None` disables the total cap in Python. The
maximum sequence length is `r3_depth` (default 4). For example:

```sh
python -m fastunknot recognize examples/hard_unknot_8.json --r3-search adaptive --r3-depth 6
```

Speculative branches roll back on interruption. Local trial exhaustion falls
back to exact recognition; a global deadline yields `UNKNOWN`. If an unfiltered
root search finds no legal RIII move, the simplifier skips further deepening
and switching because no RIII sequence can start. The default remains `last`:
the new modes did not improve crossing counts in the recorded random-diagram
audit and sometimes left more crossings under the same trial cap. Greater
depth helps two stored hard unknots independently of the clustered algorithm.
See `benchmark_causal_r3.py` for paired recognition/simplifier measurements
and its `--discovery` mode for reproducible search and exact legacy-trace checks.

The incoming radical-transfer report contributes exact binary prediction of
the objects surviving cancellation. `--reduction adaptive` (Python:
`reduction="adaptive"`) starts sparse cancellation and switches to that
prediction after its per-stage Schur-update allowance is exceeded. If the
survivors have no adjacent degrees, or the boundary is closed, their zero
differential is constructed directly. Otherwise cancellation resumes from
the saved partial complex. This works in both recognition and raw homology;
it requires the standard backend, minfill, bits, and race=1. It is distinct
from `--no-reduction`, which disables Reidemeister simplification.

`--reduction residue` predicts eagerly and is retained for comparison;
`--reduction standard` remains the default. The switch counters and ordinary
work counters are recorded in scan evidence. Dense two-term test complexes
benefit greatly, but eager prediction slows ordinary diagram scans, and no
general recognition or complexity improvement is claimed. See
[`../synthesis/radical.tex`](../synthesis/radical.tex) for the correctness proof,
the adaptive policy, and the incoming report's stronger hypotheses.
Run `python benchmark_residue.py --output results/residue_local.json` to
compare standard, eager, and adaptive modes with paired controls.

The later dense-algebra report adds a verified homogeneous multiplication path
inside component contraction. Inputs of a single dot degree use a binary subset
transform with a cardinality filter; products in the top degree use a packed
complementary-subset inner product. Mixed inputs retain the ranked transform.
The current scanner's erased quantum shifts were recovered and checked on 520
scans (196,928 entries). This also sharpens the article's sufficient sharing bound.
Use `benchmark_homogeneous.py` and `audit_grading.py`, each with `--output FILE`,
to reproduce the local measurements and checks. The same contraction options
apply; the default sparse engine is unchanged.

The mixed-degree synthetic matrices in the original adaptive benchmark cannot
be genuine scan differentials. `benchmark_adaptive_graded.py --output FILE`
adds dense scalar matrices satisfying the recovered grading constraint, with
local adaptive gains of 2.7–58.5×. These are still synthetic complexes, not a
claim that the current crossing order produces that density. Ordinary forced
component scans show mixed timing results, so these measurements do not justify
changing the default engine. Full proofs and results are in
[`../synthesis/homogeneous.tex`](../synthesis/homogeneous.tex).

Report 08 adds complete recognition for checked source braids on at most three
strands. `Diagram.from_braid` and braid JSON retain validated provenance, so the
pipeline uses a linear symbolic decision before the Seifert stage. The raw-word
API `braid_certificate(strands, word)` avoids PD construction. For more strands,
the initial stage supplies a writhe obstruction; optional checked endpoint
destabilization runs after the cheaper diagram and structural tests.
Use `--no-braid`, `--braid-backend matrix`, or `--no-braid-reduction` to control
these stages (API: `use_braid`, `braid_backend`, `use_braid_reduction`). A PD-only
input never acquires an unchecked source word. `to_json(preserve_braid=True)`
explicitly retains provenance; default JSON stays PD. The specialization does
not give a general quasi-polynomial algorithm.

`benchmark_braid.py` measures fresh diagram construction plus recognition
against the current Seifert-enabled pipeline with braid dispatch disabled.
The local nine-round data in `results/braid_integration_20261007.json` show
3.30–4.89× gains on five scrambled three-braid unknots with default RIII enabled,
1.23–1.35× on positive three-braids, and 6.14× on the hard eight-crossing fixture.
A 256-strand stabilization control is about 2.8% slower. Import/startup and JSON
parsing are excluded; the script also records separate raw-word scaling.

Report 09 adds checked Gauss-interlacement factorization as the default visible
sum decomposition, with `connected_sum_factorization` certificate evidence.
Use `factor_backend="legacy"` or `--legacy-factor` for the historical cut traces.
The modular Alexander filter uses sparse elimination at 256 crossings and above;
its low-level API retains explicit `backend="dense"` and `backend="sparse"` choices.
Preprocessing and factorization now share the cooperative `UNKNOWN` resource
handler. Run `benchmark_factor_sparse.py --output results/factor_sparse_local.json`
for isolated paired kernel measurements.

```bash
python3 -m fastunknot recognize examples/trefoil.json
python3 -m fastunknot khovanov examples/conway_sum_8.json --shared
python3 -m unittest discover -s tests -v
```

Recognition accepts `--backend standard|shared|saturated|euler|shadow|closure|twist`
(with the barcode and fitting options described below). The default is
`standard`: sharing incurs overhead on prime examples that stay connected.
`shared` retains exact ranks and raw homological-degree counts. `saturated`
retains the final unreduced rank capped at three. `euler` adds an optional exact
suffix-Euler lower bound, controlled by `--euler-max-states` (default 4096).
A capped count of three means “at least three”; it is never an exact rank.
An early Euler result uses `rank_lower_bound_capped`, distinct from final
`rank_capped`. Exhausting the optional inference budget continues complete
saturated scanning; object/time exhaustion returns `UNKNOWN`.
The Euler backend begins with direct linear-time closure walks. After four
distinct queries at a stage, it prepares strand and zero-smoothing boundary
path summaries when the boundary has no more darts than the suffix has
crossings. Subsequent queries walk only these boundary summaries, computing
the exact raw Euler value as `(-1)**(n+c+c0) * 2**c`. Preparation remains
within the existing deadline and query budget; interrupted summaries are not
published. The query budget counts completed matchings. `ClosureEuler` and
the original `SuffixEuler` recurrence remain independent references.
The low-level `AdaptiveClosureEuler(compression_after=0)` forces eager setup
for diagnostics; public recognition uses the adaptive policy.
`python -B benchmark_boundary.py --output results/boundary_local.json`
separates repeated-query timings from complete scans and recognition.
See `../synthesis/boundary_reuse.tex` for the proof and measured limitations.
`euler_stats.prepared_stages` records the number of prepared stages.
`python benchmark_euler_setup.py --output results/euler_setup_local.json`
measures this setup separately from full recognition, with allocation peaks
measured outside the timing samples.
`python benchmark_euler_connectivity.py --output results/euler_local.json`
compares the raw Euler-assisted scans with the earlier recurrence implementation.

`--backend shadow` adds report 26's marked residue-four continuation bound.
It completes whole relative components with the actual suffix, recovers their
relative quantum shifts, and uses signed Tait determinants to evaluate four
Euler residues. A reduced rank lower bound above one certifies knottedness;
an inconclusive bound continues the exact scan. Only proper prefixes are
observed. A partial observation never certifies the unknot.

```bash
python -B -m fastunknot recognize examples/conway.json --backend shadow --shadow-max-work 1000000
python -B benchmark_shadow.py --output results/shadow_local.json
```

The Euler and determinant caches share `--euler-max-states`. The additional
`--shadow-max-work` allowance counts geometry visits, matrix allocation and
integer arithmetic updates (API: `shadow_max_work=None` removes this local
cap). Exhausting marked work switches to Euler-only observations using the
same exact cache and remaining shared query allowance. These direct Euler
walks are separately counted in `euler_fallback_traversed_darts`; they do not
reset or consume the spent marked-work counter. Exhausting the query cap then
continues the same saturated scan without observations. Global exhaustion
remains `UNKNOWN`. Thus `--shadow-max-work 0` permits Euler fallback, while
`--euler-max-states 0` disables all new completion queries.
`shadow_stats.observer_mode` reports `shadow`, `euler`, or `scan`; the result
also distinguishes `shadow_exhausted` and `euler_exhausted`. Completed
determinant values alone are cached, so interruption cannot publish a partial result. Early evidence
uses `reduced_rank_lower_bound_capped`, `stage`, and `shadow_stats`; the final
rank still uses `rank_capped`. The existing backend restrictions apply.
`python -B benchmark_shadow_fallback.py --output results/shadow_fallback_local.json`
compares the schedulers on complete raw scans and recognition, including low
budgets and supplied-order controls. See `../synthesis/shadow_fallback.tex`
for the exact resource contract, transition proof, and measurements.

Larger completed Tait graphs now factor at articulation vertices before dense
matrix allocation. Parallel signed weights are combined first; cancelled edges
may give a zero tree sum. Bridge blocks contribute their weights, and other
blocks use the existing exact Bareiss determinant. The original crossing phase
is retained, including loops. Cofactors through size 16 keep direct evaluation.
`shadow_stats` distinguishes `max_unsplit_cofactor_size` from the largest actual
`max_cofactor_size` and reports `tait_blocks`, `tait_bridge_factors`,
`tait_block_determinants`, `tait_disconnected`, and `tait_zero_factors`.
All work remains interruptible and locally budgeted; partial products are never
cached. `python -B benchmark_tait_blocks.py --output results/tait_blocks_local.json`
records actual observer traces and separates initial queries, raw scans, and
complete recognition. See `../synthesis/tait_blocks.tex` for the signed product
proof, cutoff measurements, and remaining complexity limits.

The default stays `standard`: earlier filters already decide many examples
where the raw marked scanner improves substantially. The paired benchmark
separates complete recognition from raw scanner timings. The theory and
validation are in `../synthesis/determinant_continuations.tex`. The common
terminal graph producer in `determinant_research/terminal_geometry_audit.py`
is a checked research prototype; production computes each completion directly.
The newer `determinant_research/boundary_tait.py` uses cut-face fragments and
boundary-only gluing checks, reusing a signed terminal kernel and partition
cache. Its audit agrees on 4,503 actual completions and checks another 3,468
arbitrary pairings. It remains research code: it imports the delivered kernel
and lacks production deadline/work accounting. Isolated repeated-query gains
do not establish a complete-recognizer speedup.

`--backend closure` adds report 28's classical closure bounds and
single-survivor resets. For a whole radical component with one matching, it
reads the scalar first-jet matrices and checks the actual remaining closure.
Pure coefficients also support bounds valid for all classical link closures.
A certified rank above two rejects the knot. When the entire scan has one
component copy and first-jet multiplier one with a knot completion, it splices
that matching into the remaining PD and restarts with fewer crossings. This
preserves total rank; it is not an isotopy certificate or a graded-homology API.

```bash
python -B -m fastunknot recognize examples/conway.json --backend closure --closure-max-work 1000000
python -B benchmark_closure.py --output results/closure_local.json
```

The local work allowance counts optional observer traversal, polynomial
extraction, binary rank operations and completion geometry. Exhaustion disables
observations and continues the current exact capped scan; global exhaustion
still returns `UNKNOWN`. API `closure_max_work=None` removes this local cap.
Evidence records reset events, `segment_stats`, and `closure_stats`, including
the actual maximum segment length `max_gap`. A general polylogarithmic bound
on this gap is unproved. An expanded 624-scan search found singleton resets
but no nonsingleton eligible blocks; algebraic tests cover the broader formula.
See `../synthesis/closure_resets.tex` for proofs, source-audit qualifications,
and separate full-recognition and raw-backend measurements.

Shared backends require minimum-fill pivots, bit algebra, no tail contraction,
and no racing. Incompatible options are rejected. `khovanov --shared` cannot
be combined with `--factor`. Backend selection only matters after enabled
earlier stages have failed to decide; use the disabling flags in the companion
article to isolate a backend deliberately.

The new functions live in `fastunknot.seifert`, `fastunknot.component_scan`,
and `fastunknot.euler_scan`. The Seifert APIs are also exported from `fastunknot`.
Public PD scanner functions assume a validated classical one-component diagram.
The permissive `Diagram(pd)` constructor does not validate this promise; use
`Diagram.from_pd` or the command-line loader.

The maintained article is [`../synthesis/report.pdf`](../synthesis/report.pdf),
with source in `../synthesis/structural.tex`; the delivered report remains in
`../reports/07/paper/`. Run `python benchmark_structural.py --output results/local.json`
for paired recognition timings and exact scanner checks against the integrated code.
`python benchmark_reduction.py --output results/reduction_local.json` isolates
the post-reduction check against the first integrated revision.

The companion article proves exactness and a finite-type complexity bound in
frontier size and actual connected-component size. **There is no general
quasi-polynomial complexity guarantee.** All 69 unit tests passed in the
recorded environment. The research archive includes proofs, raw timing samples,
source provenance, and a patch against the pinned ProveIt baseline.

## Inherited documentation and performance history

The following version-0.2 documentation is retained as the record of the
previous pipeline and measurements. Stage-order descriptions below predate
the new optional and structural stages just described.

# fastunknot 0.2: exact unknot recognition with a scanning Khovanov backend

**Status: exact, complete, and exponential in the worst case. The `n^O(log n)`
bound announced in Lackenby's February 2021 talk is NOT achieved here**, for the
reasons documented in the synthesized report (`../synthesis/`): the accelerated
hierarchy operations in the talk's final flowchart have no published
algorithmic specification with cost bounds.

Version 0.2 integrates the ideas of the nine acceleration proposals in
`../proposals/` that gave a measurable speedup. The 36-crossing braid closure
that version 0.1 abandoned after 600 seconds now takes under a second; full
recognition of the Conway and Kinoshita–Terasaka knots went from about 60 ms to
about 1 ms; a connected sum of three Conway knots from 58 s to 2.5 ms. A Rust
port is in `../rust/`.

## Pipeline

1. **Validation.** One component, spherical rotation system. Inputs: PD code,
   braid word, or rectangular (grid) diagram.
2. **Reidemeister I/II reduction**, incremental: O(1) work per move on a
   mutable dart structure, one revalidation at the end. (A search for
   Reidemeister III moves that unlock further I/II moves runs later, between
   steps 7 and 8, when no filter has decided.)
3. **Descending-diagram test**, linear time; sufficient for `UNKNOT`.
4. **Visible connected sums.** Two edges bordering the same two faces cut the
   diagram into summands. A sum is trivial exactly when every summand is, so
   the summands are examined separately, smallest first.
5. **Modular Alexander test.** The first Alexander minor at t = −1 and at a
   generic element of F_p, p = 2^61 − 1. For the unknot it is ±t^k; anything
   else certifies `KNOTTED`. O(n³) field operations.
6. **Modular Jones test.** The Kauffman bracket at a generic A in F_p by a
   frontier scan that merges partial states with equal boundary matchings.
   Cost is bounded by all perfect matchings of the scan
   boundary, `(w-1)!!` (no multiplicity factor). A Catalan bound requires
   a certified common disk boundary, which the current order does not supply. Skipped above 4096 frontier
   states. Rejects knots with trivial Alexander polynomial such as the Conway
   knot.
7. **Exact Alexander polynomial** over Z[t] (fraction-free Bareiss).
8. **Reduced Khovanov rank over F2** by Bar-Natan scanning with delooping and
   Gaussian elimination: bit-packed morphisms, compiled gluing plans, min-fill
   (Markowitz) pivots, units treated as involutions. `UNKNOT` iff the reduced
   rank is 1 (Kronheimer–Mrowka plus universal coefficients).

Every verdict is exact. Filters 5–7 can only say `KNOTTED`; agreeing with the
unknot's value is never evidence of triviality, and an exhausted filter budget
just skips the filter. Optional ceilings (`--max-objects`, `--seconds`) turn an
expensive step 8 into `UNKNOWN`, never into a knot verdict.

## Run

Python 3.10+, standard library only. From this directory:

```sh
python -m fastunknot recognize examples/conway.json
python -m fastunknot recognize examples/conway_sum_3.json --no-jones
python -m fastunknot recognize examples/hard_unknot_8.json --check-d2
python -m fastunknot khovanov examples/stress_braid5_36.json
python -m fastunknot khovanov examples/conway_sum_8.json --factor
python -m fastunknot jones examples/kinoshita_terasaka.json
python -m fastunknot alexander examples/figure_eight.json
python -m unittest discover -s tests -v
python ablation.py        # about 40 minutes: the LIFO rows hit their 300 s caps
python crosscheck.py 400  # default scanner against the generic and the 0.1 scanners on random closures
python ab.py HEAD         # interleaved A/B timing of the working tree against a git revision
python perf.py label      # sequential best-of-N timing with a control loop; see the caveat below
python cli_ab.py HEAD     # whole-process timing of the command line against a git revision
python hard_unknots.py    # scrambled unknot braids that no filter decides (pipeline timing inputs)
```

Exit codes: 0 for either exact verdict, 2 for invalid input, 3 for `UNKNOWN`.

Switches of `recognize`: `--no-reduction`, `--no-descending`, `--no-factor`,
`--no-alexander` (both Alexander stages), `--no-modular` (only the modular
one), `--no-jones`, `--jones-max-states N`, `--pivot {minfill,lifo}`,
`--algebra {bits,sets}`, `--tail N`, `--max-objects N`, `--seconds S`,
`--check-d2`. `khovanov` takes `--factor`, `--pivot`, `--algebra`, `--tail`,
`--check-d2`. `--algebra sets --pivot lifo` reproduces the 0.1 scanner.

## Input

```json
{"pd": [[1,4,2,5], [3,6,4,1], [5,2,6,3]]}
{"braid": {"strands": 3, "word": [1, -2, 1, -2]}}
{"rows": [[0, 2], [1, 3], [2, 4], [0, 3], [1, 4]]}
```

PD crossings are counterclockwise `[a,b,c,d]` with the under-strand `a-c`
(either under-port may come first). Grid rows are listed bottom to top;
verticals pass over horizontals. `{"pd": []}` is one crossing-free circle.

## Complexity

* Steps 1–5 and 7: polynomial in the crossing number n.
* Step 6: at most n · (w-1)!! · poly(w) field operations for scan width w.
  The older unconditional Catalan claim was refuted by report 09; it requires
  a certified disk frontier.
* Step 4 with step 8: if the visible factors have n_1, …, n_k crossings, the
  cost is poly(n) + Σ 2^O(n_i). Polynomial when every factor has O(log n)
  crossings; this is a restricted-class statement, not a bound for all diagrams.
* Step 8 in general: 2^O(n). The size of the complex after elimination is
  (number of boundary matchings) × (a multiplicity that grows with the
  homology of the partial tangle); no subexponential bound is known or claimed.

## Test and benchmark status (last observed 18 September 2026)

* `python -m unittest discover -s tests`: 41 tests, OK (about 9 s; one test starts race processes), about 3 s (CPython
  3.14.4, Windows 11). 19 are the 0.1 tests (three expectations updated because
  a filter now decides before Khovanov does), 22 are new and compare every new
  code path with the 0.1 implementation.
* `results/benchmark_0.1.json` is the 0.1 benchmark, kept as a record; its
  36-crossing 5-strand row is the 600 s timeout that motivated 0.2.
* `results/ablation.json` is the per-idea ablation (see the report). It takes
  about 40 minutes because the LIFO configurations on the stress case run into
  the 300 s cap; shorten the list in `ablation.py` if that matters.
* `python crosscheck.py 400 7`: 400 random braid closures (2 to 5 strands),
  ranks by degree of the default scanner (with `tail` 0 to 2 and `check_d_squared`
  on every fourth) equal to those of the generic scanner, 0 mismatches.
* **Timing caveat, learnt the hard way on 18 September 2026.** On this desktop
  the speed of pure Python drifted by more than a factor of two inside a single
  one-minute run (background applications, clock throttling): a fixed control
  loop went from 5.3 ms to 12 ms. Sequential before/after runs of `perf.py` are
  therefore not evidence. `perf.py` times that control loop next to every case
  and marks a run `SUSPECT` when the control spreads by more than 10%; three
  rows of `results/perf_log.json` are flagged as contaminated. Use `ab.py`,
  which times old and new alternately in one process (`results/ab_log.json`).
  Its first criterion, "interquartile range of new/old entirely below 1", was
  too lenient and **gave false claims in both directions**: a change confined
  to order selection, which is 0.2 to 1.8% of the affected scans and was
  measured on its own as 32 to 58% faster with identical output, was reported
  as 14% slower on one input and 4% faster on another. `ab.py` now also times
  the old code twice per round (an A/A control; on mid-sized scans identical
  code differed by 20 to 30% between adjacent runs) and claims a difference
  only if the order-statistic 95% confidence interval of the median excludes 1
  and the median lies outside the A/A interquartile range. `python ab.py OLD
  NEW` compares two revisions; the earlier "7 to 13% on small scans" claim
  below was re-tested that way and holds (0.87 to 0.92, intervals within
  0.87..0.95; no claim on the large scans). Deterministic counters are immune to this, but each
  sees only part of the work: `stats["compositions"]` counts elimination work
  and `stats["entries"]` the differential entries written while adding
  crossings. Neither alone predicts time: on the 41-crossing 4-strand closure
  the scan order with the fewest compositions (1565 against 4164, equal peak
  size) was not the faster one.
* Measured and left unchanged (deterministic counters, ranks identical in every
  variant). Pivot rule: the product cost (out-1)(in-1) with last-in-first-out
  inside a cost bucket is best or within 2% on four inputs; first-in-first-out
  needs 64% more compositions on the stress case and the sum cost is worse on
  all four. Scan-order selection: scoring greedy orders by the sum of
  2^(boundary/2) selects the same start crossing as the current (maximum,
  total) rule on all four inputs. On the 31-crossing 6-strand closure another
  start needs a tenth of the compositions, but its boundary profile is worse
  than the selected one, so no boundary-based score can find it. On the stress
  case 16 of the 36 greedy starts finish within 4 s; starts 14 to 16 tie for the
  least work (23710 compositions) and the default, which scores every third
  start, selects 15. The score is a fragile predictor: start 0 has profile
  (8, 230) against the winners' (8, 226) and needs 895182 compositions, 38
  times more, with 2.6 times the peak size.
  Scoring all greedy starts instead of 12 was tried on 40 random closures (25 to
  39 crossings, 3 to 6 strands; work = entries + compositions): a different
  order in 18, of which 8 with equal work, 6 cheaper, 4 dearer, ratios from
  0.29 to 6.69, total 0.952. Not adopted: the total is carried by three inputs
  and would change sign without one of them. The weak point is the score, not
  the number of starts. A matchings-only simulation cannot replace it: the
  38-fold gap above occurs at equal boundary size (at most 14 matchings), so it
  is all multiplicity, i.e. homology of the partial tangle.
* Where the transfer work goes (four inputs): 74 to 83% of the differential
  entries are incident to a cancelled pair when it is cancelled (an
  overestimate, since fill-in entries are counted but not in the denominator).
  Only 30 to 53% of the cancellations are between the two smoothings of one old
  object, the kind that could be predicted before writing any entries; the rest
  are between different old objects.
* Outside the scanner (`ab.py`, strict criterion, against c9572d2): the modular
  Alexander filter now evaluates only the nonzero matrix entries, at most three
  per row (`recognize T(3,61)` 0.60, interval 0.53..0.67; `recognize conway`
  0.92); the boundary profile of a greedy scan order is tracked inside the
  greedy in O(1) per step and a candidate start is abandoned once it cannot
  win (`scan chain256` 0.78, interval 0.73..0.82). Both are output-preserving:
  same determinants, and identical greedy orders, profiles and selected orders
  on 600 random diagrams (19993 start orders, 34 diagrams with loop edges).
* The Jones frontier scan now uses the interned matchings and strand-following
  gluing of `planar.py` instead of a union-find over labels per transition:
  0.67 (interval 0.46..0.72, 10 rounds) on the 36-crossing closure, where the
  scan is a few milliseconds. **No measurable effect on any `recognize` case of
  the corpus**, including the Conway knot, which this filter decides: with 11
  crossings the filter is a small part of 0.6 ms. Output-preserving: identical
  return values on 500 random closures (350 witnesses with equal bracket, peak
  states and transitions; 122 inconclusive; 28 identical budget failures; 48
  diagrams with loop edges). `filters._glue` is kept as the reference.
* The Alexander matrix is now built by sparse rows (`alexander_rows`); the dense
  `alexander_matrix` of the exact path derives from it, and the modular filter
  fills a zero matrix directly, evaluating each distinct entry polynomial once:
  `recognize T(3,61)` 0.69 (interval 0.62..0.72) on top of the 0.60 above, no
  claim on the small diagrams. Output-preserving: dense matrices, filter
  results and exact polynomials identical on 500 random closures (35 with
  kinks, where entries of one row coincide and can cancel).
* **Cross-stage plan cache (`shape_cache`, on by default; a trade-off, not a free
  win).** Every crossing brings new edge labels, so a per-stage cache never
  hits across stages, yet a long braid compiles the same few pictures at every
  crossing (at boundary 6 there are 5 matchings, and about 35 transfer plans
  were compiled per crossing of T(3,n)). Transfer plans are now also cached
  under a label-independent key (matchings and crossing slots relabelled by
  rank). This is sound because relabelling by rank is monotone and the circle
  numbering is by minimal label whichever matching is walked first (tested on
  random matchings, and on 20000 pairs while developing). Reuse: 80% of the
  plans of T(3,11), 94% of T(3,31), 72% of T(4,9), 99% of the kink chain, 38%
  and 19% of the random 3- and 4-strand closures, but 1% of the stress closure
  and 0% of the Conway knot, Kinoshita-Terasaka and Conway#Conway. `ab.py`,
  three runs agreeing: `scan T(3,11)` 0.61 (interval 0.59..0.66), `scan
  chain256` 0.78, `scan braid3_40` 0.97; **`scan conway` 1.06 (interval
  1.04..1.07 with 301 pairs) and `recognize hard_unknot_8` 1.07, slower**; no
  claim on the large scans. The cost was decomposed by timing partial variants
  against HEAD (A/A 0.999): ranking the boundary each stage +1.5%, building the
  key and looking it up +3.0%, storing +1.3%. Two explanations I had offered
  first were wrong and are recorded as such: hashing of nested tuples
  (interning shapes as integers changed nothing) and the cyclic garbage
  collector (same ratio with it disabled). Inlining the lookup changed nothing
  either; `shape_cache=False` restores the old speed exactly (1.003).
  **Correction, same day.** I first wrote here that an automatic switch was
  impossible, having tested one predictor: an early hit count predicts the
  wrong way (inputs that profit get their first hit after 35 to 150 lookups,
  the stress closure gets 12 hits in its first 64 and then none). A different
  predictor works. A plan can only be reused in a stage whose picture (the
  position of the four crossing slots among the boundary points, up to monotone
  relabelling) occurred before, and that is known from the scan order alone:
  `ordering.repeated_stages` gives 0 for the Conway knot, Kinoshita-Terasaka
  and Conway#Conway, 1 of 36 for the stress closure, 4 of 31 and 11 of 41 for
  the 6- and 4-strand closures, 16 of 40 for the 3-strand closure, 16 of 22
  for T(3,11). `shape_cache=None`, now the default, turns the cache on when the
  diagram has at least 16 crossings and at least an eighth of them repeat.
  Transfer and composition *results* are shared across stages as well, but only
  after the first plan-shape hit of the scan, since before that a shared
  result cannot exist (ungated this cost a further 2.6%, intervals
  1.023..1.029). Against the code before any of this (1ca6a5d), 301 pairs:
  `scan T(3,11)` 0.505 (0.486..0.508), Conway 1.008 (1.005..1.010), hard
  unknot 1.007; `ab.py`: T(3,11) 0.51, `scan chain256` 0.81, nothing slower.
* **The exact Alexander polynomial is no longer computed after the modular test
  has passed** (`use_exact_alexander=None`; `True` or `--exact-alexander`
  restores it; with `use_modular=False` it still runs). It can only say
  `KNOTTED`, and only for a polynomial that is not a unit, which the modular
  test has just failed to see at two points; whatever it would have caught the
  exact scan decides anyway, so verdicts cannot change. The corpus had a single
  filter-undecided input, of 8 crossings, which hid this stage's cost:
  `hard_unknots.py` now generates scrambled unknot braids, about half of which
  survive R1/R2 with 15 to 27 crossings and pass every filter. On 26 of them
  the exact polynomial took a median 24% (up to 63%) of `recognize`. Over 720
  diagrams (600 random closures, 120 scrambled unknots) the two modes never
  disagree and the exact stage decided nothing once the modular test had
  passed. `recognize` on the 55 scan-decided scrambled unknots: faster on all
  55, median 0.81, range 0.53 to 0.93; `ab.py`: 0.62, 0.84, 0.85 on three of
  them, `hard_unknot_8` 0.86. The evidence record says "not computed" instead
  of giving the polynomial and the determinant.
* A caveat on `ab.py` even with the strict criterion: that run flagged
  `recognize conway` as 1.05 slower (interval 1.005..1.254), a path this change
  cannot reach. 301 pairs gave 1.006 (1.000..1.015). With some 15 comparisons
  per run at 95%, expect an occasional false flag on sub-millisecond cases and
  confirm a flag with a few hundred pairs before acting on it.
* Tried and reverted: computing the fill-in terms of a pivot once per kind of
  source. Between 5 and 52% of the sources of a pivot share matching and value
  with another source (52% on the stress closure), so their terms coincide.
  With 151 interleaved pairs it was slower on every input: 1.075 (scrambled
  unknot, 25 crossings), 1.031, 1.043, 1.019, and 1.026 on the stress closure,
  all intervals above 1. Building the lists costs more than the sharing saves.
* `recognize` computes the greedy scan order once and hands it to both the Jones
  scan and the Khovanov scan, which used to compute the same order twice.
  Results identical to the previous code on 400 diagrams, evidence records
  included. 151 pairs: 0.943 (0.923..0.964) and 0.945 (0.936..0.955) on two
  scrambled unknots of about 10 ms; on a 40 ms one 1.029 against an A/A of 1.019
  in the same run, i.e. no difference (the change removes about 0.7% there).
  That A/A reading is itself a lesson: the second run of the old code comes last
  in every round and can be biased by a percent or two, so compare a ratio with
  its own A/A, not with 1.
* Scan orders again, now on 81 diagrams (36 scrambled unknots, 45 random
  closures of 20 to 35 crossings) and with work = entries + compositions.
  The greedy rule breaks ties by crossing index. Breaking them towards the most
  recently touched crossing costs 1.09 (unknots) and 1.05 (random) of the
  current total; towards the longest-waiting one 1.52 and 1.57. Not adopted.
  Per diagram the ratios run from 0.01 to 28, better on about as many inputs
  as worse: the rules are incomparable, not ranked. A portfolio does not
  rescue this: the best of the three rules per diagram would need 0.31 of the
  work on the unknots and 0.74 overall, but running them interleaved until the
  first finishes costs three times the winner, 0.94 on the unknots and 2.2
  overall, because 8 of the 81 inputs carry 86% of the work and there the
  rules are within a factor two. Only a predictor would collect that prize.
* **Reidemeister III help for the reduction (`simplify(d, r3=True)`,
  `recognize(use_r3=True)`, `--no-r3`).** The scan is exponential in what the
  reduction leaves, and the reduction stopped wherever a Reidemeister III move
  was needed. A triangular face is a 3-cycle of the face walk through three
  crossings; it can be inverted iff some side is over at both ends; inverting
  it reverses the order in which each of the three strands meets the other two,
  a relinking of at most twelve darts that keeps every crossing's slots and the
  direction of both strands through it, hence its sign. When no I/II move is
  left, each such triangle is inverted on trial, kept if that creates a I/II
  move and undone otherwise (the move is an involution); triangles with no
  small face across a side are skipped, which never changes the result (2120
  diagrams, identical traces). Tested on its own: 150 random moves give valid
  spherical diagrams with the same Alexander polynomial, writhe and Khovanov
  ranks by degree, and a second move restores the dart structure exactly (300
  of 300). On 1500 random closures: never more crossings than I/II alone, no
  I/II move left, every trace replays, Alexander polynomial and Khovanov rank
  unchanged; 26% of the diagrams shrink further, 0.80 of the crossings remain.
  `hard_unknot_8` goes from 6 crossings to 0. Verdicts with and without it
  agree on 900 diagrams.
  *Placement matters.* Run with the first reduction it cost 58% on T(3,61), 20%
  on a random 5-strand closure and 4 to 6% on the Conway knot, inputs a filter
  decides a moment later. It now runs only after every filter has failed,
  just before the scan: no claim of any slowdown on those inputs, `recognize
  hard_unknot_8` 0.48, a scrambled unknot of 27 crossings 0.18.
  *Fewer crossings is not always less work.* One survivor was flagged 1.43
  slower, correctly: R3 help takes it from 22 to 20 crossings and its scan work
  from 2081 to 3277. Over the 54 of 117 survivors where crossings are removed
  (3.4 on average) the scan work is 0.43 of before, cheaper on 44 and dearer on
  10, per-diagram ratios 0.03 to 7.3; over all 117 it is 0.69.
* **Deeper III search, budgeted.** One move of lookahead left 117 unknot
  diagrams (of 40000 random closures) untouched; sequences of two moves, the
  second next to the first, reduce 97 of them to nothing, three moves 109, four
  moves 110, with no violation at any depth (no I/II move left, traces replay,
  Alexander polynomial and unknot rank preserved). A failing search is what
  costs: on T(3,61), full of triangles that lead nowhere, depths 1 to 4 take
  2, 10, 44 and 189 ms. Useful sequences are found early, so the search is
  introspective about its own cost: it deepens only while fewer than
  `r3_budget` trial moves per crossing have been made. Budgets of 5, 15, 40 and
  none give the same 97 / 109 / 110, while a budget of 5 caps the T(3,61) case
  at 10 ms. Defaults: depth 4, budget 10. With them only 15 of 60000 random
  closures are unknots that survive the reduction (largest: 16 crossings).
* **Introspective algorithm selection (the introsort idea), measured.** It
  works where a cheap signal separates the populations and switching is free,
  and three parts of the package now are of that kind: the shape cache chosen
  from the scan order, result sharing enabled by the first plan hit, and the
  budgeted deepening above. For scan *orders* it does not work with the rules
  at hand, in either form. (a) Run the default order under a work budget, on
  overrun restart with another tie-break rule, grow the budget: simulated
  exactly on the saved work of three rules on 81 diagrams, 27 policies, every
  one costs 1.4 to 4.8 times the default. Introsort can switch because heapsort
  has a guarantee and recursion depth signals degeneracy; here no rule has a
  guarantee, expensive is not degenerate (on the 8 inputs with 86% of the work
  all rules are within a factor two), and an abandoned scan is lost. (b) No
  restart: `add_crossing` does not mutate the previous stage, so tied greedy
  candidates can each be tried from the same state and the smallest real
  complex kept. With all trial work counted: 0.41 on the scrambled unknots
  (median per diagram 1.02, dearer on 21 of 36) but 1.44 to 1.52 on random
  closures, 1.40 to 1.47 overall. The size of the complex now does not predict
  the cost of the choice later.
* **Racing orders in parallel** is where that data does promise something: by
  wall clock on separate cores the race costs the winner's time, and the best
  of two rules is 0.75 of the default on the expensive inputs (single inputs
  0.07, 0.24, 0.30). Not in Python, though: a competitor must be a process, and
  starting one costs 30 ms bare, 76 ms with the package imported, 111 ms for a
  complete CLI scan of the trefoil, against scans that mostly finish within
  300 ms. So it was built in the Rust version (`../rust`, `--race N`), where a
  thread costs microseconds. Measured there on 40 random closures with single
  scans of 30 ms to 8 s: racing two orders takes 0.650 of the total time, three
  0.689; per input 0.05 to 1.68 (6.8 s becomes 0.34 s), faster on half and 10
  to 60% slower where the default order was best anyway. That premium is
  hardware contention, not the allocator: separate processes slow each other
  just as much as threads. Details in `../rust/README.md`.
* **A race in Python after all (`race=N`, `race_after=1.0`; `--race`,
  `--race-after`; off by default).** Dismissing it because a process costs 0.1 s
  to start compared that cost with the typical scan; but the race only matters
  on the heavy tail, where Python scans take seconds to minutes. So the default
  order runs alone for `race_after` seconds, and only then are other greedy
  orders (tie rules `oldest`, `recent`; `ordering.best_scan_order(ties=...)`)
  started as `python -m fastunknot _scan` processes with JSON over pipes (no
  `multiprocessing`, which on Windows imports the caller's main module again).
  The scanner polls them where it looks at the clock; the first to finish wins,
  the rest are killed, and rank and ranks by degree are the same whoever wins
  (tested, including a win of a competitor against a handicapped default order,
  and that no worker is left running).
  Measured on 26 random closures with single scans of 0.15 to 3.6 s, three
  interleaved rounds (`results/race_eval_python.json`): total 0.910 of single
  with two orders, 0.925 with three. What that total is made of: a competitor
  won on 2 inputs, 3.22 s to 1.74 s and 3.55 s to 1.56 s, in every round and
  under both settings; on scans of 1 to 3 s that the default order wins the
  race costs 10 to 20%, the hardware contention seen in Rust. The other
  per-input ratios are noise and the data shows it: 18 inputs finish inside the
  head start, where nothing is started and the ratio must be 1, and they read
  0.80 to 1.43. Measured properly (61 interleaved pairs on the 0.25 s stress
  scan) an armed race that starts nothing costs 1.010, interval 0.984..1.041,
  with the A/A control at 1.042: nothing. It is insurance against a bad order on
  long scans; use `race=2`.
* `hard_unknots.py`: the scrambled family turned out weak, since its rewriting
  consists of Reidemeister III moves and the helped reduction undoes all of
  it (120 of 120; 180 of 180 with heavier scrambling). `SURVIVORS` lists unknot
  diagrams of 11 to 16 crossings found by random search that survive I, II, the
  default III search and every filter; they are the honest scan-decided inputs.
* **Start-up: a whole command-line run takes 0.52 of the time** (`python cli_ab.py`,
  41 interleaved pairs of whole processes, `results/cli_ab_log.json`): `recognize
  conway.json` 115.5 to 60.9 ms (interval 0.510..0.541), `hard_unknot_8` 0.523,
  `unknot_braid40` 0.530, `khovanov trefoil` 0.523, and still 0.856 on the
  half-second stress scan. The bare interpreter is 29.5 ms of that, so the
  package's own start-up went from about 86 to about 31 ms; for a command-line
  user that is more than every scanner optimization above, which save well
  under a millisecond on such inputs. Where it went: `import fastunknot` took
  56 ms, 25 of them for `dataclasses` (it loads `inspect`, `re`, `dis`, `ast`,
  `tokenize`) used for five simple records, now written out by hand with the
  same constructors, equality, hashing, immutability and `repr` (and they
  pickle and deep-copy); 9 ms for `subprocess` and `json`, needed only when a
  race starts; 5 ms for `typing`, used only in annotations that are never
  evaluated; the 0.1 reference scanner, needed only by the ablation
  configurations, is imported on demand. Then `argparse`: 55 to 59 ms in Python
  3.14, where it loads `_colorize`, `dataclasses` again and `shutil`
  (`color=False` does not help). The options are now one table that feeds a
  small direct parser for the well-formed common case and, on demand, the real
  `argparse` parser for everything else (help, errors, abbreviated flags,
  `--flag=value`, values that look like flags), so messages and help are
  argparse's own; tests check that the two agree wherever the fast one
  accepts, and that start-up loads none of those modules.
  Two measurement notes. My first two whole-process comparisons showed "no
  difference" and were invalid: `python -m` puts the current directory first on
  `sys.path`, and both arms ran from the working tree, so the working tree was
  compared with itself; `cli_ab.py` runs each arm from its own directory and
  checks which package it imports. And the absolute milliseconds of different
  rows are not comparable: the same command read 61 ms and, ten minutes later,
  100 ms; only the paired ratio within a row is robust.
* Three small things found by profiling `recognize` on the Conway knot by
  cumulative time: the Jones filter's `Planar` paid for shape-cache bookkeeping
  it never uses (9% of the call); `simplify` rebuilt and revalidated the diagram
  even when no move applied (12%; an unreduced diagram now keeps its own edge
  labels, where the rebuild renamed them by first appearance, and `replay` does
  the same for an empty trace); `Diagram.alpha()` was recomputed seven times
  per recognition although the diagram is immutable (now cached with `faces`
  and `traversal`; callers get copies, the caches are not pickled and do not
  affect equality). `ab.py`, strict criterion, against 3a86e0c: `recognize`
  Conway 0.765 (0.733..0.794), T(3,61) 0.759, Conway#Conway#Conway 0.731,
  random 5-strand closure 0.865, hard unknot 0.896, scrambled unknot 0.906; no
  claim on the three scan-dominated survivors. Status, method, reduced size and
  rank identical to the previous code on 700 diagrams.
* The most common input, a reducible closure that the Alexander filter decides:
  `simplify` was half of `recognize` there, and half of that was
  `Diagram.from_pd` validating the rebuilt diagram from scratch. What the moves
  could break is the topology, so `rebuild` now checks that directly on the
  darts (one traversal through every crossing twice; the face walk closing into
  n + 2 faces) and builds the diagram from rows that are normalized by
  construction. Reduced diagrams and traces identical to the previous code on
  1500 diagrams in both modes; of 282 deliberately corrupted dart structures
  273 are rejected and the other 9 also pass the full validation (a random
  reconnection is sometimes a legitimate diagram). Also, the Alexander rows skip
  the polynomial addition when a slot is empty, the usual case. `ab.py`
  (strict): `recognize` random 5-strand closure 0.796 (0.772..0.831), hard
  unknot 0.913; no claim where nothing is reduced.
* Kept but not claimed: the face walk written out with bit operations in
  `move_at` (called 168 times in a typical recognition). Identical reduced
  diagrams and traces on 1500 diagrams; `ab.py` medians 0.98 to 0.99, every
  interval reaching 1.
* `tail` re-tested on the current scanner (41 interleaved pairs per input, 15 on the
  stress closure, ratio to `tail=0`, ranks by degree asserted equal): `tail=1`
  0.94 to 1.01 on eight inputs, the interval excluding 1 on two of them (Conway
  0.947, stress 0.971) and no A/A control behind it; `tail=2` 0.98 to 1.60;
  `tail=3` 1.03 to 3.04. The default stays 0, as after the 0.2 ablation.
* `seconds=` fidelity: the default scanner overshot a 1 s budget by up to
  0.24 s because a crossing was added without checking the clock; with a check
  every 512 objects the overshoot is at most 0.03 s on the same runs.
* Post-0.2 scanner work (commits 24b6111, 2e3fef7, e34c9e8), `perf.py` totals:
  1022 ms (0.2) to 602 ms (`FastScan`) to 412 ms (integer geometry). Those six
  runs predate the control loop; what supports them is that the one case the
  changes did not touch (`jones braid5_36`) stayed within 2.63 to 2.73 ms
  throughout. The later geometry refinements are 7 to 13% on small scans by
  `ab.py` and **not measurable on the large scans**. One idea was measured and
  rejected: queuing only the cheapest pivot candidate per source object cut
  queue traffic but raised compositions on the stress case from 29k to 42k.
* Same-machine comparison with the nine proposals:
  `../synthesis/data/proposals_bench*.json`.
* Pitfall for anyone writing random tests: a braid word of even length on an
  even number of strands induces an even permutation and never closes to a
  knot, so a "draw until one-component" loop with such parameters never ends.

## Layout

`fastunknot/diagram.py` (validation, braids, grids, signs), `simplify.py`
(incremental R1/R2, descending test, 0.1 versions as oracles), `ordering.py`
(heap-based greedy scan order), `factor.py` (visible connected sums),
`filters.py` (modular Alexander and Jones tests), `alexander.py` (exact
polynomial), `geometry.py` (matchings, gluing a crossing), `algebra.py`
(bit-packed cobordism algebra), `scan.py` (entry point `khovanov_rank` and the
generic scanner used by the ablation configurations), `scan_fast.py` (the
default scanner: list storage, interned matchings, bucket-queue min-fill),
`planar.py` (its integer geometry and compiled plans), `scan_reference.py` (the
0.1 scanner, unchanged), `recognize.py` (pipeline), `__main__.py` (CLI).
MIT-0, see the repository root.

The default planar algebra also short-circuits typed identities and scalar
squares over its square-free F2 ring. These identities agree with the original
cobordism evaluator; they do not apply to arbitrary morphisms or matrix blocks.
`benchmark_planar_shortcuts.py` records raw scan and separate scalar-kernel
timings. Ordinary scans showed negligible timing impact because most identities
are already removed by the scanner. Report 12's component contraction is now integrated as an opt-in production
option; the standard engine remains the default.

### Optional component contraction

Both `recognize` and `khovanov_rank` accept `composition="component"` (adaptive)
or `composition="component-dense"` (forced ranked subset convolution).
The CLI flag is `--composition`. This contracts morphisms through the connected
components of their compiled gluing plan without changing any differential.
On a boundary of `w` points the dense operation has `poly(w) * 2^(w/2)` bit cost;
the number of chain objects and operations still has no general quasi-polynomial
bound. Standard min-fill/bit scanning and `race=1` are required; shared backends
are not yet wired to this option.

```bash
python -m fastunknot khovanov examples/conway.json --composition component --check-d2
python -m fastunknot recognize examples/conway.json --composition component-dense
```

Earlier recognition filters still take priority. `composition_max_variables=18`
(CLI `--composition-max-variables`) caps component/output variables on selected
allocations. Recognition returns `UNKNOWN` if this limit is exceeded; the raw
Python rank API raises a resource exception. The CLI reports resource exhaustion
with exit code 3. `composition_stats` exposes actual use of the new method.
The advanced fresh-scanner installer is in `fastunknot.component_algebra`.

`benchmark_component_algebra.py` separates full raw scans from dense and sparse
kernel measurements. Local seven-round data show about 38× for independent dense
ten-variable products, 183× for nearly equal dense products using polarization,
and about 44× slowdown when a sparse ten-variable product is forced through the
dense method. None of the six ordinary scan cases selected an adaptive factored
call. Those results justify the explicit option, not a default switch. The raw
samples and A/A controls are in `results/component_algebra_20261007.json`.


### Optional twist compression

Report 11 is integrated through `--backend twist` or `backend="twist"`.
Existing cheap certificates and filters retain priority. After they fail, a
checked source braid is grouped into maximal equal signed runs and evaluated
using the exact reduced twist macro complex. Its complete uncapped bound is
`poly(n) * 2^O(t log(2+n/t))`, where `n` is the expanded crossing count and `t`
is the number of runs in the supplied word. This is quasi-polynomial for
`t = O(log n)`; there is no general conversion to such a presentation.

```bash
python -m fastunknot recognize examples/hard_unknot_8.json --backend twist
python -m fastunknot khovanov examples/trefoil.json --twist --check-d2
python -m fastunknot.twist examples/trefoil.json --mode estimate --profile
```

The direct Python rank entry point is
`fastunknot.twist_adapter.twist_khovanov_rank(diagram, budget=Budget(...))`,
with `Budget` from `fastunknot.twist`. Advanced signed-run homology and estimates
are available there too. Binary run exponents do not change the expanded-size
complexity convention. The main Diagram input still expects an explicit word.

PD and grid recognition fall back to the standard scanner when no checked
source braid exists. Proper connected-sum factors never inherit the original
source word: cheap factor tests run first, then unresolved factors defer to
one computation on the whole original braid. Such factors carry
`twist_deferred` evidence. The whole-knot rank is recorded only at the top level.
This preserves the restricted run-count bound for source-braid inputs.
The raw twist-rank API rejects missing provenance instead of falling back.

An exact Temperley–Lieb basis count precedes assembly. Recognition exposes
`twist_max_basis` (CLI `--twist-max-basis`, default one million); the raw `Budget`
also controls macro states, matrix bits, XORs, and time. Preflight and assembly
share a deadline. Exhaustion returns `UNKNOWN` in recognition and the CLI;
the production Python adapter raises `ScanLimit` or `MemoryError`. These
limits are separate from the ordinary scanner's object ceiling.

Raw degree output is converted to the original source braid's cube grading,
with `grading_diagram` and `source_crossings` identifying it explicitly. This
remains the original grading after whole-diagram simplification. Macro reduced
degrees are also retained. Assembly and degree-profile estimates report the
peak degree dimension, matrix-bit bound, and a degree-sensitive XOR-bit bound.

`benchmark_twist.py` compares raw homology against the production scanner,
including exact degree equality and A/A controls. The default recognition
pipeline often decides these inputs earlier; raw homology speedups are not
recognition speedups. The theory, restricted-family proof, integration details,
and benchmark limitations are maintained in `../synthesis/twist.tex`.

Local seven-round raw homology gains on two-strand twists are 31.6×, 134.7×,
and 574.4× at 51, 201, and 801 crossings. In a fixed four-strand context, a
single 801-letter block gives a 4.29× gain with peak degree dimension 177.
The alternating no-compression control is about 4.5× slower, and the Morton
four-strand unknot about 15.8× slower. Default recognition already decides the
long examples by the braid obstruction. Full inputs, degree counts, timing
boundaries, and A/A controls are recorded in `results/twist_integration_20261007.json`
and `results/twist_context_scaling_20261007.json`.

### Exact windows and bounded adaptive widening

Report 13's exact moving-window scanner is integrated. A window retains both
adjacent differential degrees and prunes irrelevant objects before allocation.
It can choose the mirror with the smaller proved object bound. The dedicated
command returns partial ranks, never an unknot verdict from a partial rank:

```sh
python -m fastunknot window examples/conway.json --lower 0 --upper 0 --normalized --auto-mirror
python -m fastunknot recognize examples/conway.json --window-radius 4 --window-seconds 0.1
```

Recognition's `--window-radius N` enables radii 0, 1, 2, 4, …, N before the
complete backend. Attempts share a per-factor time budget (default 0.1 seconds)
and object ceiling (`--window-max-objects`, default 20000), bounded by the
outer recognition limits. Widening restarts and reuses the last crossing order.
If less than twice the previous attempt's time remains, it proceeds to the
complete backend. Local resource limits also fall back; global exhaustion is
`UNKNOWN`. Any computed profile differing from the unknot proves knottedness.
Agreement remains inconclusive unless the window covers all raw degrees.

The Python API is `fastunknot.window_scan.khovanov_window(pd, lower, upper)`
or `fastunknot.window_bounds.khovanov_window_auto(diagram, lower, upper)`.
Endpoints and `by_degree` use raw cube degree. Normalized degree subtracts the
number of negative crossings in `Diagram.signs()`, not negative braid letters.
Both functions support `reduction='adaptive'` and the component algebra modes.
`recognize(..., window_radius=4, window_seconds=0.1)` enables the bounded probe.
The API's default `window_radius=None` leaves it disabled.

`benchmark_windows.py --output FILE` reproduces seven paired rounds with A/A
controls. The 36-crossing stress input drops from 17694 to 7692 peak objects;
a 10000-object limit changes `UNKNOWN` to certified `KNOTTED`. Widening on the
hard unknot is slower, so this policy remains optional. Earlier default
certificates already decide all six benchmark fixtures. Measurements are
fallback comparisons; the raw-window arm computes less than full homology.
The integrated suite passes 245 tests. Proofs, conditional query bounds, and
negative results are in [`../synthesis/windows.tex`](../synthesis/windows.tex).

### Interval normalization and graded scalar splitting

Report 14 adds optional exact-rank and capped-decision backends:

```sh
python -m fastunknot khovanov examples/conway.json --barcode
python -m fastunknot khovanov examples/conway.json --fitting
python -m fastunknot recognize examples/conway.json --backend fitting
```

`barcode` decomposes a whole component when it has one matching and one common
square-zero differential coefficient. `fitting` first searches for a bounded,
verified scalar change of basis exposing independent summands, then applies
interval normalization and sharing. By default its scalar blocks also preserve
recovered quantum shifts. Global budget exhaustion is `UNKNOWN`; local search
limits retain unresolved components. The standard backend remains the default.

The exact Python APIs are `barcode_khovanov_rank` in `fastunknot.barcode_scan`
and `fitting_khovanov_rank` in `fastunknot.scalar_split`. Their `_decide`
counterparts return rank capped at three, shortening whole intervals to length
two under the ordinary closure theorem. Decision output has no exact rank or
degree profile. A capped three means at least three, not exactly three. Exact
mode retains full lengths and degree counts. Both support `seconds`,
`max_objects`, supplied `order`, and `check_d_squared`; `fitting` additionally
supports `record_witnesses=True` and configurable local search limits.

These backends require min-fill pivots, bit algebra, no tail contraction, and
no racing. They are separate from `--reduction adaptive` and component kernels.
An exact window probe may fall back to them, but shortened decision models
cannot answer exact window queries. The explicit low-level comparison option
`preserve_grading=False` uses the archive's ungraded scalar search and does not
support the refined homogeneous checkpoint bound.

All 267 production tests pass. `benchmark_continuations.py --output FILE`
records paired timings, full-rank cross-checks, and replayable actual splits.
The five measured knot diagrams showed overhead and no nonsingleton interval
normalizations. A separately labeled graded synthetic component compresses
217 stored objects to seven in exact mode and two in decision mode. The
conditional checkpoint theorem no longer needs a bound on the original
connected component size; it still requires suitable frontier widths and
frequent pure stages. Proofs and limitations are in
[`../synthesis/continuations.tex`](../synthesis/continuations.tex).

### Verified rank-two braid preprocessing

`recognize(..., use_ranktwo=True)` or CLI `recognize FILE --ranktwo` enables
one deterministic AVL pass on a checked source braid, after cheap certificates
and before expensive descent and fallback. It replaces an optimal collection
of disjoint two-index subwords by equal empty or single-letter words. A separate
central-normal-form verifier replays the full transcript before its output is
used. These are context-safe braid equalities, not closed-braid equivalences.

Search and replay share `ranktwo_seconds` / `--ranktwo-seconds` (default 0.1).
A local limit skips the optional stage; a global limit remains `UNKNOWN`.
If the verified word beats the current diagram's crossing count, recognition
restarts with the shorter validated input, compression disabled, and the
remaining global budget. Other options are preserved. Evidence under
`before_ranktwo` and `after_ranktwo` records the distinct reduction branches.
The former includes the original source word and independently replayable
certificate. PD input without checked braid provenance bypasses the stage.

The low-level `fastunknot.ranktwo.compress` and `verify` functions also accept
explicit braid words. Recognition always uses one pass; the low-level default
`max_passes=None` instead iterates to saturation, with a weaker total bound.
The one-pass bound is deterministic `O(n log n)` word-RAM time, not a universal
quasi-polynomial knot-recognition guarantee. Flat rank-two inflations of small
cores do have a proved conditional recognition bound.

`benchmark_ranktwo.py --output FILE` reproduces seven paired end-to-end rounds,
including diagram construction and all existing certificates. Sleeve examples
improve by 3.4–33.8 times locally, while the stress five-braid slows down about
1.8 times. Default behavior is unchanged. The full suite passes 272 tests;
proofs, barriers, and measurements are in
[`../synthesis/ranktwo.tex`](../synthesis/ranktwo.tex).

### Minimal extremal windows and certified size bounds

The new optional strategy cancels the entire crossing extension before upper
truncation, including the temporary degree beyond the guard. This is distinct
from the default support strategy's pre-allocation pruning:

```sh
python -m fastunknot window examples/conway.json --lower 0 --upper 2 --minimal
python -m fastunknot recognize examples/conway.json --window-radius 2 --window-strategy minimal
```

The Python entry point is
`fastunknot.minimal_window.khovanov_minimal_window_auto(diagram, lower, upper)`.
It defaults to choosing the mirror with smaller raw upper depth. CLI mirror
selection requires `--auto-mirror`, as with other window queries. Results
always return original raw degree labels. `trace=True` records retained
matching/degree profiles. Ordinary, residue, and adaptive exhaustive reduction
and component composition are supported.

This strategy verifies a nice disc scan order: connected prefixes and suffixes,
consecutive attachments, no projection loop edges, and final closure. With no
supplied order it first checks the fast greedy order, then attempts a cubic
construction when needed. Failure withdraws the sharper complexity certificate;
the query still computes exact homology. All planning and temporary allocations
are covered by the query's resource limits.

A certified order of girth W gives retained degree-j counts at most binomial(t,j)
before closure, doubled at closure, and a uniform quasi-polynomial query bound
for raw upper depth O(log n) and W=O(log² n). Runtime checks verify these counts.
This bound does not apply to the existing support strategy, and a narrow interval
in the middle is not necessarily a shallow endpoint query. Partial agreement
still cannot certify an unknot. See
[`../synthesis/extremal.tex`](../synthesis/extremal.tex) for the domination proof,
cache accounting, external theorem attribution, and exact padding obstruction.

All 277 tests pass. `benchmark_minimal_windows.py --output FILE` compares exact
identical window queries on common supplied orders. Minimal mode is slower on
all six measured cases; it remains optional despite its stronger conditional
bound. These partial-query ratios are not end-to-end recognition speedups.

## Optional exact Potts Jones filters

`potts-faithful` decides whether the **entire normalized Jones polynomial is
one**, and can recover all its Laurent coefficients. It chooses
`q = 2^(4*n+2) + 2` from the crossing count, making the exact quadratic
specialization injective on the proved coefficient and degree bounds.
Canonical equality partitions avoid enumerating this large number of colors.
Combined with adaptive certified separator ordering, the uncapped query takes
`poly(n) * 2^O(sqrt(n)*log(n+1))` bit operations on every classical knot diagram.
This is a general subexponential **Jones computation**, not a general
subexponential recognition algorithm. Polynomial identity still yields
`INCONCLUSIVE` in the Jones filter and continues to independent recognition.

```sh
python -B -m fastunknot jones examples/conway.json --backend potts-faithful
python -B -m fastunknot recognize examples/conway.json --jones-backend potts-faithful
python -B benchmark_faithful_jones.py --output results/faithful_jones_local.json
```

The `jones` command also returns `jones_polynomial`, with variable `t=A^-4`
and sorted `[exponent, signed_hex_coefficient]` pairs. The Python API
`fastunknot.faithful_jones.faithful_potts_exact` returns `polynomial_identity`
and optionally reconstructs coefficients with `include_polynomial=True`.
Its default caps are 4096 states and 200000 transitions; pass `None` for both
to request uncapped work. The standalone `jones` command has no local caps
unless supplied. The color count is input-derived, so `--potts-colors`
does not override it. Shared budgets and global cancellation remain active
during ordering, evaluation and recovery. The shared policy's mode name
`polynomial-tail` has a quasi-polynomial tail bound for this growing `q`;
that still preserves the stated subexponential bound.

Raw exact results contain Python integers. JSON-safe obstruction witnesses
encode color counts above 256 bits in `q_hex`, use a symbolic ring description,
and retain hexadecimal quadratic coordinates. Small color counts retain `q`.
These conversions do not change Python's global decimal-conversion limit.
Full theory, validation and measured costs are in
[`../synthesis/faithful_jones.tex`](../synthesis/faithful_jones.tex).

Full recovery now returns polynomial one immediately after the faithful pair
comparison proves identity, avoiding redundant normalization and decoding.
Paired full-query measurements show a 1.96x improvement on the 254-crossing tree
medial, with little change on most other inputs. Recognition already requests
identity alone, so this does not imply a recognition speedup. Run
`benchmark_jones_identity_shortcut.py --output FILE` to reproduce the comparison
against the preserved earlier decoder.

The independent [residual-twist audit](jones_research/README.md) finds a concrete
contradiction to the combined uniform-degree and geometric-realization claims
used in arXiv:2606.22410v1. It does not disprove Jones unknot detection. That
preprint is not used to promote polynomial identity to an unknot certificate.

`potts-adaptive` defers separator preparation until actual scalar work reaches
`64*n` transitions. If at most `2*ceil(log2(n+1))` crossings remain then, it
finishes the current table under a proved polynomial tail bound. Otherwise it
builds a certified order: an unchanged order continues without repeating work;
an improved order restarts once with the **remaining original transition
allowance**. State-cap failure can also request the one preparation. Completed
order certificates survive later scalar exhaustion; global interruption never
publishes an unfinished scalar or partial certificate.

```sh
python -B -m fastunknot recognize examples/conway.json --jones-backend potts-adaptive
python -B -m fastunknot jones examples/conway.json --backend potts-adaptive
python -B benchmark_adaptive_potts.py --output results/adaptive_potts_local.json
```

The Python API is `fastunknot.adaptive_potts.adaptive_potts_exact`. Its uncapped,
fixed-color query retains `poly(n) 2^O(sqrt(n))` bit complexity, while easy
queries avoid separator construction entirely. Result `ordering_policy` records
the actual path, discarded work and total transitions. In ordinary or
polynomial-tail mode, the later homology fallback receives no separator-width
promise. This remains a one-sided scalar filter, not a complete subexponential
recognizer.

Measurements include all preparation and retain both the initial policy and
its source. The short-tail rule improves the initial policy 1.415x on the
100-crossing grid but regresses on a shuffled 16-crossing grid. Other supplied
orders finish after adaptation where ordinary/eager queries hit state caps;
those are censored comparisons, not timing speedups. Ordinary exact Potts
remains faster on some inputs, and no consistent full-recognition advantage
over it is established. See
[`../synthesis/adaptive_potts.tex`](../synthesis/adaptive_potts.tex).

`potts-separator` first constructs and verifies a balanced separator hierarchy,
then chooses the smaller frontier of its order and the existing greedy order.
For every closed classical projection it guarantees `O(sqrt(n))` crossing
frontier. At fixed color count, the uncapped exact scalar query therefore has
`poly(n) 2^O(sqrt(n))` bit complexity. This is a general subexponential **scalar
evaluation**, not a general subexponential unknot recognizer: equality is
inconclusive and the fallback's surviving homology objects remain uncontrolled.

```sh
python -B -m fastunknot jones examples/conway.json --backend potts-separator
python -B -m fastunknot recognize examples/conway.json --jones-backend potts-separator
python -B audit_separator_orders.py --output results/separator_orders_local.json
```

The Python API `fastunknot.separator_potts.separator_potts_exact` accepts
`max_states=None, max_transitions=None` for an uncapped query. Its
`order_certificate` is checked by
`fastunknot.separator_order.verify_width_bounded_order(diagram.pd, certificate)`.
The same certificate builder, `width_bounded_scan_order`, can supply an order
to any existing scanner. Verification uses graph partitions and frontier counts;
it does not call the planar-map constructor. It does not certify common-disk
prefixes. A completed certificate survives local scalar exhaustion; a later
crossing-changing reduction rebuilds it before homology. Preparation remains
subject to the global deadline.

This option adds ordering overhead and is not the default. The retained audit
checks 114 inputs with independent union-find logic. On tree-medial stress
diagrams, a 1,022-crossing frontier drops from 256 to 18; on the grid examples,
greedy remains better. A 62-crossing matching query improves 24.6x excluding
preparation, while exact Potts already handles those trees cheaply. No complete
recognition timing improvement is established. See
[`../synthesis/separator_orders.tex`](../synthesis/separator_orders.tex).

`recognize --jones-backend potts-exact` uses integer pairs in
`Z[x]/(x²−(q−2)x+1)`, with six colors by default. The
`potts-exact-factorized` option keeps processed Tait components separate until
an edge joins them. `potts5` supplies a modular five-color comparison; it
misses a proved infinite weaving family even without modular collisions.
The exact six-color filter detects that family. Equality at any chosen
specialization remains inconclusive and continues the complete fallback.
The existing `matching` filter remains the default.

Use `--potts-colors 7` to choose another exact color count (integer ≥5), and
`--jones-max-states` / `--jones-max-transitions` for local work limits.
A state limit counts represented keys, not total memory. Local exhaustion
falls through; the global recognition deadline returns UNKNOWN.
Standalone examples:

```sh
python -m fastunknot jones examples/conway.json --backend potts-exact
python -m fastunknot jones examples/conway.json --backend potts-exact-factorized
python -m fastunknot recognize examples/conway.json --jones-backend potts-exact
python -B check_potts_independent.py /tmp/potts-independent.json
python -B benchmark_potts.py --output results/potts_local.json
```

The standalone Jones command returns an inconclusive result and exits 3 on
resource exhaustion, 2 for invalid options, and 0 on a completed query.
Exact witness pairs use signed hexadecimal strings for large-integer JSON
safety. Raw evaluator APIs retain integer pairs.

The same-color benchmark measured a 23.6× factoring gain on a fixed fragmented
order (4,111→205 peak keys), but factoring slowed all six other kernel cases.
Normal recognition with the single-table exact option was about 1.14–1.15×
faster on Conway and Kinoshita–Terasaka in this small run; earlier certificates
bypassed the new filter in the other five cases. These observations do not
justify an automatic switch or a default change. See the complete theory,
limitations and measurements in [`../synthesis/potts.tex`](../synthesis/potts.tex).

## Adaptive transfer on certified disk frontiers

`--reduction disk-adaptive` adds a full finite radical transfer after sparse
cancellation pauses and the existing cheap residue shortcut declines. It keeps
nonzero maps between adjacent surviving degrees. Geometry is certified from
the actual processed rotation system and checked against live matching types.
A local work guard can decline the attempt; the unchanged partial complex then
resumes ordinary cancellation. Global deadlines still produce UNKNOWN.

This option works with full homology, recognition, either window strategy, and
component coefficient composition, under the existing adaptive scanner
restrictions. Evidence reports actual transfer calls, geometry declines, budget
fallbacks, and transfer work. The local allowance counts cooperative polls,
not elementary bit operations or total memory. It is an experimental policy,
not a competitive scheduling guarantee. `standard` remains the default.

```sh
python -m fastunknot khovanov examples/conway.json --reduction disk-adaptive
python -m fastunknot recognize examples/conway.json --reduction disk-adaptive
python -m fastunknot window examples/conway.json --upper 2 --reduction disk-adaptive
python -B check_disk_geometry.py /tmp/disk-audit
python -B benchmark_disk_transfer.py --output results/disk_local.json
```

Dense synthetic blocks gained up to 4.08× while retaining nonzero survivor maps;
the sparse control avoided transfer altogether. None of the four ordinary
diagram benchmarks made a full-transfer call, so no recognition speedup follows.
The [theory section](../synthesis/disk_transfer.tex) covers certificates, finite
perturbation, rollback, cost accounting, and explicit unknot diagrams whose raw
frontier is Ω(√n) in every order. The latter limit an order-only approach, not
recognition with simplification and structural certificates.

## Exact long-twist profiles and streamed homology

The additive RLE frontend `python -m fastunknot.twist.continuation input.json`
accepts `{"strands": 3, "runs": [[1, 1001], [2, -1], [1, 1], [2, -1]]}`.
It checks the original knot component count and evaluates structural
certificates directly on run counts. `--mode homology --method tail` computes
an exact reduced homological profile using a finite reference at run length
`W+2`, where `W` counts the fixed context crossings. Longer exponents produce
a constant interval plus finite exceptional degrees, without expansion.
The returned degrees are macro degrees; quantum grading is forgotten.

`--method streaming` instead retains two adjacent state layers and feeds
columns directly into elimination. It reduces storage but was slower in all
eight measured full-homology cases. In recognition it may stop when finalized
reduced homology already exceeds one, explicitly reporting an incomplete
homology and a rank lower bound. A partial rank-one result never proves UNKNOT.
`--method macro` retains full assembly. The existing main CLI and production
`backend="twist"` defaults are unchanged.

The ordinary recognizer has a separate opt-in `--braid-profile` flag
(`use_braid_profile=True`) for a checked source word. It specializes the
existing Seifert graph criteria, with the established PD/Artin sign conversion.
The original source remains distinct from any connected-sum factors.

The largest measured tail gain was 58.6× for exact homology; dominant-run knots
were already structurally decidable, so this is not a new recognition family.
The profile option gained 2.30–3.33× on selected fresh prebuilt homogeneous braid
diagrams. See [TWIST_CONTINUATION.md](TWIST_CONTINUATION.md) for schemas,
budgets and examples, and [the theory section](../synthesis/twist_continuation.tex)
for proofs, output-size limits, independent audits and timing scope.


## Checked rational and Montesinos presentations

`Diagram.from_rational(e, tangles)` now builds and validates a Montesinos
numerator closure, retaining checked source provenance. The recognizer uses
an exact arithmetic decision before the general diagram pipeline; disable it
with `use_rational=False` or `--no-rational`. JSON uses
`{"montesinos":{"e":0,"tangles":[[2,3],[-2,-2,-1,-2]]}}`.
The decision preserves each rational summand's denominator and handles
nontrivial determinant-one knots. Arbitrary PDs have no inferred source.

For binary coefficients too large to expand, `montesinos_certificate(e,tangles)`
provides a separate arithmetic-only API. The ordinary constructor and CLI
still build the actual PD, with a default 100,000-crossing expansion ceiling.

`recognize_with_subtangles` in `fastunknot.tangle_obstruction` optionally
searches a small literal-pattern catalogue in an arbitrary validated PD.
Each rejection verifies a four-port disk occurrence and its non-embeddability
in an unknot. No match falls back to the ordinary recognizer. This wrapper
was slower in all five measured cases and remains explicit.

See [RATIONAL.md](RATIONAL.md) for APIs, provenance and certificates,
[rational_research/README.md](rational_research/README.md) for reproducible
checks, and [the theory](../synthesis/rational.tex) for arithmetic bounds,
full-complex barriers and performance scope. These are polynomial procedures
on supplied presentations or fixed local patterns; general quasi-polynomial
recognition remains unproved.


## Quantum-ordered full transfer

`--reduction graded` and `--reduction graded-adaptive` are optional exact
policies for the standard scanner. The first computes the full differential
between scalar survivors using quantum-ordered transfer. The second retains
completed sparse pivots and switches only when the per-stage Schur-update
allowance is exhausted. Unlike a survivor-count shortcut, both retain nonzero
maps between adjacent surviving degrees. They do not require a common-disk
certificate. The standard policy remains the default.

The Python `khovanov_rank` and `recognize` APIs accept the same reduction names.
Bit coefficients, minimum-fill pivots, self-inverse cancellation and one scan
order are required. Component coefficient composition and tail finishing are
supported; homological windows and alternative scanners are rejected before
early recognition certificates. Global resource failure remains `UNKNOWN`
in recognition. The replacement graph is fully prepared before installation,
so transfer failure preserves the current differential.

See [graded_research/README.md](graded_research/README.md) for reproducible
checks and measurements and [the theory](../synthesis/graded_transfer.tex)
for the finite-transfer proof, cost accounting and unresolved multiplicity
bounds. The new full suite has 426 passing tests. The report's remaining proposals are reviewed in
[the symbolic continuation section](../synthesis/symbolic_runs.tex).


The run frontend now transports huge integer values and degree keys using exact
hexadecimal strings, accepts either signed runs or an explicit word, and
supports independent replay of serialized structural certificates. Use
`fastunknot.integer_codec.decode_degree_profile` after a JSON round trip.
The earlier total-rank law at context length plus one is documented and audited;
the full-profile computation keeps its context-length-plus-two reference.
All 431 maintained tests pass. See [TWIST_CONTINUATION.md](TWIST_CONTINUATION.md)
for the extended schema and [the theory](../synthesis/symbolic_runs.tex) for
succinct complexity and the conditional repair-DAG research target.


### Survivor corridors and bidirectional adaptive transfer

`--reduction corridor` preserves full graded transfer while pruning paths
that cannot reach an output survivor and choosing propagation direction per
component. `--reduction corridor-adaptive` first spends the existing sparse
Schur-update allowance and retains completed pivots before switching.
Both are optional; `standard` remains the default. The supported backend,
coefficient, tail and resource contracts match the graded full-transfer modes;
window combinations are rejected. Direct controls also expose sparse scalar
components and Boolean endpoint selection.

The 458-test maintained suite passes. Independent audits check 3,885 transfer
comparisons on 555 prefixes, all eight contraction identities at each prefix,
and entrywise equality of sparse versus packed scalar maps. The constructed
shared-suffix family proves a near-linear complete stage versus quadratic
forward propagation at fixed algebra size; it does not prove a knot-prefix
family or superiority to sparse cancellation. See
[corridor_research/README.md](corridor_research/README.md) for measurements,
commands and limitations, and [the article](../synthesis/corridor_transfer.tex)
for proofs and complete setup accounting.


## Certified cyclic Garside preprocessing

Report 25's exact source-braid compressor is available with `--garside` or
`recognize(diagram, use_garside=True)`. It shares exact Garside prefix states
across cyclic cuts, independently replays the proposed equalities, and restarts
recognition only when the candidate improves the current simplified diagram.
Cheap modular Alexander and structural obstructions run first; Jones follows
the probe. The optional probe has a local time/operation
allowance; exhausting it resumes the established exact pipeline under the
remaining global budget. Original source-branch evidence and PD reductions stay
separate, and backend/reduction options survive the restart.

The default radius is one; `--garside-radius 2` adds two-letter targets.
The default caps are `--garside-seconds 0.1`, `--garside-max-ticks 100000`, and
`--garside-max-targets 100000`. The probe is disabled by default. See
[`garside_research/README.md`](garside_research/README.md) for reproduction,
resource semantics and measurement scope. The theory article derives the
polynomial fixed-radius compressor bound and a conditional small-core theorem;
it does not claim a general sub-exponential unknot algorithm.


## Compressed surface-cover geometry

`fastunknot.surface_cover` maintains report 24's classifier for supplied
binary-encoded dihedral covers of bordered surfaces. `CoverIndex` provides
component and boundary-lift queries, exact signatures for ordered marked fibre
points, and evaluation of rooted equivariant maps. Classification uses at most
three unmarked family records; all arithmetic is polynomial in the input bit
length without expanding sheets. Hexadecimal JSON and cooperative cancellation
are supported. See [`cover_research/README.md`](cover_research/README.md) for
input examples, proofs, audits and separate geometric benchmarks.

This module is not called by knot recognition. Presentation extraction, full
external attachments and hierarchy search bounds remain unproved integration
steps. Even a one-type cyclic annulus cover has `W` inequivalent ordered pairs
of marked points, so efficient marked comparison alone does not bound the
number of possible hierarchy states. The theory is maintained in
[`../synthesis/surface_covers.tex`](../synthesis/surface_covers.tex).


### Binary-state faithful Jones backend (8 October 2026)

The optional `spin-faithful` backend uses one orientation bit per cut edge,
a checked integral turning cochain, and an injective integer encoding of the
full Jones polynomial. With its certified separator order and caps/deadlines
disabled, it computes the full polynomial in `2^O(sqrt(n))` deterministic
bit time. A polynomial different from one certifies knottedness; polynomial
one continues to the independent recognizer.

```sh
python -B -m fastunknot jones examples/trefoil.json --backend spin-faithful
python -B -m fastunknot recognize examples/conway.json --jones-backend spin-faithful
```

Python callers can use `spin_jones_exact(diagram, include_polynomial=True,
max_states=None, max_transitions=None)` from `fastunknot.spin_jones` for an
uncapped query. Default local caps are 4096 states and 200000 transitions;
cancellation callbacks remain available. The turning certificate validates
local geometric weights, not a claimed completed contraction. Serialized
large scalars and coefficients use hexadecimal strings.

This integrates the Jones component of `unknot_recognition_research_20261008.zip`
from commit `1be2abc8c`. Its historical benchmark data and ordering-policy
correction remain distinct from the maintained integration measurements.
See `spin_jones_research/README.md` for provenance and the synthesis article's
binary-tensor chapter for the proof. Measured regressions justify retaining
the existing default. The other newly delivered research components remain
under component-level review; the synthesis records their current status.


The spin backend now defaults to **valuation arithmetic**: each frontier integer
is stored as an odd signed mantissa and a separate power of two. This removes
monomial padding exactly, including signed cancellation and carries. Python
callers may pass `arithmetic="shifted"` to compare the original representation.
Both modes produce the same exact final scalars, polynomials, states and
transition counts. The existing `max_coefficient_bits` includes represented
full integers and final normalization; `max_frontier_mantissa_bits` and
`max_frontier_valuation` describe the compressed frontier representation.
The general Jones bound is `2^O(sqrt(n))`; its polynomial factor is absorbed.
For a separately supplied width `w`, retain `poly(n) 2^O(w)`.


### Adaptive faithful Jones queries

The optional `faithful-adaptive` backend gives faithful Potts at most `128*n`
transitions, then switches to binary spin if Potts reaches that work allowance
or its state cap. Both attempts share the caller's transition limit; discarded
Potts work, including internal reordering, is counted. A completed separator
order is reused. With caps/deadlines disabled, the default policy retains the
`2^O(sqrt(n))` general full-Jones bound.

```sh
python -B -m fastunknot jones examples/trefoil.json --backend faithful-adaptive
python -B -m fastunknot recognize examples/conway.json --jones-backend faithful-adaptive
```

The Python API is `adaptive_jones_exact` in `fastunknot.adaptive_jones`, with
`include_polynomial=True` for full recovery. `potts_trial_transitions=None`
selects the default trial; zero selects spin directly. A custom larger trial
has its own cost. Result `transitions` counts all attempts, `selected_backend`
identifies the winner, and `backend_policy` records the switch and discarded
work. Large witnesses use the backend-specific hexadecimal encoding. Polynomial
identity remains inconclusive for recognition and continues to Khovanov.
The overall default Jones backend remains unchanged.

### Polynomial scalar projectors and local-algebra stopping

The optional `primary` Khovanov backend extends Fitting splitting with exact
polynomial idempotents from Berlekamp's fixed algebra. It can split an invertible
candidate whose stable kernel is zero. Every accepted split checks the whole
typed differential and every transformed attachment.

```sh
python -B -m fastunknot recognize examples/trefoil.json --backend primary
python -B -m fastunknot khovanov examples/trefoil.json --primary
```

Python callers select `fitting_primary=True` in `fitting_khovanov_rank` or
`fitting_khovanov_decide`. The existing object, variable and candidate caps apply.
A failed candidate ordinarily leaves the component unchanged. If the candidate
has minimal-polynomial degree equal to the *complete* commutant dimension and
one-dimensional Frobenius fixed space, the entire scalar algebra is local.
Then no scalar idempotent exists and the remaining trials are safely skipped.
This says nothing about simplification by more general cobordism operations.

The experimental `fitting_reuse_commutant=True` option transports complete child
spaces inside one static compression pass. Canonical bases preserve the fresh
solver's candidate sequence. Reuse stops at a differential change and remains
off by default: measured transport overhead exceeds the saved child solves.

The local-algebra stop improves complete compression on the supplied algebraic
fixtures, but the five tested knot scans never invoke the primary path. The
main default backend is unchanged, and no general quasi-polynomial recognition
bound is claimed. Source-pinned measurements, negative results, proofs and the
748-test validation are in `../synthesis/primary_continuation.tex` and the PDF.

### Checked two-meridian recognition

`--two-meridian` enables a bounded exact stage after the invariant filters and
before optional group search or Khovanov. It derives all Wirtinger arcs from
one or two original meridians using signed crossing relations, then checks
**every original relation** by exact integer SU(2) arithmetic. Both `UNKNOT`
and `KNOTTED` answers include a replayed certificate. A failed seed search or
local limit is inconclusive and resumes the existing pipeline.

```sh
python -B -m fastunknot recognize examples/hard_unknot_8.json --two-meridian
python -B benchmark_two_meridian.py --output results/two_meridian_local.json
```

Python callers can use `recognize(diagram, use_two_meridian=True)` or the
standalone `two_meridian_decide` and `verify_two_meridian_certificate` from
`fastunknot.two_meridian`. The standalone function returns a dictionary;
pass its `certificate` to the verifier together with the same validated PD.
The certificate includes the PD hash, seed arcs, acyclic derivation, all
relator normal forms and the final gcd/parity calculation. Replay does not
repeat seed search; it shares the parser and integer arithmetic with the
producer. It cannot verify a factor's certificate against the original whole
connected sum.

The pipeline controls are `two_meridian_seconds=0.05`,
`two_meridian_max_work=2_000_000`, and `two_meridian_max_attempts=10_000`, with
corresponding hyphenated CLI options. In the standalone API those names are
`seconds`, `max_work`, and `max_attempts`. Preparation, all failed seed attempts,
arithmetic and replay share one local allowance. Global cancellation still
propagates. Weighted work is a cooperative metric, not a hard bit-time or
memory limit. Python callers can set all three caps to `None` for exhaustive
search over the at-most-two-seed class.

Uncapped, the standalone stage is a complete polynomial algorithm for **diagrams admitting
such a seed derivation**; the conservative bound is `O(n^4 log(n+2))`. It gives
no general quasi-polynomial recognition guarantee. The full pipeline must
also pay for its earlier invariant filters, including Jones; those costs are
outside this standalone bound. The report's multi-seed
formula compiler and minimum-degree propagation are not part of this stage.
The theory, proof obligations, validation and full-pipeline comparison with
the existing compressed-group incumbent are in
[`two_meridian.tex`](../synthesis/two_meridian.tex) and the updated article PDF.
The stage remains opt-in.

### Endpoint patterns and exact overlap cutoffs

The compressed-group word engine now tries short endpoint patterns after the
existing uniform, short-period, sparse-letter and two-largest-overlap shortcuts.
Patterns of lengths 1, 2, 4 and 8 can describe a complete arithmetic progression
of candidate suffix/prefix overlap lengths even when individual letters are
dense. An exact period check makes matching monotone along that progression;
backward doubling and bisection locate the last matching candidate. Short
exceptional overlaps are checked individually.

This handles binary-sized periods and multiplicities without expanding the
words. A failed structural check retains the complete occurrence-table matcher.
All attempts use the existing arena's work, node and cancellation controls;
exhaustion never means that no overlap exists. Only complete answers enter the
cache. New counters use `lcs_anchor_`; the previous shortcuts and their counters
remain intact. The public recognition defaults and certificate formats are
unchanged.

This improves a restricted class of exact compressed-word queries. It does not
bound the number of relator moves needed to recognize arbitrary knots. See
[`endpoint_clipping.tex`](../synthesis/endpoint_clipping.tex) for the proof,
validation and comparison against the previous maintained matcher.

Endpoint Markov descent now uses the original-position linked-list kernel from
report 34 for sufficiently large, connected-closure-sized inputs (at least 64
strands and 128 letters). Small inputs retain the version-1 path. Both paths
perform the same elementary moves; the new version-2 certificate records local
inverse cancellations and singleton endpoint deletions using original letter
indices. Its independent verifier replays those choices without endpoint search.
Old version-1 certificates remain supported.

On an explicit one-component braid with `n` letters and `m` strands, adaptive
descent takes `O(n+m)` word operations, including generation and replay of new
certificates. A deletion queues at most one newly exposed seam, every original
letter is removed at most once, and left renumbering uses a single offset.
Small-path work is also linear on this domain because its rank or length is
bounded by fixed dispatch thresholds. Sparse standalone link inputs retain the
legacy behavior and its `O(n*m)` upper bound. This changes neither the sufficient
endpoint criterion nor the general unknot complexity bound. The separate matrix
three-braid backend retains its quadratic bit-arithmetic term. See
[`braid_descent.tex`](../synthesis/braid_descent.tex) for proof and measurements.

### Compressed three-braids and singleton forests

`fastunknot.compressed_braid` accepts a binary Artin-word grammar:

```python
from fastunknot.compressed_braid import Builder, recognize, verify

b = Builder()
u = b.power(b.word([1, -2]), 1 << 512)
root = b.concat(b.concat(u, b.word([1, 2])), b.inverse(u))
data = b.data(root)
result = recognize(data)
assert result['status'] == 'UNKNOT' and result['verified']
assert verify(data, result['certificate']) == 'UNKNOT'
```

The general input has exactly `strands`, `rules`, and `root`. Rule zero is
`["e"]`; subsequent rules are `["g", signed_generator]` or `["c", left, right]`
with strictly earlier references. The represented object is that word's braid
closure. It is not a certificate of conversion from a separate PD diagram.
The builder shown above is for three strands; the general forest interface
also accepts directly supplied grammars with arbitrary strand count.

Given sufficient resources, the three-strand algorithm is complete and
polynomial in grammar bit size. It uses the maintained exact string kernel,
checks closure components and exponent sum, then reduces the quotient
`C2 * C3` without expansion. Independent replay checks source binding and
local reduction equalities without repeating prefix searches. General
strand counts first detect missing generators, then split singleton-generator
connected sums. Factors with at most three strands are completely decided without expansion.
Wider factors that pass the Bennequin bound now use a complete reduced F2
Khovanov cube when their binary expanded length is within
`fallback_max_crossings=12`. Larger residuals remain `INCONCLUSIVE`.
Version-two forest certificates bind the expanded word to the exact source
projection and replay checked XOR elimination traces without pivot discovery.
The Frobenius complex builder is shared by discovery and replay. Legacy
version-one proofs retain their original residual semantics.

Public `recognize` includes replay. `verify` independently returns the certified
status or raises. Defaults share 10,000,000 abstract work units and 100,000
cumulative string nodes across all factors and replay.
`fallback_max_generators=200_000` similarly counts all reduced cube generators
cumulatively, including replay; `resources["cube_generators"]` reports usage.
Set `fallback_max_crossings=0` to disable this fallback. Both fallback controls
have hyphenated CLI flags. Additional controls are
`max_input_rules=100_000`, `max_input_bytes=16_000_000`,
`max_certificate_bytes=64_000_000`, `seconds=None`, and a `check` callback.
Limits are cooperative, not hard process-memory or CPU limits. Exhaustion
returns `INCONCLUSIVE` without a partial proof. An unsupported wider forest
can instead return `INCONCLUSIVE` with a verified residual certificate;
`verified=True` alone never means unknot. External cancellation propagates.

```sh
python -B -m fastunknot.compressed_braid recognize input.json
python -B -m fastunknot.compressed_braid verify input.json --certificate proof.json
python -B compressed_braid_research/audit.py --output results/native_audit.json
python -B benchmark_compressed_braid.py --output results/native_benchmark.json
```

The CLI recognizer prints the complete result; pass its `certificate` member
to the verifier's proof file. CLI input files have byte limits before parsing.
The ordinary explicit braid API remains the default for explicit words.
On the measured conjugation sleeves at exponent `2**16`, compressed recognition
including replay is about 118 times faster for the unknot and 14 times faster
for the nontrivial knot. Small explicit controls remain substantially faster
with the explicit API. The source-bound theorem, proofs, measurements and
limitations are in [`compressed_braid.tex`](../synthesis/compressed_braid.tex).


With sufficiently large allowances, the complete grammar algorithm takes
`poly(g) + sum_i 2**O(kappa_i)`, where `g` is grammar bit size and `kappa_i`
is the minority-sign count only of unresolved wider singleton factors.
It therefore has a restricted quasi-polynomial guarantee when those counts are
`O(log(g)**2)`. This does not bound them on arbitrary diagrams. The proof,
certificate trust boundary and validation are in
[`exceptional_cube.tex`](../synthesis/exceptional_cube.tex). Reproduce the
cross-oracle audit and the splitting ablation with
`python -B compressed_braid_research/exceptional.py audit --output FILE` or
`benchmark --output FILE`. Whole-cube comparisons include proof construction
and replay; planar-scanner timings have no such certificate and are labeled
separately.


The forest now prepares finite leaf summaries and tries finite exponent tests
first, compressed three-braid decisions second, and wider fallbacks last.
It stops on the first proved nontrivial factor. A version-three
`knotted-factor` certificate binds that single witness to its exact source
interval and proves the whole connected sum nontrivial. An unknot still needs
all factor proofs in their original order. `factor_order` reports discovery
order; it is diagnostic metadata, not part of the mathematical proof.

For a small wider factor, the fallback first performs the existing verified
free/cyclic cancellation and endpoint Markov descent. A resulting three-braid
uses the compressed exact terminal; a still-wider residual uses its complete
cube. Progress is recorded in a source-bound `exceptional-reduction-v1` child.
No progress retains the direct cube. The explicit crossing preflight still
happens before expansion. Set `use_fallback_reduction=False` (CLI
`--no-fallback-reduction`) to disable only this pre-cube step; priority and
selective negative proofs remain enabled. Verification supports old and new
proofs irrespective of how the producer was configured.

This avoids cubes for reducible wider factors and avoids unfinished factors
after a complete negative witness. It retains the same exceptional-factor
asymptotic bound. See [`adaptive_forest.tex`](../synthesis/adaptive_forest.tex)
for soundness, proof compatibility, resource accounting and paired measurements.


### Sparse two-meridian seed discovery

The optional two-meridian stage now reuses generation-stamped closure arrays.
When the crossing rules have no productive unary implication, every generating
pair must be a productive binary prerequisite pair. Only those `O(n)` pairs
need examination. A proper failed closure also rules out every later candidate
pair it contains. Productive-unary systems retain complete pair enumeration.
Both paths preserve the first successful seeds and exact derivation trace;
the arithmetic, certificate schema and search-independent verifier are unchanged.

This improves seed discovery from cubic to quadratic word operations on the
checked trivial-singleton class, with linear search storage. It does not reduce
every term in the complete stage's conservative arithmetic bound. Exhaustive
seed failure remains `INCONCLUSIVE`, and the ordinary pipeline remains opt-in
through `use_two_meridian=True` or `--two-meridian`. New statistics describe the
search mode, candidate count, excluded pairs and visited closure incidences.
All preparation, attempts, arithmetic and replay share the original allowances.
See [`sparse_seeds.tex`](../synthesis/sparse_seeds.tex) for the proofs and native
measurements, and `two_meridian_research/README.md` for reproduction commands.

### Certificates for supplied normal surfaces

The native normal-surface adapter can now record source-bound topology proofs:

```python
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.normal_surface_verify import verify_normal_surface_certificate

result = normal_surface_topology(triangulation, coordinates,
                                record_certificate=True, max_cycles=100000)
if result['status'] == 'COMPLETE':
    verified = verify_normal_surface_certificate(
        triangulation, coordinates, result['certificate'], max_operations=1000000)
```

Both calls reconstruct the finite connected orientable manifold with one torus
boundary and check the normal vector. Replay verifies three complete orbit
traces and a finite boundary-cohomology witness without rerunning either search.
It checks components, orientability, boundary curves, Euler characteristic,
connected-surface genus/crosscaps, and whether the supplied surface is a
compressing disc. These claims concern the supplied triangulation; the API
establishes no correspondence with an input knot diagram and performs no
normal-vector search.

The default remains count-only. `max_cycles` is shared across production
queries; incomplete production emits no certificate. Replay's `max_operations`
cap covers the sum of trace events; exceeding it returns `False` (unverified).
Malformed evidence returns `False`, malformed source geometry raises
`NormalOrbitError`, and external cancellation exceptions propagate. Use
`fastunknot.integer_codec.json_safe` before JSON serialization of huge integers.
See [`normal_certificates.tex`](../synthesis/normal_certificates.tex) for the
proof, scope, independent comparisons and performance measurements.

### Common normal-coordinate multiplicity

`normal_surface_topology` now defaults to `reduce_multiplicity=True`. After
validating the full source, it divides out the coordinate gcd and runs the
three orbit queries on that quotient. If its component counts are `O`
orientable and `N` nonorientable, scaling by `k` gives
`k*O + (k//2)*N` orientable components and `(k%2)*N` nonorientable components.
Boundary circles and Euler characteristic scale by `k`. This handles one-sided
components: doubling a Möbius band produces one annulus.

Every topology field still describes the original input. When reduction
occurs, `coordinate_divisor` identifies the scale and `queries` contains the
actual quotient-search statistics. The proof then uses
`normal-surface-topology-v2`; replay checks exact divisibility and reconstructs
the quotient queries without searching for a gcd. The boundary witness and
source digest remain tied to the full input. Version-one proofs remain valid.
Use `reduce_multiplicity=False` for the former direct queries and proof format;
empty and primitive inputs retain their prior output structure.

See [`normal_multiplicity.tex`](../synthesis/normal_multiplicity.tex) for the
sheet-cover argument, bit complexity, old/new proof compatibility and paired
measurements. The optimization reduces work on repeated surfaces; normal
vector discovery and knot-exterior provenance remain separate obligations.

### Prepare compressed forest factors on demand

Compressed-braid recognition now builds a cheap factor schedule from the source
DAG, then projects and summarizes each factor only when it is visited. It keeps
finite/exponent obstructions ahead of three-strand factors and wider fallbacks.
A child-span-intersection upper bound replaces actual projected grammar size as the secondary
scheduling key. This estimate changes discovery order, never proof validity.

Global source and knot-component checks still run first. A negative proof needs
one fully prepared, independently replayed summand; a positive proof still needs
all factors in original strand order. One-strand projections now return their
exact canonical empty grammar directly. Existing certificate formats are unchanged.
Set `use_lazy_factors=False` or use the compressed-braid CLI's `--eager-factors`
flag to retain eager preparation and its former ordering. All work remains under
the shared public allowances. See [`lazy_forest.tex`](../synthesis/lazy_forest.tex)
for the scheduling proof, cost limits, compatibility audit and complete-call
measurements, including positive controls that need every factor.

### Compact component permutations

Compressed forest validation now evaluates only root-reachable permutations.
For more than eight strands, it stores moved points sparsely and switches to
dense tuples when a product moves more than half the strands. Dense descendants
remain dense. Every supplied rule is still validated, including dead rules;
the missing-generator guard still runs before strand-sized allocations; the
exact global component check still precedes factor recognition.

This changes no public options or certificate fields. On 402 audited sources,
all public result fields match the pinned prior implementation, and certificates
replay in both versions. Complete recognition on the measured 64-factor forest
with a finite obstruction improves from 188.472 to 89.181 ms; its separately
measured root-summary peak traced allocation falls from 8,194,752 to 1,714,252
bytes. Small controls have no consistent gain. These are supplied-grammar
measurements, with no new general unknot complexity claim.

See [`compact_permutations.tex`](../synthesis/compact_permutations.tex) for the
composition proof, storage policy, dictionary-cost assumptions and limitations.
From this directory, reproduce the native comparisons with:

```sh
python -B compressed_braid_research/permutations.py audit --output ../synthesis/data/compact-permutations-audit.json
python -B compressed_braid_research/permutations.py benchmark --output results/compact_permutations_20261008.json
```

The benchmark pins the entire old compressed-braid package at `d0f0e37761b5`,
measures complete public calls with mandatory replay, includes identical A/A
controls and a dense-storage ablation, and records source hashes and raw inputs.
Memory measurements run separately from elapsed-time samples.

### Shared cyclic overlap search with a bounded prelude

Explicit relator-overlap search now defaults to an adaptive policy. It tries
long donors first, retaining the maintained donor-length and full-match cutoffs.
After `O(L log(L+1))` charged prelude work it switches to report 46's exact shared
capped suffix-link index. Here `L` is the total **explicit** relator length.
At most four nonempty slots retain the previous pairwise query. Local handoff
keeps the original global budget; global exhaustion and cancellation propagate.

The exact query bound improves from `O(s + m*L)` to `O(s + L log(L+1))` dictionary
operations for `s` original slots and `m` nonempty relators. This is a local bound
under the stated dictionary-cost model, with no general recognition theorem.
Tied maximum-gain witnesses may change. The existing explicit and compressed
certificate replayers remain unchanged and verify the complete source-bound trace.

The low-level `fastunknot.relator_overlap.overlap_move` accepts
`backend='adaptive'`, `'pairwise'`, or `'joint'`, and optional `stats={}`. Ordinary
recognition still uses the existing `use_group=True, group_relators=True`
opt-in, or `--group-relators` on the CLI. The new index is invoked only for explicit overlap queries reached by
that stage, including explicit fallback queries from compressed search.

The native study checks 1,140 complete recognition calls on nineteen diagrams.
Gordian has paired old/new ratios 1.238 with explicit search and 1.120 with
compressed search. Small and repeated-word queries can be slower; the joint
index alone is also slower on Gordian. See
[`joint_overlap.tex`](../synthesis/joint_overlap.tex) for the capped-tree proof,
pruning and budget argument, bit-cost qualifications, baseline reconciliation,
independent replay audits and all controls.

From this directory:

```sh
python -B cyclic_overlap_research/native.py audit --output ../synthesis/data/joint-overlap-audit.json
python -B cyclic_overlap_research/native.py kernels --output results/joint_overlap_kernels_20261008.json
python -B cyclic_overlap_research/native.py pipeline --output results/joint_overlap_pipeline_20261008.json
```

The driver loads the actual maintained baseline at `bec1afd07cd2` and the delivered
report in separate modules, verifies source hashes, and retains source words,
diagrams, certificates, work counts, warmups, shuffled raw samples and A/A controls.

### Optional boundary classification for normal surfaces

`normal_surface_topology(triangulation, coordinates, classify_boundary=True)`
now separates closed components from components with boundary and gives the
orientable and nonorientable counts in each class. Existing base counts can
eliminate zero, one, or both additional interval-cone queries. For an even
common coordinate factor, counting touched components of the doubled quotient
is enough; the unknown boundary partition of the primitive quotient is not
claimed. Every returned count concerns the original supplied vector.

With `record_certificate=True`, this option produces a source-bound
`normal-surface-topology-v3` proof. The independent verifier reconstructs
markings, replays every supplied cone and justifies omitted queries without
calling the search planner. Cycle and proof-event allowances cover all queries.
The default option is false and preserves the earlier result/proof formats.

The independent audit checks 548 surfaces against Regina and report 47, including
closed orientable and nonorientable components. This is a supplied-normal-vector
operation, with no new vector search, PD provenance, or general unknot bound.
It does not determine whether a disconnected surface contains a compressing disc.
See [`normal_boundary.tex`](../synthesis/normal_boundary.tex) for the covering,
coning, multiplicity and adaptive-query arguments and measured performance.

From this directory (the audit requires Regina):

```sh
python -B normal_orbit_research/boundary.py audit --output ../synthesis/data/normal-boundary-native-audit.json
python -B normal_orbit_research/boundary.py benchmark --output results/normal_boundary_20261008.json
```

The driver compares adaptive classification with the same implementation forced
to compute both cone counts, includes identical A/A controls and production plus
independent replay, and separately checks the smaller default feature against
the actual baseline at `ce180ce1e640`. Timed calls reconstruct all geometry.

### Source-bound compressed primitive-power terminals

The optional compressed group search now tests report 45's minimum Christoffel
width when it reaches two live generators. One shared prefix-height scan can
certify that a current relator is a power of a primitive free-group word.
The new version-five certificate retains the full source diagram and verified
move prefix and uses an explicit `terminal` field. Independent literal and
compressed checkers reconstruct that state before checking the arithmetic.
Knot-group torsion-freeness and abelianization then justify the positive verdict.
The arithmetic query alone is not a knot decision for an arbitrary presentation.

`compressed_certificate(..., primitive_power=False)` retains the old search and
rank-one terminal. Ordinary recognition reaches the new rule through the existing
`group_compressed_search=True` / `--group-compressed-search` opt-in. Explicit search
and its adaptive representation handoff retain their prior terminal contracts.

All 29,540 audited cyclically reduced words agree with the literal Whitehead/root
oracle and report 45; 844 are primitive powers. The 74-diagram audit produces 44
new terminal records, all exponent one, and solves no previously stalled diagram.
All 974 tests pass. Whole-recognition timings on nineteen diagrams are mostly
unchanged; Gordian's paired old/new ratio is 0.998 despite a small work reduction.
No proper-power activity, broad speedup, or general quasi-polynomial bound is claimed.

See [`primitive_power.tex`](../synthesis/primitive_power.tex) for the arithmetic
proof, source-bound topological implication, version contract, local cost and
complete measurements. From this directory:

```sh
python -B primitive_power_research/native.py audit --output ../synthesis/data/primitive-power-native-audit.json
python -B primitive_power_research/native.py benchmark --output results/primitive_power_pipeline_20261008.json
```

The timing driver loads the actual old group host, search and replay modules at
`cd77d1bee8fa`, includes full recognition and proof replay, and retains A/A controls,
exact certificates, work and node counts, raw samples and source hashes.


### Optional raw primitive-pair projections

`--group-primitive-projection` enables report 45's disjoint higher-rank
primitive-pair contractions. Each complete round substitutes quotient images
into every relator, retains original slots, and has independent literal and
compressed replay. Version-six certificates also support raw one-generator
zero-exponent endpoints. An explicit normalization move marks the handoff
back to legacy search when raw projection stalls.

Library options are `compressed_certificate(..., primitive_projection=True)`,
`group_decide(..., primitive_projection=True)`, and
`recognize(..., use_group=True, group_primitive_projection=True)`. The group
host enables compressed search and mandatory proof replay. The earlier
`group_adaptive` option is mutually exclusive with this mode. Defaults retain
the previous version-five policy.

The 981-test suite passes. A pinned 79-diagram audit finds 34 projected
certificates with 158 pair contractions, all passing both source replayers,
with no gained or lost positives. Raw balanced algebraic fixtures contract
255 pairs in eight rounds with normalization and expansion disabled; these
fixtures are not knot diagrams. A general short-depth producer is still
missing, so no general subexponential or quasipolynomial bound follows.

All 570 whole-recognition benchmark calls completed. Projection mode is about
5–8% slower on ordinary corpus unknots; Gordian has no reliable gain. It
therefore remains opt-in. See
[`primitive_projection.tex`](../synthesis/primitive_projection.tex) for the
quotient proof, raw-round bound, noisy controls, and full measurement scope.

```sh
python -B primitive_power_research/projections.py audit --output results/primitive_projection_audit_20261008.json
python -B primitive_power_research/projections.py benchmark --output results/primitive_projection_pipeline_20261008.json
```


### Optional unit-coordinate primitive forests

`--group-primitive-forest` extends the projection route with acyclic batches
whose primitive donor roots solve a chosen generator as an integer power of
another. Donors may share generators. The producer composes shared parent
power circuits, substitutes into every original relator slot and emits a
version-seven certificate. An independent checker validates the entire forest
before replay. Cycles, duplicate children/slots and non-unit children are
rejected; general overlapping primitive pairs do not justify this operation.

Use `compressed_certificate(..., primitive_forest=True)`,
`group_decide(..., primitive_forest=True)`, or
`recognize(..., use_group=True, group_primitive_forest=True)`. The option implies
compressed projections and mandatory independent replay. It defaults to false;
existing default and disjoint-only modes remain available. It is mutually
exclusive with the older `group_adaptive` representation-switching option.

All 988 tests pass. The 80-diagram audit preserves both old modes exactly and
verifies every forest-positive proof through literal and compressed replay.
No additional diagram was solved in this sample. Abstract star, chain and
balanced presentations contract in one raw batch; the star family proves that
disjoint matching alone can require linearly many rounds. A forest batch has
polynomial encoded cost independent of tree depth, but this does not bound
general discovery, normalization or total search.

The 760-call whole-recognition benchmark still shows ordinary-corpus overhead.
A separate 150-call actual-circle group-stage benchmark reaches a 2.81x
paired speedup over the old default and 1.52x over disjoint projections at
128 crossings, including proof replay. These stage timings bypass earlier
diagram simplification and are not whole-recognizer gains.

See [`primitive_forest.tex`](../synthesis/primitive_forest.tex) for the proof,
source-bound replay contract, complete timings and their limitations.

```sh
python -B primitive_power_research/forests.py audit --output results/primitive_forest_audit_20261008.json
python -B primitive_power_research/forests.py benchmark --output results/primitive_forest_pipeline_20261008.json
python -B primitive_power_research/forests.py stages --output results/primitive_forest_stages_20261008.json
```


### Shared primitive planning

Projection and forest search now share one current candidate list. Structural
word eligibility and normalized unit vectors are cached by immutable root;
original relation slots and live generator membership are rebuilt each time.
Forest setup is skipped when fewer than two candidate slots exist, which
cannot support the existing two-edge batch threshold. Forest graph entries
are allocated only for encountered candidate generators.

The change preserves all 240 certificates/nondecisions in an 80-diagram,
three-mode audit against the previous package; every positive passes both
independent replayers. Another 2,000 raw-state planner comparisons agree.
All 992 tests pass. Existing options, proof formats and checkers are unchanged;
finite budget outcomes can differ when accounting or execution cost changes.
See [`primitive_planner.tex`](../synthesis/primitive_planner.tex) for the
amortized accounting, whole-recognition timings and separate stage timings.
All 760 complete-recognition and 200 checked-stage measurements finish.
Whole-call differences are small relative to controls; at 128 crossings,
the checked circle stage has paired speed ratios 1.07x for projections and
1.13x for forests over their prior implementations. The smallest stage
regresses slightly, so this is not a universal speedup.

```sh
python -B primitive_power_research/planner.py audit --output results/primitive_planner_audit_20261008.json
python -B primitive_power_research/planner.py benchmark --output results/primitive_planner_pipeline_20261008.json
python -B primitive_power_research/planner.py stages --output results/primitive_planner_stages_20261008.json
```

### Bounded-run normalization

The existing projection/forest normalization boundary now tries exact
run-length arithmetic on long roots whose every intermediate reduces to at
most four generator-power runs. Exponents stay binary; short roots retain
the general reducer. An unsupported probe builds no word nodes and falls
back. Compressed proof replay uses a separate implementation, with the
same certificate schema and full source reconstruction.

All 998 tests pass. An 80-diagram audit preserves 240 three-mode results,
and 87,381 short words agree with independent literal normalization.
The article proves closure under monomial substitutions and includes these
normalizations in the conditional phase bound; general short-depth discovery
and a general quasipolynomial recognizer remain open.

All 760 whole-recognition, 200 checked-stage and 240 kernel/replay timing
calls complete. Whole-call changes are within the control variation.
Conjugate kernels improve, but supplied-proof replay and unsupported-word
fallback regress. The article retains all measurements and explains these
limits; projection and forest modes remain optional.
See [`syllable_normalization.tex`](../synthesis/syllable_normalization.tex).

```sh
python -B primitive_power_research/syllables.py audit --output results/syllable_normalization_audit_20261008.json
python -B primitive_power_research/syllables.py benchmark --output results/syllable_normalization_pipeline_20261008.json
python -B primitive_power_research/syllables.py stages --output results/syllable_normalization_stages_20261008.json
python -B primitive_power_research/syllables.py kernels --output results/syllable_normalization_kernels_20261008.json
```

The follow-up skips entire raw-uniform subtrees using exact arena metadata
and stops as soon as an unsupported descendant forces fallback. Producer
and independent replay preserve the previous probe domain. Guarded tests
verify that neither uniform descendants nor irrelevant siblings are read.
All 1,000 maintained tests pass; all 240 actual-diagram mode results and
87,381 previous/current bounded-probe decisions agree.

Against the first bounded evaluator, conjugate kernels improve by paired
ratios 1.91–2.17x, complete supplied-proof replay by 1.13–1.24x, and unsupported
fallbacks by about 1.29x. Source reconstruction and all proof operations are
included in the replay timings, but proof discovery is not. Fallback still
adds work versus calling the general reducer without a probe. See
[`syllable_frontier.tex`](../synthesis/syllable_frontier.tex) for the proof,
controls and whole-recognition follow-up. General quasipolynomial recognition
remains open; projection and forest modes remain optional.

```sh
python -B primitive_power_research/syllable_frontier.py audit --output results/syllable_frontier_audit_20261008.json
python -B primitive_power_research/syllable_frontier.py kernels --output results/syllable_frontier_kernels_20261008.json
python -B primitive_power_research/syllable_frontier.py benchmark --output results/syllable_frontier_pipeline_20261008.json
```

All 760 complete-recognition measurements also finish, but they do not
establish a broad whole-input speedup: Gordian saves only 60 charged work
units out of about 1.27 million and retains the same certificate.

### Acyclic elimination with general word images

`compressed_certificate(..., elimination_batch=True)` enables version-eight
batches of distinct singleton donors with acyclic dependencies. Their images
can be arbitrary words. One linked-circuit pass performs the simultaneous
substitution without expansion or repeated normalization. Independent compressed
replay uses Kahn evaluation; literal replay preflights all expanded images.
All 1,018 maintained tests pass, including random DAG word oracles, deep
nonmonomial images, strict forgery checks and complete source replay.

Use `group_decide(..., elimination_batch=True)`,
`recognize(..., use_group=True, group_elimination_batch=True)`, or
`--group-elimination-batch` for the adaptive host. It gives the new schedule
`max_work//4` total producer work units, with at most 50,000 additional work
units after presentation recovery. The total trial cap still applies. On
nondecision it restarts the established compressed policy from the original
source. Observed trial work is deducted from the fallback allowance; recovery
failure before complete accounting reserves the full trial quota. The wall
deadline is shared. Direct producers can opt into the extra continuation cap
with `post_recovery_work`; its default is `None`.
The option implies compressed search/replay, defaults to false, and is mutually
exclusive with the older explicit-to-compressed `group_adaptive` option.

The 80-diagram audit preserves all 240 results in the prior modes. Direct
batching loses one of 53 positives; capped fallback retains all 53. Whole-input
timings show both wins and substantial regressions, so this is an optional
alternative rather than a new default. The detailed
[`article section`](../synthesis/elimination_batch.tex) gives the Tietze proof,
polynomial encoded batch cost, conditional raw-phase bound, capacity checks,
and separate complete-recognition and checked-stage measurements. General
short-depth discovery and quasipolynomial recognition remain unproved.

```sh
python -B primitive_power_research/elimination.py audit --output results/elimination_batch_audit_20261008.json
python -B primitive_power_research/elimination.py benchmark --output results/elimination_batch_pipeline_20261008.json
python -B primitive_power_research/elimination.py stages --output results/elimination_batch_stages_20261008.json
```

The follow-up [`reachability analysis`](../synthesis/elimination_reach.tex)
maintains exact dependency reachability within each planning state, preserving
unconstrained greedy witnesses while avoiding repeated DFS scans. It retains
dense mask costs and a quadratic-bit storage bound; this is not a global
complexity improvement. The audit compares 2,250 planner states with both the
prior planner and an independent literal oracle. All 80 direct outcomes, including positive
certificate hashes, match the prior producer, and larger source trials complete at 128,
256 and 512 crossings without fallback. The recovery-aware trial can cost
more on unsuccessful candidates such as Gordian. Updated whole-input and
checked-stage measurements, including incomplete old outcomes, are separate
from the initial measurements above.

```sh
python -B primitive_power_research/elimination_reach.py audit --output results/elimination_reach_audit_20261008.json
python -B primitive_power_research/elimination_reach.py benchmark --output results/elimination_reach_pipeline_20261008.json
python -B primitive_power_research/elimination_reach.py stages --output results/elimination_reach_stages_20261008.json
```


### Exact word-cache frontiers

Inverse and free-reduction queries now stop source traversal at exact cached
results. This also handles certified reduced substrings whose intermediate
source concatenations have no individual cache entries. Discovery publishes
no partial results, and all existing work/node limits and cancellation apply.
No option or certificate format changes. The existing independent move
checkers use the updated shared word engine.

Across completed queries, each newly collected source node enters its cache
once. Traversal costs `O(q + U log(U+1))` identifier operations over `q` calls
and `U` newly visited nodes, separately for each cache. This excludes algebraic
operations, failed attempts, integer bit costs, and overall grammar growth.
See the [theory and measurements](../synthesis/word_cache_frontier.tex).

All 1,018 tests pass. Exhaustive short-word validation checks 21,845 words
against literal and prior-engine oracles. All 400 outcomes across five modes
on 80 diagrams match the prior package; every positive passes old/current
literal and compressed replay. Gordian retains its proof and 9,025 producer
nodes while default producer work drops from 1,215,145 to 1,154,597. Separate
kernel, supplied-proof and whole-recognition measurements retain A/A controls
and all incomplete outcomes; a kernel gain is not a proof-discovery bound.

```sh
python -B compressed_word_research/frontier.py audit --output results/word_cache_frontier_audit_20261008.json
python -B compressed_word_research/frontier.py kernels --output results/word_cache_frontier_kernels_20261008.json
python -B compressed_word_research/frontier.py benchmark --output results/word_cache_frontier_pipeline_20261008.json
```

### Certified sparse component incidence

`fastunknot.sparse_incidence` counts components meeting each port signature
without allocating the dense observer's `2**r` output array. Ports are explicit
unions of half-open intervals over the native interval-pairing universe.
The result contains positive `[mask, count]` rows; bit `i` denotes port `i`.

```python
from fastunknot.sparse_incidence import analyze_sparse_port_incidence
from fastunknot.sparse_incidence_verify import verify_sparse_port_incidence_certificate

ports = [[(0, 4)], [(2, 6)]]
r = analyze_sparse_port_incidence(10, [], ports, strategy='split',
                                  record_certificate=True)
assert r['status'] == 'COMPLETE'
assert verify_sparse_port_incidence_certificate(10, [], ports, r['certificate'])
assert dict(r['histogram']) == {0: 4, 1: 2, 2: 2, 3: 2}
```

`linear` (the default) deletes ports individually; `split` tries balanced
blocks and adapts query count to small signatures. Both are exact. Certificates
independently replay native orbit traces, zero witnesses and total mass without
calling either search routine. Verify certificate entries before trusting a
separately supplied histogram. Use `integer_codec.json_safe` for serialization.

`analyze_sparse_signed_incidence` and `verify_sparse_signed_incidence_certificate`
add `[mask, consistent_count, inconsistent_count]` rows using a parity cover
with the same signature support. Consistency means orientability only if the
supplied parity is known to be the surface orientation character.

`max_cycles` and `max_queries` are shared across baseline, discovery, proof and
cover counts. `max_signatures` caps positive entries. Exhaustion returns
`INCONCLUSIVE` with no histogram or certificate; `check` callback exceptions
propagate. Independent replay uses its own callback; producer allowances do
not meter verifier work. These APIs decide properties of supplied interval systems. They do
not bind a system to a knot exterior or return a knot verdict. The legacy dense
interface remains available for callers that need every subset slot.

See [the theory](../synthesis/sparse_incidence.tex). Reproduce native validation
and complete certified-query measurements with:

```sh
python -B incidence_research/sparse.py audit --output results/sparse_incidence_audit.json
python -B incidence_research/sparse.py benchmark --output results/sparse_incidence_benchmark.json
```

### Weighted normal components and essential-disc counts

`normal_surface_components.normal_component_census` now classifies components
of an admissible binary normal vector in a validated compact orientable
triangulation with one torus boundary. `mode='disk'` uses three weights per
orbit: Euler characteristic and two boundary-homology evaluations. `summary`
adds polygon and boundary-point counts; `coordinates` returns full connected
component vectors and their multiplicities. The census can detect discs when
aggregate boundary parity cancels between components.

`normal_disk_kernel.normal_compressing_disk_count` removes vertex-link
components and divides the remaining coordinates by their quadrilateral gcd
before its expensive component query. It rescales the essential-disc count
exactly. It does not infer a total component count, since one-sided components
can have connected orientation doubles. For example, from the repository's
`fast/` directory:

```python
from normal_orbit_research.fixtures import layered_torus
from fastunknot.normal_disk_kernel import (
    normal_compressing_disk_count, verify_normal_disk_count_certificate,
)
triangulation, meridian = layered_torus(4)
g = 1 << 4096
coordinates = [[g*x + (g+1 if j < 4 else 0)
                for j, x in enumerate(row)] for row in meridian]
r = normal_compressing_disk_count(triangulation, coordinates,
                                  record_certificate=True)
assert r['status'] == 'COMPLETE' and r['compressing_disk_components'] == g
assert verify_normal_disk_count_certificate(
    triangulation, coordinates, r['certificate'])
```

The count certificate binds the original coordinates, including the removed
vertex links, and independently checks the core and its weighted proof.
`normal_component_verify.verify_normal_component_certificate` checks a census.
The generic `weighted_orbits` APIs also support arbitrary signed integer-vector
weights on interval systems; `weighted_orbit_verify` independently replays them.

A previously checked orbit trace can be supplied to the census for new weight
queries, with `max_cycles=None`. Otherwise `max_cycles` limits orbit discovery;
`check` also controls weight transport and independent replay. An incomplete
query returns no histogram, disc count or certificate. Use `json_safe` from
`integer_codec` for binary-integer serialization.

A zero count rejects this vector, not all possible disc vectors. A positive
count becomes an unknot witness only after certified provenance identifies
the triangulation with the input knot exterior. That construction and general
candidate search remain separate work. See [the theory](../synthesis/weighted_components.tex).

```sh
python -B weighted_research/native.py audit --output results/weighted_components_audit.json
python -B weighted_research/native.py benchmark --output results/weighted_components_benchmark.json
```

The audit uses the optional Regina oracle; the runtime APIs do not require it.

### Ordered replay of singleton-elimination batches

New version-eight `elimination_batch` certificates list selected donors in
an independently checked dependency order. Selection and the raw Tietze
operation are unchanged. The checker assigns increasing ranks to selected
generators, and rank zero to survivors. One pass over the shared source grammar
records each node's largest rank and its occurrence count capped at two. A
donor is valid in this order when its own generator is its unique largest-rank
letter. This avoids a separate occurrence/support scan for every donor.

The checker then compiles signed references to the defining contexts. It does
not eagerly materialize inverse words or normalize the source. Every donor,
including definitions unused by surviving relators, is checked. On an ordered
valid batch with `M` reachable source nodes, the checker adds at most `5*M`
nodes and leaves at most `4*M` reachable output nodes. These are grammar-size
bounds; sorting, integer lengths, source reconstruction and batch discovery
have their own costs.

The certificate schema is unchanged. Unordered legacy entries use the existing
complete dependency checker after the rank attempt. Their meaning is preserved,
although this additional charged scan can exhaust a finite work allowance.
Literal verification remains independent and accepts either order. Cancellation
and resource exhaustion leave relator roots and live generators unpublished.
The optional portfolio and its discovery fallback retain their existing policy.
See [the theory and measurements](../synthesis/ordered_batch.tex).

```sh
python -B compressed_word_research/ordered_batch.py audit --output results/ordered_batch_audit.json
python -B compressed_word_research/ordered_batch.py kernels --output results/ordered_batch_kernels.json
python -B compressed_word_research/ordered_batch.py stages --output results/ordered_batch_stages.json
python -B compressed_word_research/ordered_batch.py pipeline --output results/ordered_batch_pipeline.json
```

### Adaptive periodic-merger scheduling

`interval_orbits.count_orbits` now defaults to `merger_scheduler='adaptive'`.
It starts with the historical lexicographic greedy scan, indexes periodic
rows after the first failed candidate, and switches to a generation-checked
heap only when the closure spends its initial `k*(k-1)//2` merger-test
allowance. This is a scheduling threshold, not an incompleteness budget.

Stable row IDs and generations preserve the exact successful merge sequence,
current certificate indices, complete orbit certificates and cycle counts.
The independent orbit and weighted verifiers are unchanged. Native weighted,
sparse-incidence and normal-surface consumers inherit the default. Callback
counts and scheduler statistics can differ, so wall-clock cancellation can
stop at different points. Incomplete calls still return no count or proof.

Pure `merger_scheduler='queue'` makes at most `(k-1)**2` candidate tests per
nonempty closure. Adaptive mode makes at most `k*(k-1)//2 + (k-1)**2`, while
easy first-pair successes and no-merge closures avoid queue construction.
The worst-case heap has quadratic storage. `merger_scheduler='legacy'`
retains the linear-space restarting scan for comparison or callers preferring
that storage bound. These are per-closure bounds; the general AHT cycle bound
is unchanged. The scheduler improves a supplied-component kernel and does not
add diagram provenance, surface discovery or a new knot-decision stage.

```python
from fastunknot.interval_orbits import IntervalPairing, count_orbits
pairs = [IntervalPairing(0, 7, 8, 15)] * 32
answer = count_orbits(16, pairs, record_certificate=True)
assert answer.complete and answer.orbits == 8
assert answer.stats['merger_queue_switches'] == 0
```

See [the proof and native measurements](../synthesis/adaptive_merger.tex).
Reproduction freezes the prior package and measures complete certificate
construction and independent replay, including fresh geometry for normal
queries:

```sh
python -B merger_research/native.py audit --output results/adaptive_merger_audit.json
python -B merger_research/native.py intervals --output results/adaptive_merger_intervals.json
python -B merger_research/native.py normal --output results/adaptive_merger_normal.json
```

### Persistent replay across raw elimination batches

Compressed version-eight verification now groups two or more consecutive
`elimination_batch` moves into one private signed circuit. Concatenation nodes
remain immutable; each eliminated generator receives one binding. Later
bindings update historical occurrences through that circuit. The checker
derives each donor from the independently reconstructed source, validates
singleton occurrence and acyclic dependencies, and exports ordinary immutable
word nodes once at the end of the block. No free reduction or equality query
is used inside a block. Normalization, projection, Whitehead and every other
move end the block; isolated batches retain the existing checker.

Ordered witnesses use a maximum-rank summary. Unordered legacy witnesses
reconstruct a dependency order with selected-generator support masks, then
undergo the same independent rank check. All donor contexts are checked
before publishing a batch internally, including unused definitions. Public
relator roots and live generators change only after the complete block and
its export succeed. Private circuit and historical word nodes share the
node allowance; all work uses the original callback and work budget.
Finite-budget outcomes can therefore differ from the old replay path.

Balanced context assembly bounds the entire raw block polynomially in its
initial grammar and generator count, even when the expanded words grow
exponentially. This replaces the per-batch growth accounting for replay.
The producer integration below extends this bound to raw batch discovery;
normalization boundaries and general knot discovery remain separate
complexity obligations. Certificates and literal verification are unchanged.
See [the proof and measurements](../synthesis/persistent_replay.tex).

```sh
python -B compressed_word_research/persistent_replay.py audit --output results/persistent_replay_audit.json
python -B compressed_word_research/persistent_replay.py kernels --output results/persistent_replay_kernels.json
python -B compressed_word_research/persistent_replay.py stages --output results/persistent_replay_stages.json
python -B compressed_word_research/persistent_replay.py pipeline --output results/persistent_replay_pipeline.json
```

### Persistent greedy batch discovery

The optional `elimination_batch` search now retains a private signed circuit
across consecutive raw batches. It recomputes exact lengths, presence and
repetition masks after bindings change, and obtains global occurrence counts
with one reverse dependency pass. The existing greedy scores, cycle checks
and ordered donor selection are preserved. A first batch that immediately
reaches rank one or two keeps the direct fast path.

The private block exports once when batch discovery stalls or reaches rank
below three. Normalization, projections and other moves use the ordinary arena.
Roots, live generators and moves are published together after successful export;
private nodes share the ordinary resource allowance. The independent checker,
certificate format, bounded trial and fallback policy are unchanged.

Balanced contexts give polynomial encoded cost for the entire raw block,
including its donor discovery. This does not bound the number or cost of later
normalization/exposure phases. See [the theory and native evidence](../synthesis/persistent_producer.tex).
The pinned comparison passes 1,116 maintained tests and an 84-diagram audit,
with identical certificates and no gained or lost positives. Previous replay
benchmark ratios are not producer speedups. The drivers preserve old packages,
source hashes, complete samples, A/A controls and incomplete outcomes:

```sh
python -B compressed_word_research/persistent_producer.py audit --output results/persistent_producer_audit.json
python -B compressed_word_research/persistent_producer.py source --output results/persistent_producer_source.json
python -B compressed_word_research/persistent_producer.py stages --output results/persistent_producer_stages.json
python -B compressed_word_research/persistent_producer.py pipeline --output results/persistent_producer_pipeline.json
```

### Plain power relations after primitive reductions stall

Optional `primitive_projection` and `primitive_forest` searches now try pairs
of raw cyclic power relators after their existing primitive donors fail.
Relations `x^a y^b` and `x^c y^d` with `a*d-b*c != 0` force both generators
to have finite order. In the independently source-verified knot group,
torsion-freeness therefore permits deleting both everywhere. Every relator
slot is retained. This internal rule is not valid for arbitrary groups with
torsion and is not a knot verdict by itself.

The producer recognizes the exact cyclic two-run spelling using bounded run
summaries on the word circuit; a pure-power row may supplement a mixed row.
It selects disjoint pairs and retains at least one generator. Version-nine
`power_pair_delete` evidence contains only generator labels and two source
slot indices per pair. Separate compressed and literal checkers authenticate
the word shape, recompute the nonzero determinant, and perform their own
substitutions. They do not call producer helpers or trust exponent claims.
Version-eight and earlier certificates cannot use this new move.

An empty coherent-pair snapshot from the existing primitive planner proves
there is no mixed donor for this detector. Search skips its preparation in
that case. This exact eligibility guard removes redundant scans while
preserving the supported discovery class.

A deletion-only epoch has polynomial encoded cost: reachable grammar size
and raw lengths never grow. General exposure and normalization remain outside
that bound. The operation closes supplied binary-power families where existing
primitive forests find no donor. The 88-diagram audit found no automatic new
proofs or coverage gain; a deliberately exposed complete PD certificate passes
both independent verifiers. All 1,121 maintained tests pass.

See [the proof, scope and measurements](../synthesis/power_pairs.tex).

```sh
python -B compressed_word_research/power_pairs.py audit --output results/power_pairs_audit.json
python -B compressed_word_research/power_pairs.py benchmark --output results/power_pairs_benchmark.json
```

### Compact full-coordinate component inventories

`normal_component_census(..., mode='coordinates')` now transports the positive
quadrilateral coordinates and one positive source-minimum triangle anchor per
quotient vertex. Matching equations recover the complete component vectors.
The reported `weight_dimension` is `max(1, q + a)` instead of `7*t`, where `q`
is the positive quadrilateral support and `a` the number of positive anchors.
The output still contains the full coordinates and binary multiplicities.

New coordinate certificates use `normal-component-census-v2`. The independent
checker reconstructs triangles by solving matching rows, without the producer's
spanning forest. Existing dense version-one certificates remain accepted;
disk and summary queries keep their existing certificates. Empty sources,
vertex links and one-sided components are supported under the existing finite
compact torus-boundary manifold contract.

The component-profile report also gives `H <= v + 2*q` distinct full component
vectors (`H <= v + q` when all are two-sided). This bounds the output for a
supplied surface; it does not bound normal-surface search or establish general
quasi-polynomial unknot recognition. See [the theory and native measurements](../synthesis/compact_coordinates.tex).

```sh
python -B weighted_research/compact_coordinates.py audit --output results/compact_coordinates_audit.json
python -B weighted_research/compact_coordinates.py benchmark --output results/compact_coordinates_benchmark.json
```

### Local vector arithmetic in weighted suffix folds

Weighted orbit truncations now rebuild vectors only in the interval receiving
the deleted suffix. Unchanged prefix and tail vectors are reused as immutable
tuples. This preserves the complete canonical partition, statistics and
certificates; the independent weighted checker is unchanged.

For `R` runs, `S` suffix runs and `P` retained runs meeting the receiving
interval, a fold takes `O(R)` traversal, `O(S log(S+1))` endpoint comparisons,
and `O((S+P)*d)` vector-coordinate work. The previous reconstruction did dense
vector arithmetic over the entire retained prefix. The native suffix operation
also has the sharp bound `R_after <= R_before + 2`, yielding `R <= R_initial + 2*T`
after `T` folds. The report's full-carrier `+3` bound applies to a different
transfer operation. See [the proof and measured scope](../synthesis/suffix_folds.tex).

```sh
python -B weighted_research/suffix_folds.py audit --output results/suffix_fold_audit.json
python -B weighted_research/suffix_folds.py benchmark --output results/suffix_fold_benchmark.json
```

### Source-anchored monomial certificate replay

The compressed checker now holds consecutive primitive projections and
unit-coordinate forests as images of immutable source roots. It authenticates
each donor's exact counts and prefix heights without constructing intermediate
words, and exports ordinary grammar nodes once at the block boundary. Isolated
moves keep their existing checker. Source recovery, version checks, torsion-free
knot-group prerequisites and terminal conditions remain mandatory. Producer
discovery and the independent literal verifier are unchanged.

Final allocation is `N0 + O(S0 + r*Lambda)` within a raw block, where `S0` is
source grammar size, `r` the source rank and `Lambda` the polynomially bounded
cumulative exponent bit size. Normalization or nonmonomial operations end that
bound. Supplied binary-power schedules replay about 2–3× faster; the largest
stabilized-circle full certificate has a 1.123 paired old/new timing ratio.
Whole recognition on the 19-case corpus shows no broad gain. See
[the proof and scoped measurements](../synthesis/anchored_replay.tex).

```bash
python -B compressed_word_research/anchored_replay.py audit --output results/anchored_replay_audit.json
python -B compressed_word_research/anchored_replay.py kernels --output results/anchored_replay_kernels.json
python -B compressed_word_research/anchored_replay.py source --output results/anchored_replay_source.json
python -B compressed_word_research/anchored_replay.py pipeline --output results/anchored_replay_pipeline.json
```

### Source-anchored primitive discovery

Optional projection and forest search now retain a monomial source table across
raw discovery rounds when a discovered move introduces nonunit powers and
leaves more than two generators. Unit-image entry moves retain the faster
cached ordinary implementation. Signed two-label eligibility is recomputed under the
current images; the existing greedy planners use source height profiles for
primitive-power queries. One export replaces repeated ordinary substitutions.
The producer returns to the existing search at rank two, before a higher-priority
singleton batch, and at a primitive stall. All independent checker files remain
unchanged. The full source audit preserves certificates in six option combinations,
including combined singleton/forest search.

The encoded bound is polynomial within a fixed monomial source block. It counts
failed donor queries as well as successful moves and ends at normalization or
other nonmonomial source changes. See
[the theory and complete-call evidence](../synthesis/anchored_producer.tex).

```bash
python -B compressed_word_research/anchored_producer.py audit --output results/anchored_producer_audit.json
python -B compressed_word_research/anchored_producer.py kernels --output results/anchored_producer_kernels.json
python -B compressed_word_research/anchored_producer.py source --output results/anchored_producer_source.json
python -B compressed_word_research/anchored_producer.py pipeline --output results/anchored_producer_pipeline.json
```

### Plain-power component certificates

Optional primitive-projection search now tries a connected power-component
contradiction after its primitive and pair rules fail. A signed cycle with
unequal exponent products, or a pure-power seed and its connected tree, proves
that the component's generators are trivial in the source-established
torsion-free knot group. Components contain at least three labels and retain
at least one survivor. The version-ten witness stores labels and donor slots;
it never asks the checker to trust rational potentials or exponent claims.

The producer uses rational graph consistency. The independent checker recovers
actual cyclic one/two-run words, strips tree leaves and compares signed cycle
products. Literal replay remains separate. Complete binary cycles with product
difference one now close where the earlier configured algebraic search stalls.
Ordinary-diagram certificates and coverage are unchanged in the pinned audit;
this is a local inference extension, not a general quasipolynomial recognizer.
See [the proof, source integration and measurements](../synthesis/power_components.tex).

```bash
python -B compressed_word_research/power_components.py audit --output results/power_component_audit.json
python -B compressed_word_research/power_components.py stages --output results/power_component_stages.json
python -B compressed_word_research/power_components.py source --output results/power_component_source.json
python -B compressed_word_research/power_components.py pipeline --output results/power_component_pipeline.json
```

### Source-checked compact knot exteriors

`diagram_exterior.diagram_exterior` constructs the compact exterior of a
validated classical knot directly from its PD. It uses the Weeks crossing
cells and a compatible finite subdivision, with exactly `20*max(1,n)`
tetrahedra and `8*max(1,n)` boundary triangles. The implementation needs no
Regina installation. A separate coordinate-based checker binds every face
pairing to the source diagram:

```python
from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.diagram_exterior_verify import verify_diagram_exterior

diagram = Diagram.from_braid(2, [1, 1, 1])
triangulation = diagram_exterior(diagram)
assert verify_diagram_exterior(diagram, triangulation)
```

This triangulation can be passed to the existing normal-surface APIs. An
independently verified essential disc in this same triangulation proves the
source knot unknotted. The constructor does not search for that disc, simplify
the triangulation, or mark a meridian/longitude basis. The checker accepts
only canonical numbering in either the current five-tetrahedron cell
subdivision or the original twenty-tetrahedron cell subdivision. The latter
remains available as `subdivision='centred'`; the default is `'pulling'`.
Arbitrary supplied triangulations still need their own provenance evidence.
The default recognition pipeline is unchanged.

See [the construction proof and validation](../synthesis/diagram_exterior.tex).
The optional Regina audit checks the unsimplified crossing triangulation up
to isomorphism and independently validates the finite result. The benchmark
measures fresh construction, independent source replay and native manifold
validation together, comparing the initial centred implementation against
the four-times-smaller pulling subdivision, with A/A controls for both.
These are geometry costs, not recognition speedups.

```bash
python -B -m normal_orbit_research.exteriors audit --output results/diagram_exterior_audit.json
python -B -m normal_orbit_research.exteriors benchmark --output results/diagram_exterior_benchmark.json
```

### Native cocycle normal-disc search

`normal_seed.normal_seed_decide` now constructs candidates on the canonical
source exterior. It recovers a primitive integral cocycle using a maximal-tree
gauge and exact rational elimination, then tests the corresponding normal
surface. If needed, it minimizes the number of pieces by integer vertex
potentials before testing a second surface. Every positive result includes
a source geometry certificate and independently replayed normal-disc proof.

```python
from fastunknot import Diagram
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate

diagram = Diagram.from_braid(4, [-1, 2, 1, -2, 3])
answer = normal_seed_decide(diagram)
assert answer['status'] == 'UNKNOT'
assert verify_normal_seed_certificate(diagram, answer['certificate'])
```

For this five-crossing input, the raw 194-piece surface has no compressing
disc, while the optimized 84-piece surface has one. The optimizer is exact
for piece count, but it does not minimize genus: the unknot represented by
the two-braid `[1, 1, -1]` remains a genus-one miss, even after reduction from
45 to 43 pieces. An unsuccessful or capped query is always `INCONCLUSIVE`.

Enable the bounded portfolio stage with `recognize(..., use_normal_seed=True)`
or CLI `--normal-seed`. It follows filters and an enabled group search, then
falls back to the established exact path when needed. The default is disabled.
`--normal-seed-max-work` controls the shared guard-count allowance, including
positive replay; `--normal-seed-no-optimize` skips span optimization. Set
`--normal-seed-tree-trials 0` as well to test only the first surface.
The API also accepts a cancellation callback. The legacy `max_cycles` argument
is still validated, but this restricted stage now needs zero orbit cycles.

The span optimizer and its arithmetic checker are separately available as
`cocycle_span.minimize_cocycle_span` and
`cocycle_span_verify.verify_cocycle_span`. Reduced-cost Dijkstra augmentations
take `O(T^2 log T)` arithmetic operations, with one flow unit per tetrahedron
regardless of binary height size. The separate cohomology preprocessing can
still take cubic arithmetic work. No complete recognition bound follows.
See [the theory, counterexample and measurements](../synthesis/cocycle_seeds.tex).

```bash
python -B -m normal_orbit_research.seeds audit --output results/cocycle_seed_audit.json
python -B -m normal_orbit_research.seeds optimize --output results/cocycle_seed_optimize.json
python -B -m normal_orbit_research.seeds source --output results/cocycle_seed_source.json
python -B -m normal_orbit_research.seeds pipeline --output results/cocycle_seed_pipeline.json
```

Primitive cocycle discovery now schedules the shortest active equation first,
preferring unit coefficients and columns incident to fewer equations. Exact
column incidence avoids visiting rows that cannot change. Reverse elimination
order reconstructs the kernel, and a fixed primitive sign preserves the
previous implementation's exact heights and normal coordinates. This reduces
observed fill and rational work; its conservative dense bound remains cubic.
This scheduling change preserved the independent source-disc verifier.

```bash
python -B -m normal_orbit_research.cocycle_sparse audit --output results/cocycle_sparse_audit.json
python -B -m normal_orbit_research.cocycle_sparse prepare --output results/cocycle_sparse_prepare.json
python -B -m normal_orbit_research.cocycle_sparse recognize --output results/cocycle_sparse_recognize.json
```

The default AHT merger scheduler now skips disjoint periodic supports with
a sweep ordered by interval endpoints. It preserves the greedy successful
merge sequence and the exact certificates, and charges overlap enumeration
before switching to the existing queue on dense cases. A no-merger disjoint
closure takes `O(k log k)` scheduling work instead of testing every pair;
the conservative per-closure bound remains `O(k^2 log k)` with quadratic
memory. Static-gap contraction also reuses immutable rows when its map is
the identity. Independent orbit and normal-surface verifiers are unchanged.

```bash
python -B -m normal_orbit_research.supports audit --output results/orbit_support_audit.json
python -B -m normal_orbit_research.supports orbits --output results/orbit_support_orbits.json
python -B -m normal_orbit_research.supports recognize --output results/orbit_support_recognize.json
```

Weighted queries now use conservation after the complete interval proof
establishes exactly one orbit: its vector is the total input weight. The
independent checker validates the entire unweighted proof before applying
the same mathematical identity with its own weight reconstruction. This
avoids weight transport in connected queries and preserves the existing
certificate bytes and schemas. Multi-orbit queries retain full transport;
matching the total weight alone cannot certify their histogram.

```bash
python -B -m normal_orbit_research.single_orbit audit --output results/single_orbit_audit.json
python -B -m normal_orbit_research.single_orbit weighted --output results/single_orbit_weighted.json
python -B -m normal_orbit_research.single_orbit recognize --output results/single_orbit_recognize.json
```

The cocycle seed stage now certifies connectedness directly, using report 31's
zero-class deletion argument. Its separate checker authenticates the knot
exterior, reconstructs signed global edge values and checks integral
primitivity after its own spanning-tree gauge. Raw proofs require a connected
zero-edge graph; optimized proofs require an independently checked minimum-span
witness. These hypotheses prove a connected orientable surface, so Euler
characteristic one certifies an essential disc without an interval-orbit trace.
An arbitrary primitive surface with Euler characteristic one is insufficient:
a retained trefoil counterexample has three components and no essential disc.

New `diagram-cocycle-disc-v1` certificates contain heights and an optional span
witness. `verify_normal_seed_certificate` also retains support for previous
`diagram-normal-disc-v1` component proofs. The independent
`normal_cocycle_verify.inspect_cocycle_certificate` returns checked connected
surface data or `None`; a valid non-disc remains an inconclusive candidate.
The candidate vectors, optional-stage default and exact fallback are unchanged.
See [the connectivity proof and measurements](../synthesis/cocycle_connectivity.tex).

```bash
python -B -m normal_orbit_research.connectivity audit --output results/cocycle_connectivity_audit.json
python -B -m normal_orbit_research.connectivity replay --output results/cocycle_connectivity_replay.json
python -B -m normal_orbit_research.connectivity recognize --output results/cocycle_connectivity_recognize.json
```

After an unsuccessful raw cocycle, the native stage now tries up to four
alternative BFS tree gauges before span optimization. It integrates the
existing signed cocycle along each tree, preserving its primitive class;
cohomology elimination runs once. Duplicate normalized potentials are skipped.
A tree success avoids the flow solve. Requested trials after the fourth run
only after an optimization miss, with reproducible shuffled adjacency orders.
Every positive retains the unchanged independent source-bound checker and
`diagram-cocycle-disc-v1` format.

Use `tree_trials` on `normal_seed_decide`, `normal_seed_tree_trials` on
`recognize`, or CLI `--normal-seed-tree-trials`; the default is four and zero
restores raw-then-span search. A larger allowance such as 24 expands this
bounded search and shares the same work cap and deadline. On 84 source records,
native positives rise from 18 to 23 by default, or 24 with 24 trials. All
previous positive hashes are preserved. This is additional restricted search
coverage, not completeness or an improvement to the general complexity bound.
See [the tree-gauge proof, audit and costs](../synthesis/cocycle_trees.tex).

```bash
python -B -m normal_orbit_research.trees audit --output results/cocycle_trees_audit.json
python -B -m normal_orbit_research.trees recognize --output results/cocycle_trees_recognize.json
```

Span optimization now batches units along zero-reduced-cost residual paths.
Breadth-first levels and an iterative current-arc traversal send a blocking
flow without another shortest-path search. Two attempts that send fewer than
two units hand off to ordinary Dijkstra; a later zero-distance augmentation
can restart batching. The independent primal/dual checker and certificate
format are unchanged, although selected corner matchings can differ.

On the all-zero shared-vertex family, one linear-work block replaces the
previous quadratic residual search. The conservative general bound remains
`O(T^2 log T)` arithmetic operations with linear graph storage. Native source
queries benefit from repeated marginal costs; sparse batches can add overhead,
which is measured separately. See [the proof and complete-call controls](../synthesis/cocycle_blocking.tex).

```bash
python -B -m normal_orbit_research.blocking audit --output results/cocycle_blocking_audit.json
python -B -m normal_orbit_research.blocking optimize --output results/cocycle_blocking_optimize.json
python -B -m normal_orbit_research.blocking recognize --output results/cocycle_blocking_recognize.json
```

After a failed span optimum and all requested tree gauges, the native seed
stage can optionally try extrema of the **minimum-span face**. The
optimal matching gives eight difference constraints per tetrahedron; two
nonnegative shortest-path searches per root produce other exact optima.
Roots in the same zero-weight strongly connected component are skipped.
Every proposed disc still passes the unchanged source-bound verifier.
Use `normal_seed_decide(..., face_roots=4)`,
`recognize(..., normal_seed_face_roots=4)`, or `--normal-seed-face-roots 4`
to request four roots. This defaults to zero because measured complete calls
were slower, despite new native coverage. It is skipped when optimization is disabled.
The shared work allowance covers all candidates and replay. An unsuccessful
bounded search remains inconclusive; tied optima can have different topology.

Reproduce the source/topology audit and complete recognition measurements:

```sh
python -B -m normal_orbit_research.face audit --output ../synthesis/data/cocycle-face-audit.json
python -B -m normal_orbit_research.face recognize --output ../synthesis/data/cocycle-face-recognize.json
```

The audit requires optional Regina for independent topology controls.
See the article's `cocycle_face.tex` section for the exact optimal-face
characterization, complexity, coverage and unsuccessful-search overhead.

The native stage now also accepts a **primitive connected annulus** in the
source knot exterior. One boundary circle must be inessential on the boundary
torus; capping it yields a compressing disc. This requires the existing
independent source, primitivity, connectedness and orientability checks.
Euler zero alone is insufficient.

These proofs use `diagram-cocycle-annulus-v1` and replay through
`verify_normal_seed_certificate`. Their stored surface remains an annulus:
`compressing_discs` is zero and the stage records `unknot_witness: annulus-cap`.
No expanded boundary trace or normal coordinates for the capped disc are
needed in production. Legacy disc certificates keep their original rules.
Use `annulus=False`, `normal_seed_annulus=False`, or
`--normal-seed-no-annulus` to disable this criterion. The whole native stage
remains optional, and face search still defaults to zero roots.

```sh
python -B -m normal_orbit_research.annulus audit --output ../synthesis/data/cocycle-annulus-audit.json
python -B -m normal_orbit_research.annulus recognize --output ../synthesis/data/cocycle-annulus-recognize.json
```

The audit requires optional Regina. It also expands only small fixture
boundaries to check the individual boundary-circle homology classes; that
control is absent from recognition and certificate replay. The earlier tree,
blocking-flow and optimal-face research drivers explicitly disable annulus
recognition to retain their original comparison criteria.

### Optional planar boundary caps

`normal_seed_decide(..., planar=True)` additionally checks whether a connected
coherent candidate is planar and has exactly one essential boundary circle.
Capping its inessential circles in a boundary collar produces a compressing
disc. This can recognize negative-Euler candidates: for example, the existing
five-crossing optimized-positive fixture has a planar seven-boundary surface
at tree trial 2, before span minimization.

The new `diagram-cocycle-planar-v1` certificate carries a torus homology basis
and a two-weight boundary orbit trace. Independent replay checks source
geometry, primitive class and connectedness through the existing cocycle
acceptance rules, then independently validates the basis and replays the weighted
trace. Boundary circles and their multiplicities remain compressed. The
stored surface can have zero disc components; its witness is `planar-cap`.
No normal-coordinate vector for the capped disc is extracted.

Use `recognize(..., use_normal_seed=True, normal_seed_planar=True)` or
`python -B -m fastunknot recognize INPUT.json --normal-seed --normal-seed-planar` to request it.
The new query defaults off. It adds boundary work to unsuccessful candidates,
so additional native coverage need not improve complete recognition time.
The seed API's `max_cycles` is shared across all boundary discoveries;
`max_work` includes discovery and independent positive replay. Existing disc
and annulus proofs need no boundary orbit query.

Reproduction from this directory (Regina is needed only for the audits):

```sh
python -B -m normal_orbit_research.planar audit --output ../synthesis/data/cocycle-planar-audit.json
python -B -m normal_orbit_research.planar survey --output ../synthesis/data/cocycle-planar-survey.json
python -B -m normal_orbit_research.planar recognize --rounds 5 --output ../synthesis/data/cocycle-planar-recognize.json
```

### Shared discovery geometry and positive-only source replay

The native search now retains the validated geometry produced during rank-one
seed construction. Tree trials and optional face/planar queries reuse that
per-call representation. Public seed and tree APIs retain their own input
validation and existing result formats.

Raw and optimized candidates first receive a cell-count prefilter from their
coherent heights: sum absolute global edge differences, subtract global face
spans, and add tetrahedral spans. This computes Euler characteristic without
expanding normal pieces. It is discovery code, not a source or connectedness
certificate. Possible disc and annulus positives still receive full independent
cocycle replay; planar positives still receive full source and boundary replay.
No verifier accepts cached geometry from the producer. Continuing misses are
still inconclusive, and no negative knot claim follows from the prefilter.

The candidate schedule and defaults are unchanged. Shared guard totals change:
continuing searches avoid repeated preparation and negative replay, while an
immediate positive pays for the cheap prefilter before its existing verifier.
The comparison driver loads the old native-search body from its recorded Git
commit and checks that it reproduces the previous audit before timing it.

```sh
python -B -m normal_orbit_research.reuse audit --output ../synthesis/data/cocycle-reuse-audit.json
python -B -m normal_orbit_research.reuse survey --output ../synthesis/data/cocycle-reuse-survey.json
python -B -m normal_orbit_research.reuse recognize --rounds 9 --output ../synthesis/data/cocycle-reuse-recognize.json
```

The callable `fastunknot.cocycle_euler.maximize_cocycle_face_euler` stage now
maximizes Euler characteristic over the **entire certified minimum-span face**,
provided every global edge has at least two face incidences. It accepts a finite
triangulation, coherent integral tetrahedral heights and a verified span
certificate, and returns an optimal surface in the existing span format plus
an independently checkable arithmetic flow dual. The new network uses
O(N² log N) indexed arithmetic operations and polynomial binary arithmetic;
its capacities depend on face incidence counts, not height magnitudes.

This is a restricted optimization API, not a new recognition verdict. Its
negative optimum does not establish knottedness: the unknot given by the
2-strand braid `[1, 1, -1]` has maximum Euler characteristic -1 on this face.
Positive surfaces still need the existing source-bound disc or annulus check.
The native portfolio keeps its current candidate schedule and defaults; the
new optimizer is available for explicit research and candidate construction.
Reproduce the source/Regina/dual audit with
`python -B -m normal_orbit_research.euler audit --output OUTPUT.json`, and the
comparison against all root extrema with the same driver in `benchmark` mode
and `--rounds 9`. These timings measure the full candidate-construction and
surface-replay pipeline, not complete knot recognition.

Euler optimization now contracts strongly connected components of zero-slack
constraints before routing flow. These components force relative potentials
throughout the entire feasible face; one-way tight edges do not. Equivalent
objective terms are combined, redundant constraints are removed, and two
spanning trees lift the resulting dual to the original vertices. The existing
arithmetic checker receives a full original-model certificate and is unchanged.
If every component is a singleton, the solver retains its full-network path.
No height or flow unit is expanded, including during dual reconstruction.
The geometric worst-case bound remains polynomial; a forced-cycle family
reduces from n-1 augmentations to zero with linear graph work for lifting.
Reproduce the source comparison and cycle-family counts using
`python -B -m normal_orbit_research.quotient audit --output OUTPUT.json`, and
candidate-pipeline timings with `benchmark --rounds 5` in the same driver.
The native recognition schedule and its default options remain unchanged.


The optional `--normal-seed-shellings` switch simplifies the finite exterior
before native cocycle discovery. In Python, pass `normal_seed_shellings=True`
to `recognize` or `shellings=True` to `normal_seed_decide`. This switch requires
the native stage to be enabled (`--normal-seed` / `use_normal_seed=True`).
Each move removes an embedded boundary tetrahedron only when its intersection
with the boundary is exactly a nonempty proper union of facets. Extra boundary
vertices or edges invalidate the move. The outer `diagram-shelling-witness-v1`
proof stores the canonical source, stable removal indices and a disc, annulus
or planar witness on the reduced exterior. Independent replay verifies the
whole source-to-surface chain without importing the simplifier or Regina.

Shellings default to off: fewer tetrahedra can change bounded candidate
coverage and need not reduce complete recognition time. Misses still use the
existing fallback. This does not establish a general subexponential or
quasipolynomial algorithm. After initial geometry preparation, shelling
selection uses O(N log N) indexed comparisons and O(N) storage; its independent
trace replay adds O(N) indexed graph work. The trace has O(N log N) bits.
Reproduce the topology/source audit with
`python -B -m normal_orbit_research.shellings audit --output OUTPUT.json`, and
complete forced-recognition timings with `recognize --rounds 5` in that driver.


Finite-manifold validation now computes vertex-link Euler characteristics
from an incidence census. Signed global edges already determine the two
oriented ends of every edge, including loops at a single vertex. For each
vertex link, count triangle corners F, edge ends V and boundary sides B;
then `2*chi = 2*V - F - B`. Reciprocal faces, edge reversal, edge links,
orientability, connectedness and the single torus boundary are still checked.
Ideal or singular vertices receive the same rejection as before.

This removes two redundant union-find structures and the per-link sets. For
N tetrahedra, P paired faces and b unpaired faces, union-find nodes fall from
34N+b to 10N+b; paired-face unions fall from 15P to 6P. The new link census
uses O(N) indexed operations and storage after the existing global geometry
has been obtained. Geometry output, certificate hashes, guard counts and
recognition settings are unchanged. Reproduce the comparison with
`python -B -m normal_orbit_research.link_census audit --output OUTPUT.json`,
and full recognition plus proof-replay timings using `recognize --rounds 5`
in the same driver. General subexponential/QP recognition remains open.

The supplied-coordinate `normal_surface_topology` API now tries a finite
coorientation proof before counting orbits of doubled coordinates. One bit
per incident global-edge block must change exactly across reversing normal
arc pairings. A valid assignment trivializes the orientation cover, so its
component count is twice the already verified base count. Success produces
`normal-surface-topology-v4`, with a strictly checked finite double proof;
the independent checker accepts the previous formats too. Failure is
inconclusive and preserves the old double query and complete result exactly.
Pass `coorientation=False` to restore the old query schedule.

The finite test adds O(N log N) integer comparisons/operations for N tetrahedra
and never expands sheet multiplicities. Existing multiplicity lifting and
optional boundary classification still apply. On the 256-tetrahedron layered
example, recorded events fall from 166,438 to 83,478 and producer plus checker
plus proof serialization improves by 1.967x. The complete 1,275-vector batch
is effectively neutral (1.003x); small inputs can regress. These are supplied
normal-surface API timings, not complete knot-recognition timings. Reproduce
the 5,100-configuration audit and isolated timings with
`python -B -m normal_orbit_research.coorientation audit --output OUTPUT.json`
and `benchmark --rounds 5` in the same driver. The separate corpus timing
driver is `../synthesis/data/coorientation_corpus_benchmark.py`. The proof,
limits and negative timing results are explained in article section 123.

Both `count_orbits` and `normal_surface_topology` also accept
`sweep_direction='forward'` (the unchanged default), `'reverse'`, or `'wide'`.
The reverse mode reflects the whole interval universe before AHT reduction.
Its proof binds the original input and records one independently checked
reflection event. Interval proof versions 3 and 4 retain the Fine–Wilf and
classical AHT merger thresholds respectively; old versions remain accepted.
No integer point is expanded, and reflection adds O(k) integer operations
for k pairings. Normal-surface multiplicity and boundary proofs still apply.

The optional wide mode compares initial terminal carrier widths and reflects
only when the left end is wider. On a 256-tetrahedron layered meridian, the
base trace falls from 82,960 to 2,311 events. This heuristic can lose: the
full 1,275-vector corpus grows from 182,925 to 189,742 events, and a concrete
surface uses fewer cycles but more events. Forward therefore remains the
default. This initial choice has no guarantee relative to the better sweep
and is not a progress-based adaptive race. Reproduce the compatibility audit
and isolated producer/replay/serialization timings with
`python -B -m normal_orbit_research.direction audit --output OUTPUT.json`
or `benchmark --rounds 5` in that driver. Article section 124 proves the
reflection rule and records the ordering counterexample and timing results.

The additional `sweep_direction='race'` mode now tries both directions with
geometrically increasing cooperative-checkpoint allowances. Width chooses
the first attempt only. A failed attempt is discarded, and the successful
answer retains exactly the corresponding fixed-direction certificate.
Independent checkers and the forward default are unchanged.

For k pairings on an M-point universe, the initial allowance is
`L = 8*(k+1)*(M.bit_length()+1)`. If W is the smaller complete checkpoint
count of the two fixed directions, unlimited attempt work is at most
`12*max(L,W)`, plus k+1 startup checkpoints. This is a checkpoint guarantee;
it is not a constant-factor wall-clock or elementary-bit-operation bound.
All begun cycles, including interrupted attempts, consume `max_cycles`.
The returned `cycles` and `race_*` statistics include scheduling work;
ordinary structural statistics describe the winning or last incomplete run.
Incomplete structural counters can lag an interrupted helper; use the race
checkpoint and cycle counters for exact interruption accounting.
No incomplete trace becomes a certificate, and caller cancellation propagates.

Article section 125 proves the bound and reports the restart costs. The
audit preserves all 5,100 default surface records, checks 5,100 race results,
and validates 1,210 literal interval systems and checkpoint inequalities.
The policy remains optional: restarts and callback accounting can exceed
the gains from choosing a better order. Reproduce with
`python -B -m normal_orbit_research.race audit --output OUTPUT.json` or
`benchmark --rounds 5` in the same driver.

`normal_sector.discover_in_sector(triangulation, allowed_types)` now discovers
normal vertex candidates in a supplied compatible quadrilateral sector.
Each allowed type is `(tetrahedron_index, type_index)` with type 0, 1 or 2;
at most one type may be allowed in each tetrahedron. The default Q-ray phase
is complete for positive canonical Euler characteristic. Request
`phase='standard'` to enumerate every non-link standard vertex ray. Positive
Euler values still undergo the existing essential-disc check.

The triangle-equality contraction gives at most 9k variables and 4k equations
for k allowed types. Standard enumeration chooses the smaller of exact
positive-support enumeration and a potential arrangement in the quadrilateral
matching nullspace. `enumerate_sector` exposes both methods for comparison.
`normal_sector_verify` independently reconstructs the dense matching model
and checks witnesses or restricted exhaustion. Negative replay repeats a search;
it is not claimed polynomial in the length of a short negative transcript.

Results distinguish `DISC_FOUND`, `NO_POSITIVE_EULER`, `POSITIVE_EULER_ONLY`,
`NO_VERTEX_DISC_IN_SECTOR` and `INCONCLUSIVE`. None is an unqualified knot
verdict. `sparse_disc_search` searches every sector up to a supplied support
cap; its exhaustion remains support-qualified. `max_bases` counts attempted
linear systems, and `max_orbit_cycles` applies per positive candidate.
Cancellation callbacks can provide a shared limit. A diagram consumer must
authenticate the supplied triangulation as its knot exterior before using
a positive witness for recognition.

All 1,269 maintained tests pass. The current-tree oracle comparison covers
1,718 sectors in both phases; independent producer-disabled replay covers
962 certificates. Article section 126 proves the support kernel, height bound,
adaptive search counts and the dense layered-meridian obstruction. The incoming
batch also supplies native-tested observer ideas; a reflection-vocabulary
counterexample is retained before promoting the delivered transversal checker.
Reproduce complete supplied-sector discovery timings with
`python -B -m normal_orbit_research.sectors --rounds 5 --output OUTPUT.json`.

`normal_topology.normal_topology_spectrum(triangulation, coordinates)` now
returns the complete abstract component-type spectrum of a supplied normal
surface, using two additive weights: Euler characteristic and actual boundary
circle count. Rows contain `chi`, `boundary_components`, `orientable`, binary
`multiplicity`, and either `genus` or `crosscaps`. A boundary orbit transversal
provides one marker per circle; weighted base and orientation-double histograms
then recover the orientability split. The zero signature has its own equation
to distinguish tori and Klein bottles. No component population is expanded.

The default `reduce_core=True` peels vertex links and divides quadrilateral
content before orbit discovery, then restores the original types with the
correct one-sided scaling rule. Set `reduce_core=False` for the direct observer.
All orbit discoveries share `max_cycles`; callback checks cover compilation
and verification. Incomplete runs return no spectrum or certificate.
`normal_topology_verify.verify_normal_topology_spectrum` reconstructs the
original source, checks the decomposition and weighted proofs, and verifies
typewise covering and restoration equations independently of their producers.
The CLI is `python -m fastunknot.normal_topology census INPUT --certificate`
and `python -m fastunknot.normal_topology verify INPUT CERTIFICATE`.

The least-representative compiler explicitly supports monotone universe
reductions. It rejects global reflection events, even when the corresponding
orbit-count proof is valid; its discovery path explicitly selects forward.
This fixes the delivered checker’s false-transversal counterexample. Supported
events are checked individually rather than inferred from a version tag.

All 1,312 maintained tests pass; 5,100 full spectra match the maintained
component oracle and 1,395 fresh Regina certificate checks pass. The measured
coordinate-census comparison is mixed: large mixtures and peeled links improve,
while primitive layered examples regress by about 5–9%. The coordinate reference
also returns embedding data. Abstract type alone does not establish boundary
essentiality, diagram provenance or attachment maps. Article section 127 proves
the observer and its trace contract and records the full timing tradeoffs.
Reproduce with `python -B -m normal_orbit_research.spectra audit --output OUTPUT`
or `benchmark --rounds 5` in the same driver.

The disc-count API now tries a checked unit-pivot support ray after its existing
vertex-link and quadrilateral-gcd reduction:

```python
from fastunknot.normal_disk_kernel import normal_compressing_disk_count
result = normal_compressing_disk_count(triangulation, coordinates,
    record_certificate=True, unit_ray=True)
```

A successful triangular unit-row transcript proves that the primitive core is
connected. Its Euler characteristic and mod-two boundary class then give the exact
essential-disc count, including multiplicity, without orbit discovery. Success
uses `normal-disc-count-v2` and independent replay; old v1 proofs remain accepted.
The default is `unit_ray=True`. A failed gate uses the previous complete observer;
`unit_ray=False` reproduces the old schedule and result. Pure links retain their
old proof. `max_cycles=0` permits the algebraic path because it bounds orbit
cycles. Callback cancellation still propagates. Rank-one supports without an
exposed unit pivot may miss this sufficient gate.

All 1,317 maintained tests pass. On 2,550 corpus configurations every count agrees
with the frozen producer and component oracle; 1,878 use the shortcut. Complete
production, replay and serialization improves 31.39x on the layered-256 count
query. Supplied-sector discovery gains 1.07–1.30x; this is not a whole knot
recognition timing or a general complexity bound. Reproduce from `fast/`:

```sh
python -B -m normal_orbit_research.unit_rays audit --output /tmp/unit-ray-audit.json
python -B -m normal_orbit_research.unit_rays benchmark --rounds 5 --output /tmp/unit-ray-benchmark.json
```

The [unit-ray article](../synthesis/unit_ray.tex) proves connectedness, scaling,
primitive disc classification, the all-size Fibonacci family and protocol
semantics. The [mathematical review](../synthesis/completion_theorems.tex) preserves
other results from reports 64–69, including results not selected for native code.

The topology observer now enables `coorientation=True` by default. After a
complete base weighted query, a checked finite block colouring can trivialize
the normal double into two copies. The Euler and boundary-marker point weights
pull back unchanged, so the doubled histogram has the same signatures and twice
the multiplicities. This skips the second weighted discovery and replay; a missed
colouring retains the complete previous result. A miss does not imply
nonorientability. `coorientation=False` or the CLI `--no-coorientation` reproduces
the old schedule. All actual discoveries share the cycle allowance.

Derived evidence uses `normal-topology-spectrum-v2` with a strict source-bound
`normal-topology-double-coorientation-v1` inner proof. Independent replay checks
the original graph and certified base histogram; it does not call the colouring
planner or any discovery. Legacy v1 certificates remain accepted. Pure reduced
vertex links retain their zero-query v1 proof.

All 1,322 tests pass. Every one of 5,100 corpus configurations agrees with the
frozen baseline and component oracle; 1,088 skip the double query. Fresh Regina
checks match 664 vectors and independently verify 1,395 certificates. Isolated
production, replay and serialization improves layered inputs 1.87–2.26x, and the
primitive coordinate-reference comparison 1.76–2.10x. Both the noisy initial
fallback measurement and a longer isolated repeat showing small overhead are
retained. These are supplied-vector timings; source recognition coverage and the
general QP question remain unchanged. Reproduce from `fast/`:

```sh
python -B -m normal_orbit_research.coorientation_spectra audit --output /tmp/weighted-spectrum-audit.json
python -B -m normal_orbit_research.coorientation_spectra benchmark --rounds 5 --output /tmp/weighted-spectrum-benchmark.json
```

The [weighted coorientation proof](../synthesis/weighted_coorientation.tex)
establishes the general additive-weight cover theorem and explains its two-weight
application, strict protocol, complete fallback and binary work. Raw records,
source pins and reproduction scripts are `../synthesis/data/weighted-coorientation-*`.

Automatic standard-sector enumeration now uses exact minimum envelopes when
quadrilateral matching nullity is one or two. It projects corner potentials once,
then lifts only genuine minimum changes and feasible section endpoints. These
are exactly all nonlink standard rays; no pairwise crossing or spurious-rank filter
is needed. Higher-nullity auto selection and quadrilateral enumeration retain
their old paths. Explicit `arrangement`, `supports` and `envelope` methods are
available; `envelope` requires the standard phase and nullity at most two.
`discover_in_sector` also accepts `method='auto'` or an explicit method.

```python
from fastunknot.sector_envelope_certificate import certify_sector_enumeration
from fastunknot.sector_envelope_verify import verify_sector_envelope_certificate
answer = certify_sector_enumeration(triangulation, allowed_types, max_rays=None)
if answer['status'] == 'COMPLETE':
    assert verify_sector_envelope_certificate(triangulation, answer['certificate'])
```

The independent `normal-sector-envelope-v1` checker reconstructs an uncontracted
matching graph, checks the whole feasible section and minimum envelopes, and
rejects omitted rays. It imports no envelope planner or sector enumerator.
`max_bases` counts begun actual output lifts on this path; partial iteration raises
`SearchLimit`. `max_rays` returns inconclusive without a partial coverage proof.
The cooperative callback bounds additional work. Coverage is for this supplied
sector, and essentiality/diagram correspondence remain separate checks.

All 1,351 tests pass. The native audit checks 9,344 eligible selected sectors
against complete frozen standard-ray lists, 9,360 auto/direct comparisons and
15 fresh Regina enumerations. Isolated full kernel construction, enumeration and
serialization improves 197.22x on the capped size-32 family. Complete supplied-sector
disc discovery with independent replay improves 17.28x; the two timing scopes
are reported separately. Empty and no-break controls and A/A arms are retained.

```sh
python -B -m normal_orbit_research.envelopes audit --fresh-regina --output /tmp/envelope-audit.json
python -B -m normal_orbit_research.envelopes benchmark --rounds 5 --output /tmp/envelope-benchmark.json
```

The [minimum-envelope article](../synthesis/minimum_envelopes.tex) proves the
face correspondence, linear output bound, exact coverage protocol and all-size
capped component formula. The [incoming mathematical review](../synthesis/incoming_contexts.tex)
preserves reports 70–75, including results without native timing gains, and proves
two further interface limitations: positive unrestricted anchor relaxations from
interior vertices, and exponential weighted rooted compatibility even at zero
cycle overlap. No general QP recognition theorem follows.


The STANDARD sector iterator now selects report 80's exact planar minimum
subdivision at matching nullity three. Nullity one/two retain the existing
minimum envelopes; higher nullity retains support/arrangement selection.
`method='planar'` is explicit, and `sector_planar_verify` independently checks
complete area/length coverage without the producer's clipper. Reusable
`PreparedSectorSource` remains explicit: one-shot queries keep native dense
preparation. All 1,391 tests and 9,807 eligible selected oracle comparisons
pass. At Fibonacci base size 16, complete enumeration improves about 493x,
while disc discovery with full proof replay improves 4.68x. Smallest discovery
cases regress; these scopes and A/A controls are retained separately.

```sh
python -B -m normal_orbit_research.planar_sectors audit --fresh-regina --output /tmp/planar-audit.json
python -B -m normal_orbit_research.planar_sectors benchmark --rounds 5 --output /tmp/planar-benchmark.json
```

The optional `normal_seed_edge_span=True` / `--normal-seed-edge-span` stage
minimizes coherent edge penalty first and span second, with independent
arithmetic and diagram-source proofs. An existing minimum-span dual avoids
the second flow when valid. It completes 84/85 audit cases, retains 24/85
positive answers, and adds measured time on misses, so the default stays off.
See [edge-first theory](../synthesis/cocycle_lex.tex),
[planar theory](../synthesis/planar_sectors.tex), and
[report 81 refinements](../synthesis/planar_overlay_refinements.tex).
The latter preserves sharper crossing, effective-support and Q-corner Euler
theorems; its alternative patch and proposed aggregated Euler precheck are
not installed. No general QP recognition bound follows.


Automatic STANDARD discovery at nullity three now tests projective Q-corners
before building the minimum overlay. It refines only after the corner
prelude finds no disc, reuses the chart, and shares one actual-ray cap across
both stages. Exhaustion still includes every standard ray and uses the
existing independent certificate checker. Complete enumeration retains its
previous canonical order. The bounded-support search also reuses one
producer matching kernel across Q and STANDARD phases of each sector;
independent source checks remain in place.

All 1,396 tests pass. The audit checks 9,807 complete adaptive ray sets and
463 discovery queries: all 44 observed positives finish before refinement,
and all 419 negative proofs replay. Complete discovery with proof replay
and serialization improves 1.64–2.68x on the tested two-cap families against
the preceding planar release. Full negative, low-nullity and enumeration
controls stay near parity. A longer repeat records 4–5% kernel-reuse gains
in the two supplied capped-exterior bounded-support scans. These are local
API scopes; the default diagram portfolio is separate.

```sh
python -B -m normal_orbit_research.planar_adaptive audit --fresh-regina --output /tmp/adaptive-audit.json
python -B -m normal_orbit_research.planar_adaptive benchmark --rounds 5 --output /tmp/adaptive-benchmark.json
```

[The progress-driven discovery chapter](../synthesis/planar_adaptive.tex)
proves complete fallback and uniform first-corner meridian selection on the
Fibonacci family. It also records the general arrangement bound
`poly(t+k+B) * (1+k)^O(d)`: logarithmic matching nullity permits complete
local QP enumeration, while a complete global sector producer remains open.


The optional `normal_seed_sector_radius=1` or `2` recognition switch searches
nearby compatible type assignments after coherent misses; its CLI flag is
`--normal-seed-sector-radius`, used with `--normal-seed`. The default is zero.
Exact signed residuals in the full matching quotient group zero columns and
opposite proportional pairs. Coordinate-face dominance preserves every
standard ray in the full radius-one/two window, including replacements.
Queries share the native work and remaining orbit limits. Positive results
use the existing `diagram-normal-disc-v1` proof; the independent source
checker also supports its transport through boundary shelling traces.

The 85-source audit preserves all disabled outputs exactly and increases
native witnesses from 24 to 31 (seven added cases, six distinct canonical
PD codes). All seven discs receive fresh Regina confirmation. All 1,401
tests pass. The motivating radius-two disc is found after 31 filtered
queries in about 0.41 seconds, compared with 4,920 unfiltered queries in
36.46 seconds. Complete small-portfolio recognition is slower with extra
windows, and 34 audit cases hit the work cap; keep the stage optional.
A missed or capped window never supplies a knot verdict.

```sh
python -B -m normal_orbit_research.sector_windows audit --fresh-regina --output /tmp/sector-window-audit.json
python -B -m normal_orbit_research.sector_windows benchmark --rounds 5 --output /tmp/sector-window-benchmark.json
```

[Signed residual theory](../synthesis/sector_windows.tex) proves full small-window
coverage, the candidate bound, and conditional local QP enumeration for
logarithmic initial nullity/radius. A complete global centre/distance theorem
remains unproved. The separated native and full-recognition timings, noisy
control repeat and producer-disabled source replay are retained.


Residual-window queries now reuse the old Q kernel, column decompositions and
source triangle potentials. Each candidate imposes at most two replacement
constraints in at most `d0+2` parameters, recovers the native free-coordinate
basis, and constructs the exact projected standard cone. Empty Q kernels
finish without another geometry build. The generic higher-nullity fallback
and independent positive source checks remain available.

All 1,404 tests pass, including exact updated/fresh basis and ray comparisons
and both generic methods at nullity four. The 85-source audit preserves all
31 native witnesses; shared-work caps fall from 34 to 30. Paired complete
recognition with radius-two windows enabled improves about 1.25–1.43x against
the preceding rebuilding implementation on tested window-search cases.
Early positives stay near parity. Radius zero remains the default: enabling
windows still costs more than the small-input fallback without them.

```sh
python -B -m normal_orbit_research.window_basis audit --fresh-regina --output /tmp/window-basis-audit.json
python -B -m normal_orbit_research.window_basis benchmark --rounds 5 --output /tmp/window-basis-benchmark.json
```

[Matching-update theory](../synthesis/window_basis.tex) proves full augmented
kernels, exact replacement restrictions, canonical gauge and projected
geometry. Frozen baseline/current source checks, positive certificate
replay and the longer microsecond control are retained in the article data.

Updated windows now compile the source Euler functional once and screen every
Q corner at matching nullity at most three before constructing standard
geometry. Empty or nonpositive sectors need no ray lifts; a positive corner
resumes the existing complete standard search. Above nullity three, the
existing generic fallback remains. Positive disc queries share the source
and freshly validated coordinate analysis with a private observer. Public
disc APIs and independent source-proof reconstruction retain validation.

All 1,407 maintained tests pass. The 85-source audit preserves all disabled
outputs, enabled verdicts and 31 native positives, with seven fresh Regina
disc checks. Work caps fall from 30 to 28. Complete enabled recognition is
1.23–1.32x faster on the measured window cases than the preceding updated
kernel implementation. A 60-call repeat resolves a noisy native timing row.
The default radius remains zero; these local gains do not prove general
quasi-polynomial recognition or justify enabling windows on small inputs.

```sh
python -B -m normal_orbit_research.window_euler audit --fresh-regina --output /tmp/window-euler-audit.json
python -B -m normal_orbit_research.window_euler benchmark --rounds 5 --output /tmp/window-euler-benchmark.json
```

[Euler-screening theory](../synthesis/window_euler.tex) derives the exact
source functional, canonical formula and complete corner exclusion. Raw
pilot/final/repeat records, source snapshots and producer-disabled positive
replay are retained under `../synthesis/data/window-euler-*`.

Residual windows now carry their thin replacement and canonical-gauge row
operations through lazily cached sparse potential modes. Each corrected
column is `P_j-P_S*c_j`; cancelling pairs and old basis modes are combined
with the exact recorded row coefficients. This reproduces direct source
projection at every physical corner while avoiding repeated wide scans.
Source transposition and each needed correction are prepared at most once;
interrupted construction never publishes a partial column.

All 1,408 maintained tests pass, including exact propagated/direct forms,
fresh source bases/rays and genuine nullity-four fallbacks. The 85-source
audit preserves all verdicts, all 31 positives and all 28 work-capped cases,
with seven fresh Regina disc checks. Small complete-recognition timings are
close to parity: a longer trefoil repeat gives only a 1.015x gain. The
improvement is in the amortized projection bound; it is not a uniform timing
claim. Guard counts can increase with cache preparation. Radius zero stays
the default, and general quasi-polynomial recognition remains unproved.

```sh
python -B -m normal_orbit_research.window_modes audit --fresh-regina --output /tmp/window-modes-audit.json
python -B -m normal_orbit_research.window_modes benchmark --rounds 5 --output /tmp/window-modes-benchmark.json
```

[Cached-mode theory](../synthesis/window_modes.tex) proves exact propagation,
explains lazy cache ownership and separates preparation, arithmetic, storage,
bit costs and independent source replay. Raw pilot/final/repeat evidence and
recoverable historical source snapshots are in the article data.

Projected windows now retain standard constraints and potentials as exact
sparse linear forms in the free Q coordinates. Low-dimensional lifts,
envelope lines and planar chart projections visit only nonzero coefficients.
The complete dense sequence remains available to generic rank calculations;
coordinate-face restrictions can index sparse rows directly. Independent
source validation and positive certificate formats remain unchanged.

All 1,411 maintained tests pass. Genuine nullity-one/two/three producers run
with dense form iteration disabled; nullity-four generic methods and huge
scaled lifts still agree with fresh source geometry. The 85-source audit
preserves all verdicts, guard counts and 31 positives, with seven fresh
Regina disc checks. A longer complete-recognition repeat shows gains of
about 4.6% on trefoil and 5.2% on figure-eight against the preceding cached
mode implementation. These include the complete fallback. Windows remain
off by default; no general quasi-polynomial bound follows.

```sh
python -B -m normal_orbit_research.window_geometry audit --fresh-regina --output /tmp/window-geometry-audit.json
python -B -m normal_orbit_research.window_geometry benchmark --rounds 5 --output /tmp/window-geometry-benchmark.json
```

[Sparse geometry theory](../synthesis/window_geometry.tex) gives the unchanged
complete equations, exact access paths and `O((k+p)*(d+1))` stored-coefficient
bound. Full timing, source and replay evidence is retained in the article data.

Window disc proofs now use a lazily constructed verifier-owned source context.
It snapshots and independently validates the actual source, compares every
query source with type-preserving structural equality, and validates each
coordinate vector and reduction afresh. Only independently derived source
geometry and boundary homology are reused. Producer preparations and analyses
are never accepted by this context. Fresh public replay and final canonical
diagram-source verification remain available; ordinary proof formats stay
unchanged.

All 1,415 maintained tests pass. Source mutation, equal Boolean/integer aliases,
proof tampering, enormous scale and interrupted cache construction are covered.
The 85-source audit preserves all verdicts and 31 positives, with seven fresh
Regina disc checks; work caps fall from 28 to 22. Complete enabled-recognition
gains are 1.18–1.26x on the measured window cases. A longer native/full trefoil
repeat confirms about 1.22x gains with stable controls. Legacy component-based
version-one proofs also receive fresh/context producer-disabled replay.
Radius zero remains the default; no general quasi-polynomial theorem follows.

```sh
python -B -m normal_orbit_research.disc_context audit --fresh-regina --output /tmp/disc-context-audit.json
python -B -m normal_orbit_research.disc_context benchmark --rounds 5 --output /tmp/disc-context-benchmark.json
```

[Independent replay theory](../synthesis/disc_context.tex) proves fixed-source
acceptance equivalence and states ownership, per-proof work and cost limits.
Raw source/timing/repeat records and disabled-context publication replay are
retained in the article data.

Euler screening now refines its objective only after a nonpositive first Q
corner. It groups equal projected forms within each source vertex, absorbs
anchors and constant groups into the linear term, and evaluates later corners
using distinct nonzero differences. Empty/scalar sections, early positive
progress and generic higher-nullity paths retain their previous behavior.

All 1,417 tests pass, including exact direct/grouped/source Euler comparisons,
huge scale, anchor-gauge invariance and unused-grouping prevention. The source
audit preserves all 85 verdicts and 31 positives, with seven fresh Regina discs,
22 caps and 32 completed local misses. The longer timing repeat is near parity;
no reliable small-case wall-clock gain is claimed. The concrete improvement is
`O(T+k^2)` post-projection scalar arithmetic at nullity at most three, with
source projection, hash/index costs and coefficient bits separately charged.
Windows still default off; global quasi-polynomial recognition remains open.

```sh
python -B -m normal_orbit_research.euler_aggregate audit --fresh-regina --output /tmp/euler-aggregate-audit.json
python -B -m normal_orbit_research.euler_aggregate benchmark --rounds 5 --output /tmp/euler-aggregate-benchmark.json
```

[Grouped Euler theory](../synthesis/euler_aggregate.tex) proves the exact
anchor formula, source distinct-form bound and progress-driven cost accounting.
Pilot, final and repeat records are preserved in the article data.

The canonical Euler screen now covers matching nullity above three through
exact Q-hyperplane intersections. Each extreme direction selects one canonical
independent active subset, giving deterministic deduplication with polynomial
work per candidate. A complete nonpositive screen uses at most `choose(k,d-1)`
candidates and avoids the larger standard arrangement. Positive sectors retain
the complete fallback; a partial scan cannot exclude a sector.

Automatic supplied-sector discovery above nullity three also tries Q rays
first. It returns the existing independently replayable Q exclusion certificate
when that phase excludes positive Euler, or resumes standard discovery after
positive nonessential Q rays, sharing the candidate allowance across phases.
Explicit standard enumeration keeps its previous behavior. All 1,422 tests
pass. The 188-sector source audit agrees with native and retained standard
oracles; fresh Regina enumerations confirm all twelve exclusions across four
sources. Complete negative source queries gain 2.7–4.5x in paired measurements,
while one positive control is about eleven percent slower. These are local
source-query gains. All 85 diagram verdicts and work counts remain exactly
unchanged, and none of their windows enters the new generic branch. The
optional window stage still defaults off; a general subexponential recognition
bound remains unproved. Reproduce with
`python -B -m normal_orbit_research.generic_euler sector-audit --fresh-regina --output /tmp/sector-audit.json`
and the driver's `sector-benchmark`, `audit` and `benchmark` modes.

After a completed positive Q phase finds no essential disc, automatic generic
discovery now removes types absent from every Q ray and rebuilds the source
kernel. It dispatches by the feasible matching dimension: 22 retained source
sectors fall from nullity four to three and enter the planar producer, while
two fall from five to four. All 188 source verdicts and full standard surfaces
agree with the prior source oracles; fresh Regina enumerations confirm all
65 sectors with forced-zero coordinates. Four return a Q witness early and
61 receive recompilation. All 1,427 tests pass.

Reduced negative certificates retain the original allowed support and
full-width ray records. Their optional `q_support_certificate` is independently
replayed on the original source before the checker derives the retained
coordinates and reconstructs the reduced standard model. Incomplete or forged
Q support cannot authorize dropping coordinates. Legacy certificates still
use the full-source checker, and ordinary positive proof formats are unchanged.
Complete source queries, including respective independent replay and serialized
output, improve 3.86x and 23.86x on the measured dimension reductions; controls
and a reduction without dimension change remain near parity. This is a local
geometry improvement, with the original complete Q phase still charged. It
does not establish general quasi-polynomial knot recognition. Reproduce with
`python -B -m normal_orbit_research.feasible_span audit --fresh-regina --output /tmp/feasible-audit.json`
and the driver's `benchmark` mode.

Automatic standard discovery above nullity three now tries sufficient
polynomial matching implications before its generic Q phase. Canonical
reduced equations are recovered from the existing kernel; one-sided sign
propagation proves coordinate zeros. Only useful reductions compile a source
forest and exact matching-row provenance, then rebuild the source kernel.
The complete Q/standard fallback remains available at a mixed-sign fixed
point, which is not a proof of maximal support or a complete LP solver.

Negative proofs optionally carry `matching_support_certificate`. Independent
replay adds the stated actual source matching equations, requires cancellation
of all triangles, and validates each forced coordinate by exact nonnegative
Q coefficients. The final proof still states the original sector and restores
its coordinate width; partial matching proofs can compose with Q support
proofs on an authenticated intermediate sector. Ordinary positive proofs and
legacy full-source replay remain available.

All 1,433 tests and 34 focused tests pass. All 188 source verdicts and complete
standard surfaces remain; the procedure finds 126 oracle zeros in 65 selected
sectors and admits all 22 effective-dimension-three sectors without the
original Q prelude. Fresh Regina enumerations confirm the involved sources.
Complete affected source queries improve 1.16–1.61x over the preceding
complete-Q implementation, including provenance preparation, independent
replay and serialization. These are local source improvements, with no general
quasi-polynomial recognition claim. Reproduce using the
`normal_orbit_research.matching_support` audit and benchmark driver.

Report 79's native bounded Pachner search is now integrated. Integral cochain
transport, commitments/sleep search, connected regions, shared cover indexing,
causal projection/composition and source replay use the maintained move
primitives. `find_pachner_descent` completely decides bounded total-upward
descent with connected cover size `min(t,3U+3)` when uncapped. The formal
first-descent theorem gives `2^O(U) poly(t+B)` geometry; caps remain
inconclusive, and no bounded negative is a knot verdict.

`recognize(..., use_pachner_seed=True)` and `--pachner-seed` enable a new
source-bound positive disc stage after filters. CLI controls are
`--pachner-seed-max-upward`, `--pachner-seed-max-nodes` and
`--pachner-seed-max-work`. It probes the source before indexing bounded
covers and shares its node/work allowance with the later search. Only an
independently replayed `diagram-transport-disc-v1` witness returns `UNKNOT`;
local misses and caps continue the existing complete fallback.

All 1,499 tests and 66 focused integration tests pass. Exact source audits
match restarted endpoint classes and replay 124 retained endpoints plus
two strict one-up/two-down descents; fresh Regina confirms the source and
endpoint solid tori. First verified descent gains 37.7x and 79.7x on the
two measured sources, including replay and serialization. Thirteen actual
diagrams preserve all complete verdicts and exact disabled evidence. Their
small direct-search allowance adds no nonempty-diagram successes, and enabling
the stage adds about 0.21–0.23 seconds to three otherwise submillisecond
controls. It **defaults off**. The universal small-upward/terminal hypothesis
and general quasi-polynomial recognition remain open. Reproduce with the
`causal_research.native` audit, source-benchmark and diagram-benchmark modes.

Shared Pachner cover search now asks exact covering existence on demand.
A frame stores consumed original cells; a covering witness supports its
certificate but does not restrict future moves. Connected admissible footprints
are immediate witnesses. Disconnected footprints use duplicate-free rooted
reverse search, with completed positive/negative caches and no approximate
Steiner oracle. A capped or interrupted completion remains unknown.

`cover_backend='auto'` uses this oracle unless `max_regions` requests the
original complete-index cap. Explicit `indexed`/`oracle` backends remain
available; `max_oracle_states` caps aggregate rooted completion states.
Original geometric certificates and independent replay are unchanged.
All 1,506 tests and 27 focused tests pass. Complete source endpoint proofs
agree exactly with the frozen indexed release apart from the witness-cover
field. All 83 source endpoints, both strict descents and thirteen complete
diagram verdicts pass the fresh audit.

Under the same diagram checkpoint cap, completed moves rise from nine to
141, but no extra disc success appears. Budgeted wall-clock calls are slower
because actual move construction is more expensive than index checks.
The optional diagram stage stays off. Complete source descent ratios are
1.033 and 1.125 over the indexed release; no general recognition gain or
new asymptotic complexity class is claimed. Reproduce with
`causal_research.cover_oracle` audit, source-benchmark and diagram-benchmark.
The preceding `causal_research.native` byte-identity audit describes its
frozen integration release; the current cover-oracle audit supersedes it.

An explicit strict-descent epoch policy is available through
`pachner_epoch_seed_decide` or `recognize(..., use_pachner_seed=True,
pachner_seed_epochs=64)`. CLI: `--pachner-seed --pachner-seed-epochs 64`.
Zero epochs preserves the single-family policy. With epochs enabled, the
upward allowance applies per epoch, not to the concatenated trace. One
node/work allowance covers preparation, all epoch searches and positive replay.
Only independently replayed strict tetrahedron descents allow restarts; a
stationary or capped source remains inconclusive and uses complete fallback.

A genuine genus-one-miss diagram obtains a transported disc after 33 descents
from 54 to 21 tetrahedra. The full original-source proof has nine upward and
forty-two downward events in 51 steps, and independent replay rejects missing,
reordered or changed moves and input substitution. All 1,514 tests and 26
focused tests pass. The geometric restart count is bounded by the initial
tetrahedron count, but no small-upward universal reach or terminal theorem
is claimed. Epoch mode and the optional Pachner stage stay off by default.
Reproduce the actual-diagram audit with `causal_research.epochs`.

Epoch mode can periodically reoptimize the current source's integral vertex
gauge. API: `pachner_seed_regauge_interval=4`; CLI:
`--pachner-seed --pachner-seed-epochs 64 --pachner-seed-regauge-interval 4`.
The default zero interval preserves the preceding policy. The producer
anchors component constants and requires nonincreasing disc span. Its
independent `verify_cocycle_gauge` reconstructs source vertices and checks
the exact corner equation; it imports no optimizer or flow solver. Edge
changes are one global integer coboundary, so every cohomology period is
preserved, although the coherent normal fibre can change topology.

Mixed move/gauge proofs use `diagram-transport-disc-v2`, replaying every
geometric move and every gauge from the original input; old v1 move-only
proofs remain valid. No optimizer assertion, lower span or Euler value can
replace the final essential-disc certificate. Shared caps and complete
fallback remain, with no default activation of the optional stage.

The actual genus-one-miss disc now needs 24 rather than 33 descents, 83
rather than 191 nodes and about 32% fewer checkpoints. Six optimizer calls
produce three actual changes; its full v2 proof has 32 geometric moves
and three gauge steps. All 1,521 tests and 28 focused tests pass, including
source/potential forgeries, schema downgrade rejection, optimizer-disabled
replay and portable 9,000-bit common offsets. The precise source audit and
configured-call timings are in `causal_research.epoch_gauge`.

Explicit epoch mode can authenticate a primitive annulus cap with
`pachner_seed_annulus=True` or
`--pachner-seed --pachner-seed-epochs 64 --pachner-seed-annulus`.
The default is false. The adapter retains current-source minimum-span
witnesses at optimization checkpoints and discards them after geometry
changes. A zero-Euler candidate is accepted only by independent source,
matching, primitive-period and connectivity/optimality replay. A valid
nonprimitive minimum-span witness is explicitly rejected.

`diagram-transport-annulus-v1` carries the original source and complete
move/gauge chain plus the terminal primitive surface certificate.
`verify_transport_annulus_certificate` replays the exact final source and
uses the existing connected primitive annulus theorem to authenticate its
boundary cap. It imports no optimizer or source/move producer and stores
no fictitious normal vector for the capped disc. Existing v1/v2 normal-disc
proofs retain their final component authority.

The actual optimized-positive source now returns a certified annulus at
48,281 checkpoints and zero epochs, instead of reaching the two-million
work cap. All 1,529 tests and 36 focused tests pass, including a nonempty
move/gauge chain, topology/dual/source forgeries, valid doubled nonprimitive
arithmetic, CLI routing and cap-safe complete fallback. The other sampled
disc proofs and negative controls are preserved. All optional defaults
remain off; the general quasi-polynomial recognition bound is still open.
Reproduce the audit and configured-call timings with `causal_research.annulus`.

### Exact sector transcripts through binary integer transport

The independent sector-exhaustion checker now decodes its ray-count and Euler
fields with the same strict signed hexadecimal codec used by the component
proofs. Equivalent integer and hexadecimal values have identical mathematical
meaning. Booleans, floats, decimal strings, malformed encodings, changed counts
and incorrect support widths are rejected; allowed-type indices keep their
existing strict schema. A verified nested Q transcript is decoded before its
positive support is extracted, so a hexadecimal zero remains zero.

All 1,534 maintained tests and 24 focused tests pass. Tests use actual source
triangulations and cover all exhaustion statuses, nested support reductions,
producer-disabled replay, changed large binary values and cancellation.
This fixes certificate compatibility for compressed arithmetic; it does not
change the search policy or establish a new recognition complexity bound.
See [the bit-size proof and replay evidence](../synthesis/sector_integer_transport.tex).

### Two-row source matching implications

High-nullity automatic standard discovery now considers exact signed two-row
combinations after the existing one-row sign propagation. Rational interval
bounds find nonnegative active consequences, and source-equation provenance
uses the existing certificate schema and independent checker. The closure
has polynomial `O(k^4)` scalar work with polynomial bit cost; combinations
of three or more rows can still expose zeros that it misses. Complete fallback
and the original support statement remain authoritative.

The source pilot finds fifty extra reductions among 3,412 sectors on 48
triangulations. Two raw-nullity-four sectors bypass generic Q screening,
reach nullity-three adaptive discovery, and drop attempted candidates from
63 to seven. Their complete native source-query paired ratios are about
1.55 and 1.53, including preparation, proof replay and serialization.
The existing-reduction control is at parity; the unreduced control has
about five percent overhead in this sample. No full-recognition timing or
new general complexity theorem follows. All 1,540 tests and 22 focused
tests pass. The optional diagram geometry policy remains off.

Reproduce the source evidence from this directory with:

```sh
PYTHONPATH=. python -B -m normal_orbit_research.matching_pairs audit --output ../synthesis/data/matching-pairs-audit.json
PYTHONPATH=. python -B -m normal_orbit_research.matching_pairs benchmark --rounds 5 --output ../synthesis/data/matching-pairs-benchmark.json
```

The audit uses Regina for independent source-ray checks. See
[the theory, counterexample and measurements](../synthesis/matching_pairs.tex).

### Binary cut-open component connectivity

`fastunknot.normal_cut_complement.normal_complement_components` counts the
connected pieces after cutting a supplied valid normal surface. It represents
local quad-stack/triangle-arm chambers with at most `20*T` interval pairings,
regardless of the number of represented normal discs. Unlimited work is
polynomial in the source and binary coordinate size. Independent replay is
`fastunknot.normal_cut_complement_verify.verify_normal_complement_certificate`;
it reconstructs face regions without the chamber or orbit producers.

Parallel coordinates are retained: cutting along `m` parallel meridians gives
`m` pieces, while the retained Möbius-band vector gives `floor(m/2)+1`.
A capped query has no count or certificate. Source geometry retains the
existing finite compact orientable one-torus-boundary contract. The API
returns a count and optional source-bound proof; it does not return full cut
triangulations, boundary patterns, regluing maps or a knot verdict. It is not
called by recognition and establishes no new general recognition bound.

All 1,548 tests and eight focused tests pass. The audit agrees with 2,019
actual Regina cuts on 48 sources and independently checks thirteen large
binary cases, including a 16,385-bit coordinate certificate. At 1,024 copies,
the measured count task is about 74.9 times faster than an explicit Regina
cut-and-count baseline. Native Python replay is slower on the smallest
inputs; the baseline additionally constructs the expanded triangulation.
Reproduce from this directory (Regina is required only by the research driver):

```sh
PYTHONPATH=. python -B -m normal_orbit_research.cut_complement audit --output ../synthesis/data/cut-complement-audit.json
PYTHONPATH=. python -B -m normal_orbit_research.cut_complement benchmark --rounds 5 --output ../synthesis/data/cut-complement-benchmark.json
```

The theory, independent construction and missing hierarchy geometry are in
[cut_complement.tex](../synthesis/cut_complement.tex).

### Wholly prismatic cut components and a bounded conservative core

Pass `classify_prisms=True` to `normal_complement_components` to count components
that avoid the quad-chain endpoints and innermost triangle chambers. There
are at most six exceptional chambers per source tetrahedron. Every component
avoiding them is an interval bundle over an embedded normal midsection;
`prismatic_components` includes twisted bundles. `core_components` counts
components touching exceptions and is at most `6*T`; those components may
also be interval bundles. This is a sufficient classification, not a maximal
parallelity-bundle decomposition or an extraction of core geometry.

A second cone orbit query authenticates the classification. Both queries
share the cycle allowance, and the independent version-two checker charges
both traces against its replay operation limit. Default false preserves the
previous scalar API and version-one certificates. The full patterned-cutting
and recognition obligations remain open. The theory and published component
algorithms are discussed in [cut_products.tex](../synthesis/cut_products.tex).

The geometric pilot covers 5,241 cuts on 48 sources and 7,838 connected normal
midsections with consistent Regina cut signatures. The integrated audit matches
all classifications, all frozen disabled results and 157 legacy proofs. All
1,555 tests and 15 focused tests pass. At 65,536 meridians, compressed
classification is about 112 times faster than an explicit chamber-graph
union-find baseline, including native proof replay; small inputs are slower.
This is a classification task, not a full parallelity-bundle extraction.

```sh
PYTHONPATH=. python -B -m normal_orbit_research.cut_products audit --output ../synthesis/data/cut-products-audit.json
PYTHONPATH=. python -B -m normal_orbit_research.cut_products benchmark --rounds 5 --output ../synthesis/data/cut-products-benchmark.json
```

### Source-bound prismatic normal midsection inventories

`fastunknot.normal_prismatic_inventory.normal_prismatic_inventory` recovers
full normal midsection coordinates, Euler values and binary multiplicities
for wholly prismatic cut components. Core components remain counted only.
An additive marker plus normal-disc weight system distinguishes these classes;
independent replay is
`fastunknot.normal_prismatic_inventory_verify.verify_normal_prismatic_inventory`.
The checker reconstructs its own source weights and validates the entire
inventory. Connected doubles are retained rather than divided by their gcd.

A supplied `orbit_certificate` is checked against freshly owned chamber pairings
and reused without another orbit search. `max_cycles` must then be `None`.
Callbacks apply to weighted transport and verification as well as discovery.
An unfinished query has no inventory or certificate. This standalone operator
retains the one-torus source contract and does not supply core geometry,
interior attached parallelity regions, a knot verdict or a new recognition bound.

All 1,564 tests and 24 focused tests pass. The audit matches all 5,241 explicit
finite inventories and retains 57 source proofs, nine large binary cases and
six search-free reused traces. At 65,536 meridians, the complete native inventory
call is about 149 times faster than an explicit chamber reference, including
independent replay; small cases are slower. Reproduce from this directory:

```sh
PYTHONPATH=. python -B -m normal_orbit_research.prismatic_inventory audit --output ../synthesis/data/prismatic-inventory-audit.json
PYTHONPATH=. python -B -m normal_orbit_research.prismatic_inventory benchmark --rounds 5 --output ../synthesis/data/prismatic-inventory-benchmark.json
```

The full coordinate proof, output-size bound and remaining core problem are in
[prismatic_inventory.tex](../synthesis/prismatic_inventory.tex).
