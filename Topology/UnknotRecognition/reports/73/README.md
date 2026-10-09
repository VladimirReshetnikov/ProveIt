# Active Normal Faces and Batched Geometric Descent

Research continuation for Vladimir Reshetnikov's ProveIt project, 9 October 2026.

**Start with `article/article.pdf`.** The complete modular LaTeX source is beside it. This package provides proved local algorithmic results, executable additive implementations, exact certificates, reproducible measurements, and a research agenda. It does not claim that the complete recognizer now has a general quasi-polynomial complexity bound.

## Principal results

1. **Exact optimal sub-batches by matching.** Within any fixed tetrahedron-disjoint family of legal coherent 3–2 moves, the best vertex-link-peeled Euler score reduces to maximum-weight matching. An optimum with the fewest omissions omits at most one move per relevant interior vertex.
2. **A linear selector for the maintained source.** The canonical pulling diagram exterior has two interior poles. Its positive reward graph therefore has a vertex cover of size at most two, and the matching stage needs only a linear graph scan. After greedy packing from M candidates, an optimal nondecreasing sub-batch retains at least `max(0, ceil(M/10) - 2)` moves. The packing and complete geometry preparation have their own costs.
3. **Commuting geometry and compact replay.** Disjoint formal bipyramids commute even when they share global boundary vertices or paired facets. One simultaneous certificate removes repeated full intermediate states. The conflict graph has maximum degree nine.
4. **Maintained exact peeling scores.** Deterministic AVL trees retain all corner records and cache thirteen-key prefixes. Singleton hypothetical edits take a constant number of integer operations after local data are known; committed edits replenish the prefixes in logarithmic tree work. Collective scores are checked against full endpoint geometry.
5. **Complete active-support certificates.** A rational primal–dual pair proves both every active coordinate and every forced zero of a nonnegative matching cone. An adaptive incompatibility search has at most `2^(rho+1)-1` nodes.
6. **A genuine obstruction.** Unrestricted anchored normal cones satisfy `rho >= t - v`, and the maintained n-crossing pulling source satisfies `rho >= 16*max(1,n)-2`. Active support alone cannot make this unrestricted-root parameter polylogarithmic.

The article proves these statements, separates inherited theorems from this continuation, gives a 32-tetrahedron geometric counterexample to additive peeled scores, and lists fourteen concrete research questions.

## Measured results and their scope

On the same fixed 64-move sets, four paired workloads give checked-producer speedups of 117–123 times and literal witness size reductions of about 59–60 times. A fresh index plus complete candidate scoring is 160 times faster on the largest layered workload and 210 times faster on the largest source-unknot workload than full individual replay for every candidate. These comparisons do not measure complete recognition or compare different search policies.

The enlarged support LP is an adverse result: across 17 positive paired cases it reduces 130 unary calls to 17 lifted calls but increases total time from 1.4183 seconds to 22.8305 seconds. It has no timing win in that audit. It remains an optional certificate/research interface.

## Pinned baseline and integration

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

Commit: `66098968e88bba797143ac1bf7ad0ac4c5f697df`

The files used from the maintained `fast/` tree were checked against that revision's Git blob hashes. The incoming prerequisite archives were independently byte-verified against their recorded Git blobs. `manifest.json` records the lineage and hashes; `integration/file_lineage.json` distinguishes new modules from unchanged incoming dependencies.

`integration/additive.patch` is intended to be applied **from the repository root** at that baseline:

```sh
git apply --check /path/to/package/integration/additive.patch
git apply /path/to/package/integration/additive.patch
```

The patch adds files under `Topology/UnknotRecognition/fast/`; it changes no existing maintained file. It includes the few unchanged prerequisites absent from that baseline:

- `exact_lp.py`, from the incoming dual-certificate package;
- `cocycle_transport.py` and `cocycle_transport_verify.py`, from the incoming geometric-transport package.

If those names have been integrated in a newer revision, reconcile their versions before applying the patch. The complete supporting tree in `code/fast/` is for reproduction; the additive patch is the integration deliverable. Historical helper files and two fixtures required by maintained tests are included in sibling `code/reports/` and `code/synthesis/data/` directories.

No production recognizer policy is enabled by default. The research interfaces operate on supplied geometry and cocycles, or on explicitly reconstructed normal matching queries.

## Reproduce correctness

Python 3.12 is the recorded runtime. Most paths require only the standard library and the included project modules. NetworkX 3.7 is optional for general matching; it is unnecessary for the two-pole source path. Regina is unnecessary for ordinary replay. Existing project dependencies and licenses are preserved in `code/fast/`.

From `code/fast/`:

```sh
python -S active_research/replay.py
python -S batched_descent_research/replay_evidence.py
python -m unittest discover -s tests -v
```

The active replay checks 37 support certificates and seven complete normal-search certificates without solving an LP. The geometric replay checks 24 batch proofs, 500 sequential transports, their source bindings, exact witness sizes, and the strict interaction example. Its runtime guard rejects calls into the move, transport, fixture, dynamic, and matching producers.

To run the new interface tests alone:

```sh
python -m unittest \
  tests.test_normal_active \
  tests.test_pachner_batch \
  tests.test_corner_minima \
  tests.test_cocycle_peeling \
  tests.test_peeled_batch_selection \
  tests.test_batched_descent_driver -v
```

With `python -S`, the five optional general-NetworkX tests are skipped explicitly, while the source-specific small-cover tests still run. Retained validation logs give the exact tested counts and versions.

The portable geometric counterexample can be reconstructed from package root:

```sh
python -S evidence/counterexample/peeling_geometric_counterexample.py \
  --output counterexample_rebuilt.json
```

Its three peeled gains must be `[1, 1, 0]`. The optional `--regenerate-torus-with-regina` flag independently rebuilds the original 24-tetrahedron seed; the saved seed avoids this dependency for normal use.

## Use the geometric interfaces

From `code/fast/`, with a supplied valid triangulation and coherent integer heights:

```python
from fastunknot.cocycle_peeling import CocyclePeelingState
from fastunknot.pachner_batch import select_disjoint_collapses

state = CocyclePeelingState(triangulation, heights)
census = state.score_candidates()
packed = select_disjoint_collapses(census['candidates'])
family = [census['candidates'][i] for i in packed['selected_indices']]
choice = state.optimal_subbatch(family)
if choice['sites']:
    checked_result = state.apply_batch(choice['sites'])
```

Candidate objects belong to one current state. Do not reuse them after a commit or edit their local charts. `apply_batch` independently validates the actual move before changing the cache. A callback interruption during cache mutation invalidates the object; reconstruct it before reuse.

The research `batched_descent_research/descend.py` driver repeatedly applies this policy to a supplied state, with explicit round and work limits and a replayable chain. Use its `--help` for the actual JSON interface. It returns geometric diagnostics, not a knot verdict. Its optional final essential-disc query uses the maintained component certificate and keeps that claim tied to the supplied final vector.

A retained driver example starts from the source-unknot workload with 28 tetrahedra, performs batches of 8, 2, and 2 collapses, and stops at 16 tetrahedra with an empty legal census. All three peeled Euler gains are zero, and the independent final component certificate counts one essential disc. This is a demonstration on that supplied meridian fibre, not a claim of complete witness search. Its source, trajectory, and replay summary are in `evidence/validation/descent_*.json`.

From package root, reproduce it with:

```sh
python -S code/fast/batched_descent_research/descend.py \
  evidence/validation/descent_input.json --max-rounds 20 --disk-count \
  --output descent_rerun.json
python -S code/fast/batched_descent_research/descend.py \
  evidence/validation/descent_input.json --replay descent_rerun.json
```

The general matching routine is:

```python
from fastunknot.peeled_batch_selection import solve_two_endpoint_rewards

result = solve_two_endpoint_rewards(
    [{'cost': 2, 'rewards': [[0, 2], [4, 1]]}],
    cover_vertices=[0, 1],
)
```

The supplied cover is checked against every positive reduced edge. Omitting `cover_vertices` selects the optional general matching backend. The geometric wrapper computes the cover from actual interior vertex links. Attained value, algorithmic optimality, and independent topological validity are distinct checks; see the article's certificate discussion.

## Reproduce measurements

From `code/fast/`:

```sh
python -m batched_descent_research.benchmark_batch \
  --repeats 3 --counts 1 4 8 16 32 64 \
  --output batch_rerun.json --evidence-dir batch_rerun_evidence

python -m batched_descent_research.benchmark_peeling \
  --evidence ../../evidence/geometry/benchmark_evidence \
  --rounds 3 --output peeling_rerun.json

python active_research/benchmark.py \
  --seconds 25 --output active_rerun.json
```

Timing ratios depend on the host. Exact source binding, output geometry, coordinates, support activity, objective values, and independent certificate acceptance are the reproducible mathematical checks. Every raw paired geometric timing sample is retained. The active audit has one timing per request and is described accordingly.

## Build and verify the article

From package root, `python tools/generate_figures.py` regenerates the static figure with Matplotlib. Then:

```sh
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Run `python tools/verify_package.py` from any directory to check the delivered byte manifest. `evidence/validation/` contains final test, certificate replay, patch-application, and PDF layout results. The article is a research contribution with explicit assumptions and complete proofs of the stated local results; the final section identifies the open global statements needed for quasi-polynomial recognition.

