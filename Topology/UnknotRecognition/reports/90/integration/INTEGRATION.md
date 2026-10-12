# Integration into ProveIt

This package is an additive research continuation based on ProveIt commit
`a28a49ee5c4145db0facbeb1e7f65cd8a2816775`. It contains local mathematical
reductions, implementations, and independently replayable evidence. It supplies
neither an automatic replacement for the maintained recognizer nor a proof of
its global running time.

## 1. Preserve an isolated, reproducible entry point

Retain the article and archive under the project's incoming research workflow.
One possible extracted staging location is
`Topology/UnknotRecognition/research/hierarchy_kernels_20261012/`; the directory
name is a proposed integration choice. Run `python verify_all.py` from the
extracted package before moving modules into any maintained namespace.

The default runner creates separate processes for routing, geometry, and
cancellation. This matters because both geometric and cancellation runtimes
use the `fastunknot` namespace and originate in different pinned source
closures. Putting both runtime directories on one `PYTHONPATH` would select
one by import order. A unified integration should reconcile those versions
deliberately and rerun source-certificate checks.

Do not install either reproduction runtime's minimal `__init__.py` shim over
the maintained `fastunknot/__init__.py`. The shims only avoid unrelated public
facade imports in this standalone package. The upstream module files themselves
are copied unchanged. Their hashes and origins are listed in:

- `geometry/evidence/upstream_dependencies.json`: 30 incoming source modules
  and the pinned native corpus;
- `provenance/cancellation_dependencies.json`: 42 maintained/incoming source
  modules and the obstruction-fixture location.

The cancellation overlay's `normal_vertex_gate.py` is the unchanged incoming
rank-and-boundary gate. The new search implementation is
`normal_weight_clusters.py`. Reused machinery should retain its provenance
when promoted or renamed.

## 2. Public entry points and what they certify

| Interface | Input | Accepted result | Meaning of other outcomes |
|---|---|---|---|
| `cluster_defect_search` | Genuine source triangulation and cancellation/support/component budgets | `DISC_FOUND`, coordinates, and a vertex-disc certificate | `NO_VERTEX_DISC_IN_CANCELLATION_CLASS` concerns only that class; `INCONCLUSIVE` is resource exhaustion. Invalid hypotheses raise validation errors. |
| `verify_vertex_disc_certificate` | Source, supplied coordinates, and rank/boundary proof | `True`: the supplied primitive normal surface is an essential disc | `False` rejects that proof. It does not classify the manifold or prove that no disc exists. |
| `normal_cut_unsaturated_handlebodies` | Source triangulation and normal coordinates | `COMPLETE` with exact unmarked handlebody census; certificate when requested | `INCONCLUSIVE` may indicate saturation, an unsupported core proof, or a resource limit. |
| `verify_normal_cut_unsaturated_handlebodies` | Original source, coordinates, and complete native proof | `True`: replays parallelity, boundary, core, and finite reduction proofs | Rejection is a proof-verification outcome, not a non-handlebody verdict. |
| `routed_patterns.core.solve` | Closed cubic chain with aligned through tiles, or supported small literal blocks | `routed-cubic-cut-v1` graph proof | A large unaligned/unsupported block raises `ValueError`; use the through wrapper where applicable. |
| `routed_patterns.stable.solve` | Closed cubic chain with arbitrary through tiles, or supported small literal blocks | `stable-routed-cubic-cut-v1` proof with exact original-source binding | A large tile with a component missing an interface raises `UnsupportedTile`. |

For graph results, `LOW_CYCLIC_CUT` certifies a cut of size at most three
with an edge on each shore and includes a compressed original-source coloring.
`NO_LOW_CYCLIC_CUT` carries independently checkable four-flow certificates for
the required edge-anchor pairs. Both are statements about the supplied cubic
graph. A faithful spherical boundary embedding and a separately certified
ambient ball are additional inputs needed by the geometric essentiality
interpretation.

### Cancellation example

Run this from the package's `cancellation/` directory:

```python
import json
from pathlib import Path
import bootstrap
from fastunknot.normal_weight_clusters import cluster_defect_search
from fastunknot.normal_vertex_gate import verify_vertex_disc_certificate

saved = json.loads(Path("artifacts/disconnected_disc.json").read_text())
source = saved["triangulation"]
result = cluster_defect_search(source, max_defect=2, max_components=2)
if result["status"] == "DISC_FOUND":
    assert verify_vertex_disc_certificate(
        source, result["coordinates"], result["certificate"])
```

`bootstrap.py` defaults to the bundled `runtime/`. For a consciously selected
repository integration, `PROVEIT_UNKNOT_ROOT` may point to
`ProveIt/Topology/UnknotRecognition`, and `CANCELLATION_PACKAGE` may point to
the extracted incoming cancellation archive. These overrides are useful only
after the matching dependencies have been installed. The root validation
runner explicitly selects the bundled runtime for reproducibility.

The search's current source hypotheses include one global vertex, rank-one
integral cohomology, orientability, and the required torus boundary. With more
than one global vertex, a fixed absolute cocycle representative does not give
the same complete search. The new component parameter should not become a
default heuristic cap whose exhaustion is mistaken for a negative knot result.

### Geometric source-certificate example

Run from `geometry/` with `PYTHONPATH=code:vendor`:

```python
import json
from pathlib import Path
from unsaturated_bundles.native import (
    normal_cut_unsaturated_handlebodies,
    verify_normal_cut_unsaturated_handlebodies,
)

saved = json.loads(Path("evidence/pilot_lst_5_7_0_certificate.json").read_text())
source = saved["source"]
result = normal_cut_unsaturated_handlebodies(
    source["triangulation"], source["coordinates"], record_certificate=True)
if result["status"] == "COMPLETE":
    assert verify_normal_cut_unsaturated_handlebodies(
        source["triangulation"], source["coordinates"], result["certificate"])
    print(result["census"])
```

The finite package also exposes `make_certificate(model)` and the independent
`verify_certificate(model, certificate)`. Its integer incidence model is
conditional on the existence of the stated genuine attachments. The native
adapter closes that gap by deriving merged attachment runs and core owners
from replayed source geometry. A spreadsheet with matching Euler counts does
not replace those source proofs.

Unsaturated annular attachments are accepted regardless of annular slope. The
proper-boundary hypothesis is essential. Saturated bases remain outside the
native classifier extension: the theorem leaves a genuine two-handle for each
such base, and neither relator count nor first homology determines its effect.
Huge genus and multiplicity outputs are binary counts. The implementation does
not construct that many bands or transport marked curves through them.

### Routing and through-reblocking example

Run from the package root with `PYTHONPATH=code`:

```python
import json
from pathlib import Path
from routed_patterns.core import parse_chain
from routed_patterns.stable import solve
from routed_patterns.stable_verify import verify_result, verify_source_witness

chain = parse_chain(json.loads(Path("examples/through_4097_bits.json").read_text()))
proof = solve(chain)
assert verify_result(chain, proof)
if proof["verdict"] == "LOW_CYCLIC_CUT":
    original = verify_source_witness(chain, proof)
    print(original["cost"], original["crossings"], original["anchors"])
```

For an aligned chain use `routed_patterns.core.solve` and
`routed_patterns.verify.verify_result`. The aligned source-witness function
takes `proof["source_witness"]`; the through-wrapper source-witness function
takes the **whole wrapper proof**. This deliberate API difference lets the
latter authenticate reblocking metadata and the map back to original blocks.

Original edge addresses are zero-based `{block, copy, edge}` records. `copy`
is a nonnegative hexadecimal string. A main composite-copy address `(v,u,e)`
maps to original copy `m*v+u`; an explicit tail uses offset `m*q+u`. The
checker reconstructs the bounded powers independently and checks the actual
alignment and source mapping. Certificate-supplied replacement tiles are not
trusted.

The general builders `routed_patterns.core.build_kernel` and
`routed_patterns.stable.build_kernel` accept `threshold=k, close=False` for an
open marked-query kernel. `connected_cutoff(k)` returns `1, 3, 4, k+1` in the
four respective regimes `k=0,1,2,≥3`. The closed cubic graph producer and its
certificate schemas remain fixed at threshold three.

## 3. Keep discovery, transition, and terminal checks separate

Integrate the new cluster search as an optional candidate supplier. Its
positive proof should pass the rank/boundary gate before a downstream cut.
Keep the incoming search available: the new bound can be worse when edge
incidence is large or the defect is highly dispersed. A race between searches
must charge both arms' actual work and preserve external cancellation.

Integrate the geometric extension only after the source-parallelity, ordered
boundary, and core proof prerequisites are met. A census sufficient for an
unmarked handlebody query does not provide all boundary charts needed by the
next patterned hierarchy stage.

Integrate graph kernelization after producing a faithful flat tile descriptor.
Every component must meet both interfaces for the large-power theorem, and
later attachments may access only the declared exterior interface vertices.
Neither a large parallelity multiplicity nor a small numerical graph kernel
proves that these descriptor conditions hold geometrically.

For any eventual recognizer dispatch, preserve `INCONCLUSIVE` and unsupported
outcomes as separate states. The article's global branch-budget conditions
also charge failed candidates, cleanup, and restarts. A successful short
hierarchy alone is not an asymptotic analysis of the complete search.

## 4. Verification and optional reproduction

`python verify_all.py` performs the default retained validation, using only
Python's standard library and bundled source modules. It writes
`results/verify_all.json` and per-group logs/results in
`results/verification/`. Counts are taken from actual unittest results and
actual certificate replays. The current inventory is 27 routing, 14 geometry,
and 11 cancellation methods, plus four graph, five geometric, and one
cancellation saved-proof replays. Skips do not count as a full validation pass.

For certificate-only CI:

```bash
python verify_all.py --only replays --output results/replay_only.json
```

The four graph certificates can also be checked through the CLI, for example:

```bash
PYTHONPATH=code python -m routed_patterns examples/through_4097_bits.json \
  --verify examples/through_4097_bits_certificate.json
```

For other individual examples, replace both filenames. The CLI automatically
selects the wrapper checker from the certificate schema. Add `--through` when
generating a new certificate for an arbitrary through tile.

The following optional experiments intentionally regenerate their named result
files. Preserve retained measurements or use a separate extracted copy when
comparing environments. Run timing jobs without competing compute-heavy tasks.

| Experiment | Command and working directory | Extra dependency |
|---|---|---|
| Full routed signature audit and example generation | Root: `python experiments/routing_audit.py` | None |
| Independent routing/source-address audit | Root: `python experiments/independent_routing_audit.py` | None |
| Through partition audit | Root: `python experiments/reblocking_partition_audit.py --max-width 5 --output results/reblocking_partition_audit.json` | None |
| Exact connected-cutoff audit | Root: `python experiments/connected_cutoff_audit.py` | None |
| Complete graph-query timings | Root: `python experiments/routing_benchmark.py` | None |
| Native geometric coverage/oracle audit | `geometry/`: `PYTHONPATH=code:vendor python tools/native_audit.py --corpus vendor/marked_parallelity_research/corpus.json --output evidence/repeated_native_audit.json` | Regina |
| Paired native geometry timings | `geometry/`: `PYTHONPATH=code:vendor python tools/benchmark.py --corpus vendor/marked_parallelity_research/corpus.json --output evidence/repeated_benchmark.json --rounds 5` | Regina |
| Disconnected fixture reconstruction | `cancellation/`: `python audit_disconnected.py` | None |
| Full external standard-vertex census | `cancellation/`: `python audit_disconnected.py --full-census` | Regina |
| Cancellation benchmarks | `cancellation/`: `python benchmark_clusters.py` | None |
| Article figures and routing table from retained measurements | Root: `python experiments/make_report_figures.py` | Matplotlib |

The retained optional oracle used Regina 7.4. Full cancellation benchmarks
include complete all-support enumeration through 40 tetrahedra and are much
longer than certificate replay. External census agreement is finite evidence;
its negative/completeness assertion is not a new independently verified
negative certificate.

The optional Python dependencies are listed in `requirements-audit.txt`.
For the main PDF, use a TeX installation providing the packages declared in
`article/hierarchy_kernels.tex`. The bibliography is supplied as TeX source;
there is no separate bibliography database to download. With `latexmk`:

```bash
sh article/build.sh
```

Matplotlib is needed only for regenerating plotted figure assets. The article
PDF, TeX source, raw measurements, fixture sources, proof files, and dependency
provenance should travel together in the repository's research archive.
