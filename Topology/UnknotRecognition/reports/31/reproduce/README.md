# Reproducing the certified primitives package

This package extends the implementation at ProveIt commit
`8a95834940cf77cdab1b39571ffc102ca8b6bede` in
`Topology/UnknotRecognition/fast`. It contains three exact research primitives
and the article explaining their proofs and limitations. These changes do
not establish a quasi-polynomial bound for the complete recognizer.

| Primitive | Integration | Certified result |
|---|---|---|
| Binary tensor Jones evaluation | `jones --backend tensor`; `recognize --jones-backend tensor` | Exact full polynomial. A nonidentity polynomial obstructs unknottedness; identity continues the established recognition fallback. |
| Integral cocycle seed minimization | Standalone `fastunknot.cocycle_seed` APIs | Minimum total normal-disc count among global vertex-potential changes of the supplied cocycle. Geometric conclusions require the article's manifold, coorientation and class hypotheses. |
| Strict-majority cyclic overlap witnesses | `--group-overlap-witness`; explicit Python keywords | A sound shortening relator move whenever the uncapped local query finds one; existing independent group-certificate replay remains decisive. |

The ordinary `matching` Jones filter remains the recognition default. The
tensor CLI selects the valuation-normalized integer implementation; the
low-level `tensor_jones` function retains Laurent arithmetic as its default
and an independent reference implementation. The overlap policy remains
opt-in because its first maximal alignment can have smaller gain than the
historical optimal-overlap choice. Cocycle optimization is not called by
the recognizer and does not perform normal-surface enumeration or hierarchy
search.

## 1. Checkout and prerequisites

Use a checkout containing the package's integrated changes. For controlled
historical comparisons, retain the baseline Git object above: the overlap
benchmark reads its archived module with `git show`. Copying the Python files
to a directory without the Git history is sufficient for ordinary use and
tests, but does not reproduce that historical benchmark.

All Python commands below run from:

```sh
cd /absolute/path/to/ProveIt/Topology/UnknotRecognition/fast
```

Python 3.10 or later is required. The recorded experiments used Python
3.12.14 on Linux x86-64. The base package has no external Python runtime
dependencies:

```sh
python -m pip install -e .
```

Regina is optional for ordinary recognition and for the tensor/overlap
primitives. Install the recorded version to reproduce the independent
normal-surface and finite-exterior checks:

```sh
python -m pip install 'regina==7.4.1'
python -c 'import regina; import importlib.metadata; print(importlib.metadata.version("regina")); print(regina.versionString())'
```

The package distribution version is 7.4.1; `regina.versionString()` reports
`7.4` in the recorded runtime. On a system using a separately installed
dependency directory, put that directory on `PYTHONPATH` for both the test
process and its children. Merely having a wheel or installed files elsewhere
does not enable the Regina tests.

The complete maintained suite also imports earlier reference implementations.
A full ProveIt checkout contains them. If using a sparse checkout, include
at least these paths (the command runs from the repository root):

```sh
git sparse-checkout add Topology/UnknotRecognition/fast Topology/UnknotRecognition/reports/02 Topology/UnknotRecognition/reports/24/reference Topology/UnknotRecognition/reports/26/detshadow Topology/UnknotRecognition/reports/28/src
```

These are required reference files, not optional proof assumptions:

| Path relative to `Topology/UnknotRecognition` | Purpose |
|---|---|
| `reports/02/unknotlab/normal.py` and its package | Validated finite-triangulation and cocycle adapter audits. |
| `reports/24/reference/graded_transfer_v1.py` | Independent historical transfer comparison. |
| `reports/26/detshadow` | Existing shadow, Tait-block and boundary-connectivity tests. |
| `reports/28/src/closure_reset` | Existing closure scanner reference checks. |
| `fast/examples`, `fast/normal_research`, `fast/tests/fixtures` | Maintained diagrams and independently replayable certificates. |

The existing `conway_sum_8.json` fixture is present under `fast/examples`.
If relocating examples, set `FASTUNKNOT_EXAMPLES` to the directory containing
that file; otherwise two older large-sum tests intentionally skip.

## 2. Tests

Run the focused suites independently:

```sh
python -B -m unittest discover -s tests -p test_tensor_jones.py -v
python -B -m unittest discover -s tests -p test_cocycle_seed.py -v
python -B -m unittest discover -s tests -p test_overlap_witness.py -v
python -B -m unittest discover -s tests -p test_certified_primitives_integration.py -v
python -B -m unittest discover -s tests -p test_normal_surface.py -v
```

Then run the maintained suite:

```sh
python -B -m unittest discover -s tests -v
```

The tensor tests use independent cube polynomials and literal smoothing-circle
traversals. The cocycle tests compare exhaustive finite primal and dual
oracles, reject corrupted optimality certificates, and, when Regina and
archive02 are available, inspect genuine finite-manifold surfaces. The
overlap tests enumerate all cyclic starting positions and signs in literal
oracles, forbid expansion on enormous represented words, and independently
replay a completed original-PD Gordian certificate. The integration suite
checks public argument validation, CLI option dependencies, completed exact
polynomials, identity fallback and resource-exhaustion semantics.

The complete module-batch run is recorded in
`validation/full-suite-modules.json`, with unedited per-module output in
`validation/module-logs/`. The final validation accounting, including the
subsequent worker compatibility repair, is recorded in
`validation/final-validation.json`. The runner independently counts the complete
discovered suite, checks that the sum of executed module counts agrees, and
records source hashes at the beginning and end of the run. It changes no
tests or subprocess allowances. To repeat this validation route:

```sh
python -B /absolute/path/to/unknot_certified_primitives_20261008/reproduce/run_test_modules.py --fast . --output results/certified_primitives_validation
```

An earlier single-process discovery attempt terminated with exit code 1
after 14 passing test lines, without a unittest summary or traceback. It is
preserved in `validation/full-suite-incomplete-attempt.log` and its JSON
metadata, and is classified as incomplete rather than as a completed pass
or failure. The exact next existing stress test passed in isolation; the
module-batch run supplies the recorded comprehensive inventory. The cause
of the incomplete process termination was not established.

`validation/integration-tests.log` and its JSON record contain a separate
six-test public-integration run; they must not be described as a
complete-suite result.

The complete 83-module batch executed all 720 tests present at that point,
with 719 passing and one error in the existing
`test_communication_retains_input_across_polls`. That error reproduced in
isolation under the unchanged three-second allowance; both logs are retained.
This exposed a compatibility bug in the earlier worker code: on the recorded
Python 3.12.14 runtime, retrying `Popen.communicate(None, timeout=...)` after a
partial write retains the payload internally but does not register the pipe
for the remaining writes. The repair submits the input exactly once in a
communication thread while the caller continues to check cancellation and
deadlines. Cleanup kills and reaps the child, joins a started thread, and
closes the pipes, including communication and thread-setup error paths.

After the repair, the affected worker module passes all nine tests, including
the unchanged delayed 500 KB input regression and one additional cleanup
regression; the six public-integration tests also pass on a fresh rerun.
Only `fastunknot/normal_surface.py` and `tests/test_normal_surface.py` changed
after the comprehensive batch. Final discovery counts **721 tests**: the
82 unchanged modules supply 712 passing tests, and the rerun affected module
supplies nine. There are no skips. The additional six integration tests are
a repeat and are not counted twice. This is comprehensive coverage assembled
from module runs, not a claim that a final single-process discovery command
completed successfully.

The final raw reruns are `validation/normal-surface-after-fix.log` and
`validation/integration-after-worker-fix.log`. The diagnosis, exact local
standard-library branch, independent review and scope are recorded in
`validation/worker-communication-fix.md` and
`validation/python-communicate-input-branch.txt`.

Avoid running CPU-heavy benchmarks concurrently with the suite. Some older
tests exercise subprocess communication under short time limits. If such a
test fails under load, retain the original log and record a separate isolated
rerun; neither silently omit it nor change the test's allowance to obtain
a pass.

## 3. Tensor polynomial audits and measurements

Run the independent polynomial and turning-number audit:

```sh
python -B audit_tensor_jones.py --output results/tensor_jones_audit_local.json
```

Run the paired complete-polynomial measurements:

```sh
python -B benchmark_tensor_jones.py --rounds 7 --seconds 2 --output results/tensor_jones_local.json
```

The benchmark records its random seed, arm order, all measured samples,
source hashes, resource caps, full polynomial output and censored results.
Every arm starts with a fresh diagram; order preparation is included.
The arms compare faithful Potts evaluation, an A/A repeat, Laurent tensors,
a global integer encoding, valuation-normalized integer tensors, and an
ordinary-order ablation. The ordinary-order ablation does not inherit the
certified separator width bound. Compare only completed equivalent queries;
an exhausted arm has no completed-time denominator.

Example production calls:

```sh
python -B -m fastunknot jones examples/trefoil.json --backend tensor
python -B -m fastunknot recognize examples/trefoil.json --jones-backend tensor
python -B -m fastunknot jones examples/trefoil.json --backend tensor --max-transitions 0
```

The last command deliberately exhausts its local allowance and exits with
code 3. It does not publish a completed polynomial. In the recognition
pipeline, an inconclusive local filter continues the remaining stages under
the global limits. The standalone exact tensor API is
`fastunknot.tensor_jones.tensor_jones`; request `arithmetic="integer"` for
the implementation used by the tensor CLI. A full polynomial equal to one
is not promoted to an unknot certificate.

## 4. Cocycle seed optimization

Run the combinatorial optimizer measurements and independent Regina checks:

```sh
python -B benchmark_cocycle_seed.py --regina --output results/cocycle_seed_local.json
```

For a dependency-free optimization-only run, omit `--regina`:

```sh
python -B benchmark_cocycle_seed.py --output results/cocycle_seed_combinatorial_local.json
```

The product solid-torus cases include binary heights through 4,096 bits.
The Regina-enabled run also truncates the trefoil and figure-eight ideal
exteriors, obtains the archive02 tree-gauge cocycle, and records all finite
face gluings, the cocycle, optimized coordinates, primal/dual certificate,
and independent geometric observations. These are single optimizer
measurements and certificate checks, not paired recognition timings.

Supported APIs include:

```python
from fastunknot.cocycle_seed import (
    minimize_disc_seed,
    check_seed_certificate,
    optimize_face_pairing_cocycle,
    optimize_triangulated_cocycle,
)

# vertices[t] and heights[t] each contain four integers.
certificate = minimize_disc_seed(vertices, heights)
check_seed_certificate(vertices, heights, certificate)
```

`check_seed_certificate` does not run the optimizer. It checks the integral
potential, local normal coordinates, and an equal-valued dual matching.
The face-pairing adapter checks gluing reciprocity, local-height compatibility
and normal matching; it does not validate that an arbitrary quotient is a
three-manifold. The geometric theorem additionally requires a validated
finite compact orientable manifold. Connectedness requires rank-one
cohomology and an integral primitive class. Optimization does not minimize
genus or prove incompressibility. In a one-vertex triangulation this
particular vertex-potential freedom is vacuous.

## 5. Strict-majority overlap measurements

Confirm that the historical object is available, then run the full paired
benchmark:

```sh
git cat-file -e 8a95834940cf77cdab1b39571ffc102ca8b6bede:Topology/UnknotRecognition/fast/fastunknot/compressed_overlap.py
python -B benchmark_overlap_witness.py --rounds 5 --output results/overlap_witness_local.json
```

Its optional scope restrictions are:

```sh
python -B benchmark_overlap_witness.py --rounds 5 --kernels-only --output results/overlap_witness_kernels_local.json
python -B benchmark_overlap_witness.py --rounds 5 --queries-only --output results/overlap_witness_queries_local.json
```

The original recorded run uses seed 3110, one excluded warmup and five
shuffled measured rounds. It contains 225 completed whole-knot queries,
195 local-operation measurements, and 15 real-residual continuations.
Each residual's complete original-PD certificate is then checked with both
independent replay implementations outside the residual timer.

The historical module and its A/A repeat are loaded into the same current
word-arena, search, application and replay harness as the optional helper.
This is a controlled component comparison. The original timings predate
the later public API/CLI plumbing, which has separate integration tests.
No full-knot corpus query reaches the changed compressed partial-overlap
helper, so those corpus times establish no speedup attributable to it.

The modified equal-bigram family and its interior rotation exhibit the local
gain. The shared-tail family is an already-fast control. The gain-tradeoff
family explicitly records a smaller greedy gain under the optional rule.
The large no-majority control exhausts in the preceding whole-donor stage,
before the new helper is invoked; this distinction is visible in the stats.
All `LIMIT` results are incomplete operations, never negative mathematical
answers.

The public CLI enables its required compressed-group and relator options:

```sh
python -B -m fastunknot recognize examples/hard_unknot_8.json --group-overlap-witness --group-seconds 2
```

Python callers specify the dependencies explicitly:

```python
from fastunknot.group_certificate import group_decide

result = group_decide(
    diagram,
    compressed_search=True,
    relator_moves=True,
    overlap_witness=True,
    seconds=None,
    max_work=20_000_000,
)
```

`seconds=None` removes the local wall cap only. Work and node limits remain.
Equivalent options for `recognize` are `use_group=True`,
`group_compressed_search=True`, `group_relators=True`, and
`group_overlap_witness=True`. The standalone producer is
`compressed_certificate(..., relator_moves=True, overlap_witness=True)`.
The low-level local query remains
`cyclic_overlap_move(arena, roots, witness_first=True)`.

## 6. Replay the supplied Gordian certificate

From `fast/`, pass the extracted package's certificate path as the one
argument in this command:

```sh
python -B - /absolute/path/to/unknot_certified_primitives_20261008/certificates/gordian_witness_certificate.json <<'PY'
import json
from pathlib import Path
import sys

from fastunknot import Diagram
from fastunknot.group_certificate import verify_group_certificate

record = json.loads(Path(sys.argv[1]).read_text())
diagram = Diagram.from_pd(record['pd'])
for compressed in (False, True):
    valid = verify_group_certificate(
        diagram, record['certificate'],
        compressed=compressed, max_work=20_000_000,
    )
    assert valid
    print('compressed' if compressed else 'literal', 'VERIFIED')
PY
```

This reconstructs the presentation from the original PD and replays all
142 moves. It does not trust the producer's residual state. The first 132
moves come from the archived reachable Gordian trace; the optional helper
selects a valid overlap in the ten-generator residual and ordinary search
completes the certificate. This is different from forcing the compressed
partial-overlap route from the beginning of Gordian, an experiment which
exhausted its 20-million-work allowance.

## 7. Interpreting the artifacts

`results/overlap_witness_20261008.json` contains all primary overlap samples,
caps, status, work counts, nodes and complete residual certificates.
`provenance/overlap_witness_findings.md` gives the local theorems, exact hard
family, unbounded gain-ratio counterexample and measurement interpretation.
`provenance/cocycle_independent_review.md` records an independent review of
the cocycle closure, connectedness and bit-complexity proofs.

The article and source-level proofs distinguish three separate matters:
polynomial or subexponential cost of a local primitive, the cost actually
measured on supplied cases, and a complexity bound for complete unknot
recognition. The package advances the first two. Bounds on hierarchy state,
reset counts, general search completeness and grammar growth remain needed
for the quasi-polynomial target.

## 8. Build the article

From the extracted package root, run:

```sh
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error unknot_certified_primitives.tex
```

Keep the section inputs and bibliography beside the main source. The
provided PDF is the typeset article; the source is included for independent
rebuilding and repository integration. The Python benchmark commands are
separate from the LaTeX build and need not be rerun to typeset the saved
results.

