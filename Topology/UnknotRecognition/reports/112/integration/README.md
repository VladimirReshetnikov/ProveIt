# Native integration package

This directory supplies a reviewable patch and a standalone Python runtime for
the research article **Lazy Weight Replay and Native Chamber Graphs for Unknot Recognition**.
The baseline is the public ProveIt repository at commit
`e0b2f802f336fcb51e9ec5f29174cfe28dfb9d39`.

The patch adds a deterministic AVL run rope with lazy vector additions to the
independent weighted orbit certificate verifier, and an independently checked
normal chamber graph construction. It preserves the original flat weighted
replay as a selectable reference. These are specific algorithmic contributions;
the package does not establish a general quasi-polynomial unknot recognizer.

## Contents

| Path | Purpose |
| --- | --- |
| `proveit_lazy_replay_chamber_graphs.patch` | Git-compatible unified patch containing precisely the six changed or new source/test files. |
| `overlay/` | The same six files at their repository-relative paths. |
| `native_snapshot/fastunknot/` | The complete native Python package, including this patch. |
| `native_snapshot/tests/` | The two new test modules and their existing test helper. |
| `native_snapshot/normal_orbit_research/fixtures.py` | Exact fixture generator required by the new chamber tests. |
| `native_snapshot/marked_parallelity_research/corpus.json` | Exact 106-case source corpus required by those tests. |
| `reference/weighted_orbit_verify_baseline.py` | Pristine weighted verifier bytes from the pinned commit, for isolated baseline comparisons. |
| `PROVENANCE.json` | Pin, source origins, old/new source hashes, and a payload manifest. |
| `validation.json` | Recorded clean patch application and standalone import-smoke results. |
| `verify_integration.py` | Payload-hash and dependency checks, optional clean patch application, and optional execution of the 18 new tests. |
| `LICENSE` | Repository MIT No Attribution license. The nested cyclic Garside package license is also retained. |

The six overlay files are:

```text
Topology/UnknotRecognition/fast/fastunknot/weighted_run_rope.py
Topology/UnknotRecognition/fast/fastunknot/weighted_orbit_verify.py
Topology/UnknotRecognition/fast/fastunknot/normal_chamber_graph.py
Topology/UnknotRecognition/fast/fastunknot/normal_chamber_graph_verify.py
Topology/UnknotRecognition/fast/tests/test_weighted_run_rope.py
Topology/UnknotRecognition/fast/tests/test_normal_chamber_graph.py
```

Only `weighted_orbit_verify.py` modifies an existing file. The other five files
are new. The runtime snapshot contains 262 Python files from `fastunknot`, plus
the exact auxiliary dependency closure for the two new test modules. It excludes
unrelated research archives and large generated data. The snapshot and overlay
together occupy approximately 3 MB of source/data payload before filesystem
allocation overhead.

## Review and apply

Set `PACKET` to the absolute path of the extracted article package and
`PROVEIT_REPO` to a local checkout of the pinned repository. Review the patch,
then apply it with:

```sh
cd "$PROVEIT_REPO"
git apply --check "$PACKET/integration/proveit_lazy_replay_chamber_graphs.patch"
git apply "$PACKET/integration/proveit_lazy_replay_chamber_graphs.patch"
```

The patch has already passed `git apply --check` and actual application in a
clean temporary Git repository containing the pristine modified source. Every
resulting file was compared byte for byte against the overlay. That validation
does not alter the research checkout and creates no commit or remote write.

If integrating against a later repository revision, inspect any overlapping
changes before applying. The pristine verifier is provided so that the baseline
does not depend on a mutable branch or on access to GitHub.

## Standalone checks and tests

The two new test modules use Python's standard library and the bundled files.
Regina is not required. `test_normal_surface_orbits.py` is included because the
chamber tests import its exact source-relabeling helper; its separate optional
Regina tests are not part of the following commands.

Check all payload hashes and load the exact dependency closure without running
the test bodies:

```sh
python -B "$PACKET/integration/verify_integration.py"
```

Add `--apply-check` to repeat the clean temporary Git application check. Git is
required only for that option. Add `--new-tests` to execute the two new modules:

```sh
python -B "$PACKET/integration/verify_integration.py" --apply-check --new-tests
```

Equivalently, execute the 18 new tests directly:

```sh
cd "$PACKET/integration/native_snapshot"
python -B -m unittest tests.test_weighted_run_rope tests.test_normal_chamber_graph -v
```

The included package marker files prevent an unrelated installed `tests` or
`normal_orbit_research` package from shadowing these local dependencies. The
verification helper confirms that all imported `fastunknot` modules came from
this snapshot. Its ordinary smoke check only loads the suites, reads the
106-case corpus, and constructs the one-tetrahedron layered fixture; it does not
execute any of the 18 test bodies.

## Reproduce paired benchmarks without a repository clone

The package's `scripts/benchmark_rope.py` can use this runtime directly. The
serialized native source/method cases are stored in `results/native_cases.json`.
For example:

```sh
python "$PACKET/scripts/benchmark_rope.py" \
  --fast "$PACKET/integration/native_snapshot" \
  --baseline-verifier "$PACKET/integration/reference/weighted_orbit_verify_baseline.py" \
  --cases "$PACKET/results/native_cases.json" \
  --rounds 3 --output "$PACKET/reproduced/native_benchmark.json"
```

Add `--synthetic` to select the complete legal AHT block-star trace family
instead of the native cases. For native queries, the benchmark creates separate
temporary runtime copies for baseline and proposed verifier processes, restores
only the pristine verifier in the baseline copy, and compares full
certificate/result outputs. The synthetic experiment alternates the public
lazy checker and retained flat-reference checker within one process, using the
same complete certificate. Neither mode mutates the bundled snapshot or
monkeypatches the verifier in place.

The SHA-256 of the pristine verifier is:

```text
0965e5b920a5645a6579e56050f8e149e77ea22d62485e58690adf6cbe39df95
```

The recorded native measurements distinguish verifier replay from complete
production, replay, and serialization. The native replay aggregate improved,
while the recorded complete-query aggregate was slightly slower. Retain both
observations when evaluating the patch. The synthetic family proves and tests
a specific replay separation; it is not asserted to be a family of geometric
knot-complement inputs. See the article and benchmark reproduction notes for
the exact workload, operation counters, and scope of the asymptotic claims.

## Provenance and licensing

`PROVENANCE.json` records immutable payload hashes and identifies generated
package marker files. Its `files` manifest excludes the manifest itself and
this explanatory documentation; the final package manifest may additionally
cover those files. `validation.json` records the initial packaging checks,
while `verify_integration.py` can repeat them on an extracted copy.

The repository and native package use the included MIT No Attribution license.
The nested `fastunknot/cyclic_garside/LICENSE` preserves that component's
license notice. No external binary dependency is bundled.
