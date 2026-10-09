# Weighted Component Extraction and Persistent Elimination

Research continuation for Vladimir Reshetnikov's **ProveIt** unknot-recognition project, 9 October 2026.

Read **`article/unknot_research.pdf`** for the complete article. This archive includes the TeX project, proofs, bibliography, figures, source code, tests, experimental drivers, exact inputs, raw samples, and source hashes.

## Result and scope

This work supplies exact polynomial primitives for a compressed geometric/algebraic recognition procedure. It does **not** establish a general quasi-polynomial running-time bound for the ProveIt recognizer.

The geometric additions implement classical weighted Agol–Hass–Thurston orbit counting over the maintained independently checked orbit trace. They provide sparse many-port incidence and the full normal-coordinate vectors of actual connected components, grouped by binary multiplicity. The article proves a sharp increase of at most three weight runs for the full rightmost-range transfer schedule, and the support-sensitive bound `H <= v + 2q` on distinct component vectors (`H <= v + q` for two-sided components). Attribution to the classical literature is explicit; no literature-priority claim is made for the latter deduction.

The algebraic addition is a separate signed persistent-circuit prototype. A whole sequence of `k` raw singleton eliminations has at most

```
S0 + k*(k+1)*(D0+1)/2
   + 2*k*(k-1)*(k+1)*log2(D0+k+2)
```

allocated nonzero vertices, where `S0` is initial circuit size and `D0` initial concatenation depth. Final ordinary-SLP export at most doubles the size. The theorem excludes intervening free reduction, generator introduction, external word construction, and other transformations. The prototype is not yet integrated with the recognizer's donor planner or source-derived certificate replay.

## Baseline and integration

```
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit:     9feb4346b4d050b305f825f0f7257f495960822a
Subtree:    Topology/UnknotRecognition
```

`integration.patch` adds exactly six files under that subtree:

- `fast/fastunknot/weighted_orbits.py`
- `fast/fastunknot/sparse_port_incidence.py`
- `fast/fastunknot/normal_components.py`
- `fast/tests/test_weighted_orbits.py`
- `fast/tests/test_sparse_port_incidence.py`
- `fast/tests/test_normal_components.py`

Patch paths are rooted at the ProveIt repository root. From the pinned checkout:

```bash
git apply --check /path/to/this-package/integration.patch
git apply /path/to/this-package/integration.patch
```

No existing production file, recognition dispatch, or dense-incidence API changes. `code/fast` contains the same additions and unchanged baseline dependencies. Preserve `code/reports` beside `code/fast`: historical tests import its reference fixtures. These fixtures are not in the patch because they already exist in ProveIt.

The article and experiment directories can be placed in a new report directory chosen by the maintainer. Keep the persistent circuit as an experiment until its planner, cache invalidation, source replay, and normalization boundaries are integrated. Existing immutable-word summary caches cannot be used unchanged with mutable generator bindings.

## Directory map

| Path | Contents |
|---|---|
| `article/` | Main TeX, proof/research sections, generated tables, bibliography, figures, PDF, final TeX log |
| `code/fast/` | Maintained source and tests, plus the six additions |
| `code/reports/` | Thirteen unchanged Python fixtures and four original licenses |
| `experiments/` | Persistent prototype/tests, geometry audits, timing drivers, build/reporting scripts, runnable example |
| `results/` | Final samples, inputs, certificates, hashes, logs, and labelled nonfinal records |
| `review/` | Separate AI-assisted mathematical audit notes; not formal proof-assistant verification |
| `integration.patch` | Additive patch against the pinned repository root |
| `SOURCE_MANIFEST.json` | Source origins, sizes, SHA-256 values, baseline comparisons |
| `SHA256SUMS` | Checksums of delivered files, excluding this checksum file itself |

## Verified evidence

The final integrated suite passed **1,044 tests** with Regina enabled, in **134.266 seconds** reported by unittest. All source hashes match before and after. The separate persistent suite has six passing methods, including 600 random traces and more than 1,000 independently checked literal substitutions.

Geometry tests include 15,816 exhaustive small systems, 2,500 signed vector-weight cases, 5,000 literal pushforwards, huge binary endpoints, proof mutations, and resource/cancellation checks. A broader audit agrees exactly with Regina on **1,000 connected-component multisets**. Every audited certificate verifies with orbit and parity search disabled. The stronger two-sided bound applies and passes in 824 cases.

The final primary geometry benchmark has 260 measured complete calls over thirteen cases and four arms: dense, identical dense control, sparse, and sparse plus replay. The batched follow-up has 4,704 measured calls and 672 excluded warm-up calls. All samples are retained, including an approximately 5.8% verified-query slowdown on one small meridian case.

At 128 eliminations the artificial presentation benchmark records eager/persistent median times of 2.853190/0.395421 seconds and 57,418/6,890 vertices. The persistent side also has 128 binding entries. This roughly 7.22-fold ratio concerns the supplied raw-word kernel, not knot diagrams; its freely cancelling padding is documented.

A capacity example extracts two component types from a normal surface with `2**16385 + 1` components, including `2**16384` compressing disks. The trace has 275 events and the serialized certificate has 1,259,441 bytes. Capacity observations are distinct from repeated comparative timings.

## Reproduce checks

Recorded environment: Python 3.12.14, Linux x86-64, Regina runtime 7.4 / Python distribution 7.4.1. The kernels use only the standard library. Regina is required for the independent normal audit and some existing optional tests; TeX and matplotlib are only needed to rebuild the article.

From the package root:

```bash
python experiments/run_checks.py --normal-audit --output-dir results/reproduced
```

This runs the maintained and persistent suites sequentially, captures complete logs, and runs the 1,000-case audit. Omit `--normal-audit` to omit that broader audit. Frozen original results are preserved.

Equivalent individual commands:

```bash
PYTHONPATH=code/fast python -m unittest discover -s code/fast/tests -v
python -m unittest discover -s experiments -p 'test_persistent_elimination.py' -v
python experiments/audit_normal_inventory.py --fast code/fast --cases 1000 --output results/normal_inventory_audit_reproduced.json
python experiments/demo_inventory.py --bits 128
```

The demonstration's exact fixture generator does not require Regina.

## Reproduce measurements

Run timings sequentially, without concurrent test or audit workloads. Completed comparisons and resource-limited observations must remain separate.

```bash
python experiments/benchmark_geometry.py --fast code/fast --output results/geometry_reproduced.json
python experiments/benchmark_geometry_batched.py --fast code/fast --input results/geometry_reproduced.json --output results/geometry_batched_reproduced.json
python experiments/benchmark_persistent_elimination.py --baseline-fast code/fast --sizes 8 16 32 64 128 --rounds 5 --output results/persistent_reproduced.json
```

The batched driver requires production hashes matching its primary JSON. The eager word arm uses unchanged baseline modules. Timed regions include construction and complete calls/eliminations, with verification included only where stated. Correctness comparisons and final diagnostics are outside timing. Exact hexadecimal JSON transport represents very large integers without changing global interpreter settings.

## Build the article

From the article directory:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error unknot_research.tex
```

Or from the package root, using isolated build output and complete log capture:

```bash
python experiments/build_article.py
```

Regenerate figures and tables from the frozen data with:

```bash
python experiments/make_report_assets.py
python experiments/build_article.py
```

The reporting script requires matplotlib and never changes measured JSON. Standard TeX dependencies include Latin Modern, AMS mathematics, geometry, microtype, booktabs, tabularx, xurl, hyperref, cleveref, listings, and fancyhdr. The final build has no unresolved references or overfull boxes.

## Certificate interpretation

`normal_component_inventory` certifies a **supplied** normal vector in a validated finite compact orientable triangulation with one torus boundary. It does not search for a surface, prove correspondence with a knot diagram, or certify knottedness when no disk is present.

The ordinary orbit checker is independent of the scheduler. Weighted production and checking share transport arithmetic; independent literal oracles and Regina comparisons validate it and the normal encoding. This is not a separately implemented second weighted algorithm.

The cycle cap belongs to ordinary orbit search. Weight-run, output-record, and event caps apply during subsequent weighted replay, after the ordinary trace has been generated and checked. They are cooperative work/output controls, not hard process-memory or wall-clock limits. Incomplete results contain no mathematical inventory.

## Retained nonfinal records

- `geometry_benchmark_initial.*`: development measurement pass before minor cancellation-polling corrections. Final tables use `geometry_benchmark.json` and the separately reported batched follow-up.
- `full_suite_initial.log`: initial sparse-checkout setup failure from missing historical reference fixtures.
- `full_suite_interrupted_capture.*`: incomplete live-log capture. Exit zero without a unittest summary was not accepted as a pass.
- `lcs_transition_isolation.*`: successful isolation of five tests at the capture cutoff.
- `full_suite_complete.*`: authoritative final run, captured through a subprocess pipe and published after completion; all 1,044 tests pass.

The new source follows the existing MIT No Attribution license included at the root. Existing third-party notices and fixture licenses are preserved.
