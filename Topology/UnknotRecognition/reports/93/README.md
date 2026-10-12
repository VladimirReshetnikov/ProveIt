# Genus Budgets and Native Boundary Interfaces for Unknot Hierarchies

Research continuation for Vladimir Reshetnikov's ProveIt project, 12 October 2026.

**Read the article:** `hierarchy_primitives.pdf`. The complete LaTeX sources are
in `article/`; compile `article/hierarchy_primitives.tex` from that directory.

This package proves and implements local improvements toward a complete
quasipolynomial unknot-recognition hierarchy. It does **not** prove that the
maintained general recognizer has quasipolynomial complexity. It is an additive
research package: no existing recognizer default has been changed.

## What is new relative to the audited project state

1. An exact genus budget for unused one-handle cocores and a rooted-forest
   attachment reduction. At connected boundary genus `g`, at most `g` specified
   nonball pieces and `g-1` connecting handles remain; the all-ball case becomes
   one ball with `g` handles. The graph certificate does not construct ball charts.
2. A source-bound initial torus compiler: either a solid-torus certificate or
   an inherited admissible core for the empty boundary pattern. Four local
   tetrahedral characteristic graphs prove the required admissibility condition.
   Only the canonical-diagram wrapper authorizes the knot interpretation.
3. Independent replay of geometric cancellations using occurrence counters,
   and an exact `Theta(t^2)` versus `O(t log t)` certificate-size comparison on
   the specified Fibonacci layered family, relative to the maintained explicit
   cocycle-list encoding.
4. Native first returns, exact old-edge lengths and local fibre transport from
   one weighted census. The source ownership bridge and an independently
   verified compact pair codec are implemented; a four-field reference codec
   remains for differential checks.
5. An output-sensitive unmarked reconstruction theorem, conditional global
   complexity accounting, and specific further research problems. These
   theoretical sections do not claim a delivered patterned reconstruction.

## Reproduce the verification

Python 3.12 was used for the recorded run. The algorithms use the standard
library. Regina 7.4 supplies the independent topology controls; install the
listed requirement to reproduce the full no-skip audit.

```bash
python3 verify_manifest.py
python3 -m pip install -r requirements.txt
python3 run_checks.py
python3 examples.py
```

`run_checks.py` inserts `code/` and the bundled `native_snapshot/` into the import
path. It writes `results/validation_summary.json` and returns a nonzero exit
status on failure. This is the delivered research suite, not a claim that all
unrelated upstream recognizer tests were rerun.

The suite covers 48 raw source triangulations and their relabellings, canonical
diagram provenance, reducible counterexamples, all connected labelled simple
graphs on up to five vertices under three root assignments, random multigraphs,
157 native normal-source cases, independent literal checks on 146 cases, and
all 4,140 partitions of eight terminal labels. The native stress cases include
normal multiplicity `2**16384`, which is never expanded into individual discs.
Malformed certificates, exact resource caps, and cooperative interruption are
also exercised. See `results/validation_log.txt` for the final combined run.

## Reproduce measurements and saved certificates

From the package root:

```bash
export PYTHONPATH="$PWD/code:$PWD/native_snapshot"
python3 code/benchmark_unused_handles.py --repeats 5 --output data/unused_handles_benchmark.json --tex-output article/unused_handles_measurements.tex
python3 code/native_moments_benchmark.py --repeats 5
python3 code/attachment_kernel_benchmark.py
python3 code/native_moments_replay.py
python3 code/audit_unused_handle_fibonacci.py --output data/unused_handles_fibonacci_audit.json
python3 code/audit_unused_handles_k4.py
```

The benchmark files contain all samples, medians, scope, source revision and
structural counts. They measure completed source operations with independent
replay, not end-to-end knot recognition. The new source operator and old operator
return different certificates. Timings are instance-dependent, and the article
reports regressions as well as gains. Rerunning benchmarks overwrites the named
result files; preserve a copy first if comparing machines or revisions.

The native benchmark emits both a default pair-codec result and the retained
four-field reference result. Representative native certificates can be replayed
without discovery. Huge integers in JSON use the maintained hexadecimal
transport convention where required by Python's decimal conversion limits.

## Rebuild the article

The complete PDF and figure files are included; Python is not needed to read
them. With a TeX distribution supplying the usual AMS, geometry, hyperref,
booktabs, listings, lmodern and natbib packages:

```bash
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error hierarchy_primitives.tex
```

The optional `python3 code/create_figures.py` uses matplotlib to regenerate
the exact graph drawings and the plot of recorded certificate sizes. It does
not generate new measurements or fit an asymptotic curve.

## Integration and provenance

The audited upstream commit is
`704600626606a9097cfd89d4e3d2bbc63c8dd1cb` at
<https://github.com/VladimirReshetnikov/ProveIt>.
`SOURCE_AUDIT.json` identifies the four inspected incoming archives and relevant
maintained sources by hash. `native_snapshot/SOURCE_MANIFEST.json` inventories
the unmodified Python snapshot used for reproduction. The snapshot is included
for convenience; a repository integration should import the matching maintained
source rather than copy it a second time.

Read `integration/INTEGRATION.md` for proposed placement, status contracts and
the limits of the adapter. `integration/unused_handles.md` and
`code/native_moments_README.md` give the detailed module interfaces.

The mathematical proofs are written proofs, not proof-assistant formalizations.
The independent checkers use separate source reconstruction or traversal paths
as described in the article; they still rely on the pinned parsers and exact
arithmetic. The graph hash binds incidences and Euler labels, not geometric ball
recognition. A generic raw-source certificate never accepts a caller-supplied
irreducibility flag as a knot-recognition authority.

`SHA256SUMS` covers every release file except itself. `verify_manifest.py`
checks those contents; it is an integrity check, not a substitute for source
or mathematical verification. `build_release.py` regenerates that manifest
and the ZIP after intentional updates, excluding build products and Python
caches. The final combined test log and PDF quality record are in `results/`.
