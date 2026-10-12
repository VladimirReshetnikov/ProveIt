# Reproduction and native integration

The native patch targets exactly ProveIt commit
`8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4`:

<https://github.com/VladimirReshetnikov/ProveIt/tree/8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4>

The archive contains proposed code and recorded evidence. It does not contain
the full repository. The finite graph/matrix tools are standalone; the native
modules use the source geometry and certificate machinery in the pinned
repository.

## 1. Verify the archive and replay a finite example

From the extracted package root, run:

```bash
python -B check_package.py
```

Python 3.10 or later suffices. There are no third-party Python dependencies
for this command. It checks the SHA-256 and size of every file listed in
`code_manifest.json`, then independently replays four saved finite proofs,
regenerates the same certificates with both solvers, and rejects four mutated
proofs. The code manifest covers the code, native overlay, patch, reproduction
instructions, and recorded evidence. The final archive manifest also covers
the article and its PDF.

The positive example has two parallel dual edges, with unsigned occurrence
counts one and three. Deleting the second edge leaves a unit pivot. The
negative example has two parallel edges each with count two; both singleton
stopping sets would need to be deleted, which a one-edge spanning tree cannot
do. Its negative status concerns only the supplied graph/matrix problem.

To rerun the finite tests, exhaustive audit, and controlled benchmark:

```bash
cd code/forest_search
python -B -m unittest -v test_dual_forest.py
python -B audit.py
python -B benchmark.py
python -B dual_forest_search.py examples/positive_problem.json --method degree-two > result.json
python -B dual_forest_verify.py examples/positive_problem.json result.json
```

The recorded run has 18 focused tests and 33,995 oracle comparisons. Of the
33,995 instances, 4,554 are feasible and 29,441 infeasible. Every completed
certificate was independently verified. The scripts create a new local
`code/forest_search/results/` directory, leaving the archived observations
under `results/forest_search/` separate. Operation counts and finite answers
are reproducible; timing samples depend on the machine and system load.

## 2. Prepare a checkout and apply the native patch

Set `PACKAGE_DIR` to the absolute path of the extracted archive. Use a
checkout at the stated revision:

```bash
PACKAGE_DIR=/absolute/path/ProveIt_Dual_Forest_Normalization_2026-10-12
git clone https://github.com/VladimirReshetnikov/ProveIt.git ProveIt
cd ProveIt
git checkout 8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4
PROVEIT_DIR="$(pwd)"
git apply --check "$PACKAGE_DIR/integration.patch"
git apply "$PACKAGE_DIR/integration.patch"
```

The patch contains 14 paths: two modified entrypoints, four new runtime
modules, one new test module, and seven research/support files. The complete
resulting versions are also present under `native/` with repository-relative
paths. Use either the patch or those complete files. The patch was checked
against the exact two original file contents at the pinned commit, applied
in a clean temporary directory, and every resulting file was compared byte
for byte with the supplied overlay. The recorded check is
`results/package_validation/patch_check.json`.

No normal-cut discovery policy is changed by these entrypoints. The new
native branch runs where the old code returned `core_has_three_handles`.
The standalone forest-choice solvers are research tools and are not enabled
inside native dispatch by this patch.

## 3. Native tests and source certificate replay

The focused native tests and saved-packet replay need Python 3.10 or later
and only the existing repository code:

```bash
cd "$PROVEIT_DIR/Topology/UnknotRecognition/fast"
python -B -m unittest discover -s tests -p test_source_core_dual.py -v
python -B "$PACKAGE_DIR/code/replay_native_packets.py" "$PROVEIT_DIR"
python -B "$PACKAGE_DIR/check_package.py" --native-repo "$PROVEIT_DIR"
```

The focused module contains ten test methods. It uses the existing
`normal_orbit_research/fixtures.py` and
`marked_parallelity_research/corpus.json`; both are present in the pinned
checkout. It also uses the new pure-Python relative subdivision generator
`source_core_dual_research/fixtures.py`. These focused tests require no
historical report fixtures and no Regina installation.

The packet replay checks all seven saved positive v6 certificates against
their original face pairings and normal coordinate vectors. It also checks
the three negative packets: source parallelity and boundary certificates
are authenticated, an independent geometric tracer reconstructs the finite
matrix and fixed initial forest, and the finite verifier checks the negative
stopping certificate. The negative conclusion is that no dual forest makes
that fixed raw finite boundary kernel completely eliminable. It does not
establish that the cut manifold fails to be a handlebody.

### The full existing repository suite

The integrated checkout also passed the complete existing test command:

```bash
cd "$PROVEIT_DIR/Topology/UnknotRecognition/fast"
python -B -m unittest discover -s tests -v
```

The recorded run completed **1,688 tests in 374.807 seconds**, with no
failures. It also reports 13,846 expanded-sheet topology comparisons and
the existing marked-cover audit counters. These are suite validation counts,
not 1,688 new tests from this delivery. The complete output is
`results/package_validation/native_full_suite.log`.

Use a complete checkout, including the existing `fast/` research fixtures,
`synthesis/data/`, and the following report assets beneath
`Topology/UnknotRecognition/reports/`:

- `24/reference/graded_transfer_v1.py`
- `26/detshadow/*.py`
- `28/src/closure_reset/*.py`
- `45/code/oracle.py`
- `57/results/discovery_corpus.json`
- `79/repro/fast/commitment_research/coherent-obstruction-certificate.json`
- `79/repro/fast/shared_cover_research/results/exhaustion.json`

These assets already belong to the pinned commit and are not redistributed
in this archive. Their individual pinned hashes are recorded in
`results/package_validation/historical_fixtures.json`. The first local
partial checkout omitted these historical directories; they were restored
from the same commit before the successful full-suite run. The focused new
test module and archived packet replay remain independent of those report
assets.

## 4. Native corpus, matrix audit, and obstruction reconstruction

The native corpus audit uses Regina as an independent oracle for the seven
newly completed cuts. The recorded environment used Python 3.12.14 and the
`regina` Python distribution 7.4.1, whose `versionString()` reports `7.4`.
The native runtime itself has no Regina dependency. Install the comparison
dependency in an appropriate Python environment:

```bash
python -m pip install regina==7.4.1
```

Then set an output directory separate from the archived measurements:

```bash
EVIDENCE_DIR=/absolute/path/reproduced_dual_forest_evidence
cd "$PROVEIT_DIR/Topology/UnknotRecognition/fast"
python -B -m source_core_dual_research.audit --output "$EVIDENCE_DIR/native" --timeout 20
python -B -m source_core_dual_research.matrix_audit --output "$EVIDENCE_DIR/matrix_audit.json" --solver-dir "$PACKAGE_DIR/code/forest_search"
python -B -m source_core_dual_research.audit_obstructions --matrix-audit "$EVIDENCE_DIR/matrix_audit.json" --solver-dir "$PACKAGE_DIR/code/forest_search" --output "$EVIDENCE_DIR/obstructions"
python -B -m source_core_dual_research.source_parity_audit --output "$EVIDENCE_DIR/source_parity_audit.json"
```

The baseline audit reads the original entrypoint directly with `git show`
at the pinned commit. Git and that commit object must therefore be available.
It records the SHA-256 of the original entrypoint and of the 106-case corpus.
The preserved baseline count is 85 complete censuses; the new count is 92,
with all 85 earlier complete outputs retained exactly. All 92 completed
certificates replay. The seven new censuses agree with actual Regina cuts
and exact component recognition.

The matrix audit checks all 106 original source matrices and saves the
complete finite problems for the ten cases with three-handles. Source-only
matrices and full finite boundary matrices have separate labels. The latter
include annular attachment rows that cannot be deleted by the dual forest.
The three saved obstructions use only such ineligible rows.

The source parity audit separately checks uncapped occurrence counts and
even dual incidence at every vertex for all 3,239 source columns in the
106-case corpus. It records no violations. Its 74 three-unit-row columns
consist of seven parallel-edge-pair-plus-loop patterns and 67 three-loop
patterns. Three supplementary stellar subdivisions, identified separately
from the corpus, exercise actual triangular dual cycles. The source parity
report was regenerated during package validation and matched the archived
JSON exactly. This audit concerns original source rows, excluding annular
additions.

## 5. Complete supplied-cut performance comparison

Run the paired benchmark with Regina installed:

```bash
cd "$PROVEIT_DIR/Topology/UnknotRecognition/fast"
python -B -m source_core_dual_research.benchmark_mobius --output "$EVIDENCE_DIR/mobius_benchmark" --rounds 5
```

Both arms start from the same four-tetrahedron source and normal coordinate
vector. The native arm includes certificate production and independent
replay; the Regina arm includes input conversion, actual cutting, component
triangulation, and exact handlebody recognition. Each size has a checked
warm-up and five randomly ordered paired rounds with a fixed seed. The
JSON retains every timing component and sample. Small instances can favor
Regina; the saved evidence retains those regressions. This experiment does
not measure complete unknot recognition.

The finite graph benchmark in Section 1 is a separate experiment. It compares
an explicitly specified spanning-tree enumerator with the two finite solvers.
Every positive timed arm includes the same independent finite checker.
Its large polynomial-only cases report hypothetical tree counts as formulas,
not measured enumeration runs.

## 6. Build the article

A LaTeX installation with pdfLaTeX, BibTeX, Latin Modern, AMS packages,
TikZ, and the standard packages named in the preamble suffices:

```bash
cd "$PACKAGE_DIR/article"
pdflatex -interaction=nonstopmode -halt-on-error dual_forest_normalization.tex
bibtex dual_forest_normalization
pdflatex -interaction=nonstopmode -halt-on-error dual_forest_normalization.tex
pdflatex -interaction=nonstopmode -halt-on-error dual_forest_normalization.tex
```

The principal deliverables are `article/dual_forest_normalization.tex` and
`article/dual_forest_normalization.pdf`, with their section files and
bibliography alongside them. Rebuilding may change PDF metadata and file
hashes even when the mathematical text is unchanged.
