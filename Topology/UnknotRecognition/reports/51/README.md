# Simultaneous Tietze elimination with shared circuits

**Research continuation for ProveIt, 9 October 2026.**

This archive contains the complete article in PDF and LaTeX, an integration
patch and matching overlay, runnable source snapshots, independent certificate
checkers, maintained and new tests, raw experiments, and reproduction tools.
The pinned predecessor is commit
`483b7397a1086206bc463222094315390c42550d` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/483b7397a1086206bc463222094315390c42550d/Topology/UnknotRecognition).

## Research outcome

The principal result is a local exact operation: an acyclic system of raw
singleton Tietze definitions can be eliminated simultaneously with linear
shared-grammar growth, independently of dependency depth and expanded word
length. The proof charges all context extraction using disjoint paths to the
unique pivot occurrences. A topologically ordered witness permits independent
checking with small node summaries.

This removes a specific repeated-rewrite obstacle. It **does not establish a
general quasi-polynomial unknot recognizer**. Finding productive reductions,
controlling the residual presentation, and bounding the complete search remain
research obligations.

| Result | Evidence and limitation |
| --- | --- |
| Exact quotient and size bounds | Full proofs in the article; at most `4M` reachable output nodes, `5M` additional persistent nodes, excluding the empty node. Bit costs and old unreachable storage are accounted for separately. |
| Improved source family | At 256 crossings, checked group-stage paired median ratios of **36.47×** versus default and **9.44×** versus forest. These easy stabilized unknots bypass earlier simplification in this stage experiment. |
| Ordinary workload | No whole-recognizer gain: paired default/singleton **0.954856**, forest/singleton **0.985518**. Lower than one favors the predecessor. The workload is approximately 86% Gordian time. |
| Implementation checks | **1,008 tests passed**, no failures, errors, or skips; 3,698 independently enumerated local cases. |
| Source audit | **81 cases, 75 distinct PD arrays**; 243 exact legacy comparisons; all 54 positives pass both source replayers; no gained or lost positives with the guarded option. |
| Failed policy retained | Eager partial batches lost Gordian within a 20,000,000-work allowance. The delivered terminal guard restores that positive and remains opt-in. |

Read [the article](article/unknot_singleton_dag.pdf) for the mathematics,
counterexamples, experiment protocol, ten research questions, and proposed
next priorities. Its complete source begins at
[unknot_singleton_dag.tex](article/unknot_singleton_dag.tex).

## Quick start

From the extracted archive root:

```sh
python3 scripts/verify_bundle.py
bash scripts/reproduce.sh focused
python3 experiments/replay_saved_certificates.py
make -C article
```

`verify_bundle.py` checks all manifest file hashes, snapshot identities, and
the frozen corpus and harness. The replay command checks all 54 guarded
positive certificates from their recorded original source diagrams using
both source replayers. Its default output is under `reproduced/`.

The patch was checked and applied to a clean copy of the pinned source, and
the resulting files were compared byte-for-byte with the overlay. To apply
it in your own clean checkout, use `git apply --check` followed by `git apply`
with the absolute path to `integration.patch`. No remote repository write is
part of this deliverable.

## Evidence notes

The immutable audit JSON's top-level `seed` is the master constant 261009817.
The actual braid generator in the hashed harness uses 261008504. The timing
seeds are 261009818 for the ordinary workload and 261009819 for stages. All
input PD arrays are retained. This metadata qualification is documented rather
than silently changing the original records.

The raw timing JSON, not rounded tables, is authoritative for numerical
recalculation. Ratios are medians of per-round paired ratios; they need not
equal ratios of displayed median times. All 150 stage and 570 ordinary
measured calls completed, as did all 30 and 114 excluded warmups. Five rounds
and one environment do not support a universal performance claim.

The archive's SHA-256 manifest covers deliverable files; `MANIFEST.json` and
`CHECKSUMS.sha256` are not self-hashed inside that manifest. `CHECKSUMS.sha256`
also includes `MANIFEST.json`. Rebuilding the article or regenerating outputs
can change hashes, so verify the unmodified bundle first.

---

## Contents and integration

| Path | Purpose |
| --- | --- |
| `article/unknot_singleton_dag.tex` and `.pdf` | Complete article; keep its `sections/`, `generated/`, `figures/`, and `references.bib` together. |
| `repo_overlay/Topology/UnknotRecognition/fast/` | Changed and new files for integration, including `SINGLETON_DAG.md`. This directory is an overlay, not a complete standalone package. |
| `snapshots/final/Topology/UnknotRecognition/fast/` | Complete runnable final package, tests, helper modules, examples, and required fixtures. Historical `fast/results/` and Python bytecode caches are omitted. |
| `snapshots/final/Topology/UnknotRecognition/reports/` | The adjacent historical reference modules required by maintained tests: `24/reference`, `26/detshadow`, `28/src`, and `45/code`. |
| `snapshots/baseline/fastunknot/` | Complete frozen Python package at the pinned predecessor. |
| `snapshots/eager/fastunknot/` | Frozen exploratory eager-policy package, retained to reproduce its measured regression. |
| `experiments/` | Experiment drivers, complete raw records, certificates, source hashes, the authoritative test ledger, and byte-preserved corpus. |
| `scripts/reproduce.sh` | Convenience reproduction entry point; the equivalent explicit commands appear below. |

Merge the overlay into the corresponding paths of a checkout at the pinned
commit. If integrating into a later checkout, review conflicts before adopting
the changes. The final snapshot allows immediate testing without modifying an
existing repository. Existing modes retain their defaults. Public opt-in is
`group_decide(..., singleton_dag=True)` or the CLI's `--group-singleton-dag`.
The general algebraic helper accepts partial DAGs; the delivered search policy
uses the terminal guard because eager partial substitution regressed on Gordian.

## Environment

The package declares Python **3.10 or newer** and no mandatory third-party
runtime dependency. The recorded complete run used **Python 3.12.14** on
Linux x86-64 and **Regina 7.4.1**. Regina is needed to reproduce the complete
suite's optional normal-surface cross-checks without skips; the singleton DAG
implementation and the four experiment runs use the standard-library route.

For the same optional engine version, use an appropriate Python environment and:

```sh
python -m pip install "regina==7.4.1"
```

The project metadata also exposes the broader supported optional requirement
`regina>=7.4.1,<8` under the `normal` extra. Installing the project itself is
unnecessary for the source-directory commands below. Timing results depend on
the machine and interpreter; the preserved measurements are evidence, not
predictions of another machine's wall time.

## Run the maintained suite

Start in the extracted archive root. Run the harness from the full `fast/`
directory: several maintained tests spawn `python -m fastunknot` without
overriding their working directory. Merely passing a fast-directory argument
to the harness from another directory does not configure those subprocesses.

```sh
cd snapshots/final/Topology/UnknotRecognition/fast
python -B ../../../../../experiments/run_test_suite.py . --output ../../../../../reproduced/test-suite-ledger.json
cd ../../../../..
```

The recorded authoritative result is `experiments/test-suite-ledger.json`,
with its adjacent `.log`: **1,008 discovered, 1,008 run, successful, zero
failures, errors, or skips**. It records source hashes and interpreter details.
The original completed run took 137.348 seconds in the recorded environment.
The harness writes a new explicit completion ledger, preserves verbose output,
and exits unsuccessfully if tests fail or the executed count differs from the
discovered count. Earlier exploratory logs are not the authoritative final
completion record.

For the focused singleton tests:

```sh
cd snapshots/final/Topology/UnknotRecognition/fast
python -B -m unittest discover -s tests -p 'test_singleton*.py' -v
cd ../../../../..
```

## Reproduce the final experiments

Run these commands from the archive root. They create new output under
`reproduced/`. Each experiment copies complete Python packages into its own
frozen directories, checks source hashes, and uses independent persistent
workers. Existing snapshots must match exactly; use a fresh snapshot directory
when intentionally testing modified code.

The corpus is copied byte-for-byte from the pinned report-46 corpus. Its
SHA-256 is
`ed7ae3116c89a294e0bcf716cf027f4c80b6bcf48523e6a0bb0e4ecb97d7e89b`.
The stages command accepts no corpus, but it is supplied below to reproduce the
preserved record's corpus-hash field as well.

```sh
python -B experiments/singleton_dag_research.py audit \
  --baseline-fast snapshots/baseline \
  --current-fast snapshots/final/Topology/UnknotRecognition/fast \
  --corpus experiments/corpus.json \
  --snapshots reproduced/frozen-guarded \
  --output reproduced/audit-guarded.json

python -B experiments/singleton_dag_research.py stages \
  --baseline-fast snapshots/baseline \
  --current-fast snapshots/final/Topology/UnknotRecognition/fast \
  --corpus experiments/corpus.json \
  --snapshots reproduced/frozen-guarded \
  --sizes 16 32 64 128 256 --rounds 5 \
  --output reproduced/stages-guarded.json

python -B experiments/singleton_dag_research.py benchmark \
  --baseline-fast snapshots/baseline \
  --current-fast snapshots/final/Topology/UnknotRecognition/fast \
  --corpus experiments/corpus.json \
  --snapshots reproduced/frozen-guarded \
  --rounds 5 \
  --output reproduced/benchmark-guarded.json
```

The audit contains **81 cases representing 75 distinct PD arrays**, including
243 exact comparisons of legacy modes. The recorded stages experiment has
150 measured calls plus 30 warm-ups; the ordinary whole-recognition experiment
has 570 measured calls plus 114 warm-ups. Both experiments retain all six
shuffled arms, A/A controls, certificates, sample orders, and incomplete
outcomes. Group-stage timing and whole-recognizer timing have different
boundaries and must be reported separately.

To reproduce the exploratory eager-policy audit with its own frozen source:

```sh
python -B experiments/singleton_dag_research.py audit \
  --baseline-fast snapshots/baseline \
  --current-fast snapshots/eager \
  --corpus experiments/corpus.json \
  --snapshots reproduced/frozen-eager \
  --output reproduced/audit-eager.json
```

The snapshot at `snapshots/eager` is the one matching the source hashes in
`experiments/audit-eager.json`; it must not be replaced by the guarded final
package when reproducing that result.

## Derived tables and PDF

`summarize_singleton_dag.py` reads the four named raw JSON files from its own
directory and writes derived CSV, Markdown, JSON, and LaTeX tables. To summarize
new runs without overwriting preserved derived records, copy that one script
into `reproduced/` after all four commands above, then run:

```sh
python -c "import shutil; shutil.copy2('experiments/summarize_singleton_dag.py', 'reproduced/summarize_singleton_dag.py')"
python -B reproduced/summarize_singleton_dag.py --article-generated reproduced/article-generated
```

The delivered article already contains its generated tables and figures, so
compiling it does not require running the experiments. With a LaTeX distribution
providing the packages in its preamble, compile from `article/`:

```sh
cd article
pdflatex -interaction=nonstopmode -halt-on-error unknot_singleton_dag.tex
bibtex unknot_singleton_dag
pdflatex -interaction=nonstopmode -halt-on-error unknot_singleton_dag.tex
pdflatex -interaction=nonstopmode -halt-on-error unknot_singleton_dag.tex
cd ..
```

## Fixture completeness and scope

The full test snapshot must retain all `fast/` files other than `results/`
and bytecode caches. In particular, keep `examples/`, `certificates/`,
`normal_research/`, `normal_orbit_research/data/projective_plane_torus.json`,
`two_meridian_research/corpus.json`, the frozen
`two_meridian_research/baseline_two_meridian.py`, `tests/fixtures/`, and the
helper Python modules and research packages imported by tests. No maintained
test or its exercised reference helper needs a file from `fast/results/`.

The adjacent report directories listed above are sufficient historical
references for this maintained suite. Some other old benchmark scripts retained
in the complete fast tree refer to additional historical reports or results;
the reproduction commands here concern the maintained tests and this package's
specified experiment drivers.

## Final extracted-layout verification

The complete suite was also run from the packaged final snapshot after
omitting unrelated historical results: all 1,008 tests passed again with
zero failures, errors, or skips. See `experiments/package-test-suite-ledger.json`
and its log. All 54 saved guarded positives passed both source replayers
from this same snapshot; the separate record is
`experiments/saved-certificate-replay.json`.
