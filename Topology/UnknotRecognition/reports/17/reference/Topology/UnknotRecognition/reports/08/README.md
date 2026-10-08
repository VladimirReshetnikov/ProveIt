# Toward Quasi-Polynomial Unknot Recognition

Research continuation for Vladimir Reshetnikov's **ProveIt** project, 7 October 2026.

## Outcome and proof status

This bundle contains a comprehensive mathematical article and an executable
performance extension to `Topology/UnknotRecognition/fast`, version **0.3.0**.
It is prepared for review and integration; no remote repository changes have
been made.

The main implemented result is a **complete decision algorithm for the knot
closure of an explicit braid on at most three strands**. Its default
three-strand backend uses `O(ell)` symbol operations and `O(ell)` tokens for a
word of length `ell`; a conservative bit bound is `O(ell log(ell+2))`.
An independent integral-matrix backend provides a second exact decision and
arithmetic witness. A writhe obstruction works for any strand count, and
replayable singleton endpoint destabilizations extend the useful input class.

The article also proves that exhaustive categorical unit cancellation leaves
canonical matching multiplicities at every fixed scan prefix. The included
residue diagnostic checks those multiplicities on the actual scanner engines.
A finite homological perturbation formula specifies a possible batch
cancellation algorithm for disk frontiers, with an explicit cost bound; that
batch algorithm is **not implemented as a production feature in this bundle**.

**The delivered general recognizer still has an exponential worst-case
fallback. This work does not prove or implement a general
`n^{O(log n)}` unknot recognizer.** The article distinguishes established
classification theorems, proved specializations, measured improvements,
conditional complexity results, and open implementation obligations. The
proofs are conventional mathematical proofs; no Lean formalization is claimed.

## Contents

| Path | Purpose |
|---|---|
| `Topology/UnknotRecognition/research/2026-10-07-braids-and-multiplicity/unknot_recognition_progress.pdf` | Complete compiled article |
| Same directory, `unknot_recognition_progress.tex` | Self-contained LaTeX source with bibliography and embedded tables |
| Same directory, `build.sh` | Three-pass PDF build |
| Same directory, `summarize_results.py` | Regenerates measured tables and CSV summaries from the recorded JSON |
| Same directory, `paired_timings.csv` | All 28 pipeline comparisons, intervals, A/A controls, and methods |
| Same directory, `raw_word_scaling.csv` | Direct-word timing and operation-count summaries |
| Same directory, `residue_profile_summary.csv` | All 24 diagram/configuration profile summaries |
| Same directory, `measured_results.tex` | Generated table fragment already embedded in the main article |
| `Topology/UnknotRecognition/fast/` | Complete updated Python source snapshot, tests, examples, and experiment scripts |
| `Topology/UnknotRecognition/fast/results/` | Three original JSON records: paired timings, residue profiles, and verification |
| `baseline/fast/` | Exact pinned baseline source, tests, examples, and scripts used for comparisons |
| `code_changes.patch` | Source, test, script, documentation, and metadata changes against the pinned baseline |
| `PROVENANCE.json` | Repository revision, tree IDs, baseline Git blob hashes, and changed-file list |
| `RELEASE_CHECKS.json` | Patch application, byte comparison, and final integration verification |
| `SHA256SUMS`, `verify_bundle.py` | Integrity manifest and verifier |
| `LICENSE` | Upstream MIT No Attribution license |

The baseline snapshot deliberately omits old generated benchmark results.
It contains all 40 baseline files needed by this comparison and the original
test suite. Third-party papers and lecture slides are cited, not redistributed.

## Baseline and integration

The exact baseline is:

```text
repository: VladimirReshetnikov/ProveIt
commit:     4e6fe879e5238ec0b134b6d33fdca0b8c7c1c711
fast tree:  b99a666269f660d932fc82ac8d1f29d3ae42231f
```

From a checkout matching that baseline, apply the patch after reviewing it:

```sh
git apply --check /absolute/path/to/unknot_recognition_progress/code_changes.patch
git apply /absolute/path/to/unknot_recognition_progress/code_changes.patch
```

The patch changes eight existing files and adds eight source, test, or script
files. It contains no deletions. It does not include the article or generated
result records. Copy the dated `research/2026-10-07-braids-and-multiplicity/`
directory and the three new `fast/results/*.json` files into the corresponding
repository directories as part of the integration. The full updated `fast/`
snapshot is included for inspection or use without applying a patch.

If integrating into a later revision, review any intervening changes before
applying the patch. The archived baseline is also sufficient to reproduce the
published comparison without fetching the repository.

From the extracted bundle root, verify integrity with:

```sh
python3 verify_bundle.py
```

## Running the implementation

Python 3.12.14 was used for the supplied measurements. Runtime and tests use
Python's standard library; the package metadata permits Python 3.10 or later.
No package installation is required when running from the included `fast/`
directory.

```sh
cd Topology/UnknotRecognition/fast
python3 -m unittest discover -s tests -v
python3 -m fastunknot recognize examples/torus_3_5.json
python3 -m fastunknot recognize examples/torus_3_5.json --no-braid
```

The new options are `--no-braid`, `--braid-backend matrix`, and
`--no-braid-reduction`, with corresponding Python keyword arguments.
The regular API only dispatches on retained, validated braid provenance;
an arbitrary PD diagram does not acquire a claimed small braid index.
`Diagram.to_json(preserve_braid=True)` explicitly preserves the source word.

For direct word processing without PD conversion:

```python
from fastunknot import braid_certificate

unknot = braid_certificate(3, [1, -2])
assert unknot["status"] == "UNKNOT"

figure_eight = braid_certificate(3, [1, -2, 1, -2])
assert figure_eight["status"] == "KNOTTED"

independent = braid_certificate(3, [1, -2, 1, -2], backend="matrix")
assert independent["status"] == "KNOTTED"
```

On higher-strand inputs the direct preprocessing API may return
`INCONCLUSIVE`. The full recognizer then uses its existing exact fallback.
Resource limits in the full recognizer return `UNKNOWN`, which is not a
decision that a knot is nontrivial.

## Reproducing the experiments

Run these commands from the bundled `Topology/UnknotRecognition/fast/`
directory. Write fresh runs under new filenames to preserve the published data.

```sh
python3 benchmark_braid.py \
  --baseline ../../../baseline/fast \
  --repetitions 15 \
  --raw-repetitions 5 \
  --largest-raw 1024000 \
  --output results/braid_benchmark_rerun.json

python3 benchmark_residue.py --output results/residue_profiles_rerun.json
```

The `--baseline` argument is important: omitting it instead compares the new
implementation against its own `use_braid=False` ablation. When running after
repository integration, use the absolute path of the archived baseline.

The exhaustive comparisons are inside the 59-method unittest suite:

| Verification | Coverage | Observed result |
|---|---:|---|
| Symbolic versus matrix backend | 46,376 one-component three-braid words, lengths 2, 4, 6, 8 | Zero mismatches |
| Backend versus independent dense reduced Khovanov cube | 2,856 such words through length 6 | Zero mismatches |
| Matrix determinant versus exact Alexander polynomial | 120 seeded cases | Zero mismatches |
| Braid relations and conjugation | 200 seeded contexts | Zero mismatches |
| Intrinsic multiplicities | 54 prefixes in four scanner configurations, 216 pre/post checks | All predictions and completed profiles agree |

Additional tests cover certificate tampering, both endpoint choices and signs,
mirrors, serialization of large integral witnesses, provenance, resource limits,
and fallback behavior. Morton's four-braid unknot is intentionally inconclusive
to the singleton shortcut. A 257-strand kink-chain regression checks that cheap
diagram simplifications finish before the more expensive repeated word passes.

The published pipeline timings contain 1,260 completed samples:
28 cases × 15 rounds × 3 arms. Each sample constructs a fresh PD and recognizes
it. Startup, import, and JSON decoding are excluded. The three arms rotate the
baseline, new implementation, and a second baseline call. All 1,260 verdicts
match the expected answers; future incomplete or inconsistent runs suppress
the speed comparison.

The median paired speedup is the median of old/new ratios, not necessarily the
ratio of separate medians. Under the stated order-statistic and local A/A
comparison rule, 21 cases are measured faster, seven support no timing claim,
and none are measured slower. Default-pipeline ranges are 3.97–7.04× for
positive three-braids, 2.39–3.88× for alternating three-braids, and 2.44–5.29×
for scrambled three-braid unknots. The 10.72–51.05× range is a separate
R3-disabled ablation. These observations are workload-specific and do not
prove a worst-case bound.

To regenerate the article's summaries from the published JSON, run from the
dated research directory:

```sh
python3 summarize_results.py \
  --results ../../fast/results \
  --output-dir . \
  --article unknot_recognition_progress.tex
```

The script exports CSV tables and replaces only the marked benchmark-table
region of the main TeX source. It does not rerun timings. That article region
also describes the fixed published protocol and its recorded aggregate
results; changing the experimental corpus requires reviewing that prose.

## Building the article

Run `sh build.sh` from the dated research directory, or provide its full path.
It uses pdfLaTeX with standard TeX Live packages, including AMS mathematics,
Latin Modern, microtype, booktabs, longtable, tabularx, listings, hyperref,
fancyhdr, and needspace. The main TeX file is self-contained: no external
bibliography database or figure files are required. Three passes resolve
the table of contents and references.

The delivered PDF was rendered page by page and checked for layout and
cross-reference problems. Its final build reports no warnings or overfull
or underfull boxes.

## Research priorities

The article develops ten specific research questions: certified recovery of
small-braid presentations from PD inputs; stronger Markov and exchange moves;
structural four-braid decision; multiplicity-aware scan ordering; finite
radical batching; compressed differential operators; correct multi-boundary
state spaces; provable multiplicity profiles; an implementable geometric
hierarchy primitive with encoded-size bounds; and formal verification of the
small algebraic and certificate-checking core.

The immediate practical candidates are certified braid preprocessing and
implementation of the finite batching formula. The main asymptotic tasks are
to control the representation of general differential operators or to complete
the geometric hierarchy's size, depth, and per-operation cost bounds.
