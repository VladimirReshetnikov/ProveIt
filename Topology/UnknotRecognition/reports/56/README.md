# Saturating raw Tietze eliminations and indexing certified interval orbits

Research continuation for **ProveIt / Topology / UnknotRecognition**.

Baseline commit: `fdeb5b1a20b84b93cb150e0232031837bb7d30cb`.

The complete article is [article/compiled_certificates.pdf](article/compiled_certificates.pdf).
Its main LaTeX source is [article/compiled_certificates.tex](article/compiled_certificates.tex);
all included sections, numerical tables, and figures are present.

## Mathematical results

1. **Complete raw singleton saturation.** For a frozen presentation and a
   prescribed survivor alphabet, existence of any successful raw singleton
   Tietze elimination epoch is equivalent to original-source Horn closure.
   A completed epoch can be flattened using the same donor slots, after
   rematching donors to generators. The induced free-group homomorphism is
   preserved; unreduced word spellings need not be. The proof uses a positive
   occurrence-matrix pivot lemma and a unique perfect matching.

2. **Polynomial replacement of a raw epoch.** After exact source metadata,
   fixed-seed closure takes O(r+m+I) structural operations and exhaustive
   rank-one discovery O(r(r+m+I)). A successful epoch compiles into
   O(M+qH+q) grammar nodes from its frozen source. Word-bit costs, source-slot
   handles, and historical arena storage are charged separately. Intervening
   normalization is outside the theorem.

3. **Canonical queries from an orbit certificate.** A complete independently
   verified interval-orbit trace compiles into a reusable map returning the
   minimum original point of every component. Minimum keys agree across
   different valid traces of the same source relation.

4. **A compact set of all component minima.** With g static-gap records, the
   entire set of minimum representatives is a union of at most g ordinary
   intervals. The bound is sharp. Canonical minimum ranking and selection
   take O(B log(g+2)) bit operations after preparation.

These results improve defined local operations. **They do not establish a
general quasi-polynomial unknot recognizer.** The article gives counterexamples,
trust boundaries, a conditional global complexity contract, and ten concrete
research questions about normalization, discovery, representations, marked
attachments, hierarchy frontiers, weighted queries, and formal verification.

## Implementation and observed results

The new runtime modules are `fastunknot/raw_saturation.py` and
`fastunknot/orbit_index.py`. Four existing files receive the optional group
hook. The group producer emits the existing version-eight certificate format;
the independent verifier implementation is unchanged. The default recognition
policy is unchanged. Enable the new group producer with
`raw_saturation=True` in `group_decide`, or with `use_group=True` and
`group_raw_saturation=True` in `recognize`.

The final suite passes **1,114 tests**, compared with **1,090 baseline tests**.
An independent theorem audit checks **85,303 matrices** and **1,896 completed
signed raw epochs**. The actual-diagram source audit includes **102 diagrams**,
old/new verifier cross-replay, and source-binding mutations. The orbit audit
includes **315,554 literal minimum comparisons** and additional membership,
rank/select, huge-coordinate, and mutation tests.

Selected final measurements:

| Workload | Baseline | New | Median paired ratio |
|---|---:|---:|---:|
| Complete group stage, elementary 255-crossing unknot | 1,036.076 ms | 22.204 ms | 46.720 |
| Complete orbit workload, 8 tetrahedra, 32 queries | 46.957 ms | 2.996 ms | 15.629 |
| Complete orbit workload, 24 tetrahedra, 32 queries | 422.509 ms | 20.539 ms | 20.686 |
| Prepared selection, 512 queries / 512 minimum intervals | 29.732 ms | 0.365 ms | 81.511 |

The first row includes source reconstruction and independent replay. The orbit
membership rows include trace discovery, verification, preparation, and all
queries, but begin from supplied interval systems. The final row excludes
preparation; preparation for that case took a separately observed 557.962 ms.
Ratios are medians of paired ratios, not quotients of the displayed medians.

The complete recognizer corpus shows **no broad speedup**. Earlier filters
often settle an input before these operations matter, and some cases regress.
The article and raw data retain those results, connected-orbit controls,
failed-probe overhead, and all resource-limited outcomes. No elapsed ratio is
reported against an unfinished search.

## Integration

`integration.patch` adds the runtime modules, option plumbing, tests, and
research drivers against the pinned repository paths. From a clean checkout
of that commit:

```bash
git apply --check /path/to/integration.patch
git apply /path/to/integration.patch
cd Topology/UnknotRecognition/fast
python3 -B -m unittest discover -s tests -q
```

The patch was checked, applied in an isolated pinned source tree, and compared
byte-for-byte with the delivered files. The evidence is in
`provenance/patch_verification.json`. It changes 20 files in total, including
additions. The existing checker/kernel comparisons are recorded separately.

Copy the standalone `article/` directory and the desired `fast/results/`
evidence into the repository's chosen research location. No report number is
assumed. The bulky results, full baseline snapshot, and initial-candidate
snapshot are supplied in this archive rather than embedded in the patch.
If applying to a newer upstream revision, reconcile the patch against that
revision and rerun the relevant checks.

## Reproduce

The runtime requires Python 3.10 or later. The recorded environment is Python
3.12.14 with Regina 7.4.1. The new tests are pure Python; optional historical
normal-surface tests need Regina. Matplotlib is required only to regenerate
figures. TeX Live with common LaTeX packages builds the article.

From this archive's root:

```bash
cd fast
python3 -B -m unittest discover -s tests -q
python3 -B raw_saturation_research/audit_epoch.py
python3 -B raw_saturation_research/benchmark.py --mode audit \
  --candidate-label final-preindex-guard \
  --output results/raw_saturation_audit.json
python3 -B raw_saturation_research/benchmark.py --mode kernels \
  --candidate-label final-preindex-guard \
  --output results/raw_saturation_kernels.json
python3 -B raw_saturation_research/benchmark.py --mode stage \
  --candidate-label final-preindex-guard \
  --output results/raw_saturation_stage.json
python3 -B raw_saturation_research/benchmark.py --mode pipeline \
  --candidate-label final-preindex-guard \
  --output results/raw_saturation_pipeline.json
python3 -B raw_saturation_research/summarize.py
python3 -B orbit_index_research/audit.py
python3 -B orbit_index_research/benchmark.py --rounds 7
python3 -B orbit_index_research/rank_select.py --rounds 7
```

The default paired baseline is `../baseline/fast`. Run the baseline suite
from `baseline/fast` if desired; its external reference modules are also
included. Preserve the delivered results before rerunning these commands,
which overwrite their correspondingly named output files. Avoid concurrent
CPU-heavy work when collecting fresh timing data.

From the archive's root, rebuild numerical tables, figures, and article:

```bash
cd article
python3 generate_artifacts.py --results ../fast/results
latexmk -pdf -interaction=nonstopmode -halt-on-error compiled_certificates.tex
```

The raw benchmark uses one excluded warmup and five measured rounds. The orbit
benchmarks use one excluded warmup and seven measured rounds. Full call order,
all outcomes, exact inputs, source hashes, and timing boundaries are retained.

## Evidence inventory

- `fast/results/raw_epoch_audit.json`: independent matrix and signed-word audit.
- `fast/results/raw_saturation_{audit,kernels,stage,pipeline}.*`: final group
  measurements, logs, and per-arm journals.
- `fast/results/raw_saturation_initial_*`: initial candidate results, kept
  separately to explain the pre-index guard optimization.
- `fast/results/raw_saturation_kernels_oversized_pilot.*`: an explicitly
  investigator-aborted 100-million-work pilot. Its partial measurements are
  excluded from headline results.
- `fast/raw_saturation_research/initial_candidate/`: frozen initial source,
  drivers, and fixtures for reproducing the earlier candidate.
- `fast/results/orbit_index*.json` and `orbit_rank_select.json`: complete orbit
  audit, membership, and prepared-query evidence.
- `provenance/`: exact source manifest, environment, original and final suite
  logs, patch verification, and SHA256 manifest of packaged files.

The original retrieval manifest also lists synthesis sources read during the
research; those sources are not all repeated here. The archive-content manifest
lists the files actually delivered. Existing source licenses are preserved.
