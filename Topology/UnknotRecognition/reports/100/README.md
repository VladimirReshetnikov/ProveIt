# Dual Forests and Homological Progress Certificates

Research contribution for ProveIt, 12 October 2026.

**Article:** `article/dual_forests_and_homological_progress.pdf`  
**Source:** `article/dual_forests_and_homological_progress.tex`  
**Integration patch:** `integration/dual_forest.patch`

Baseline revision: `8cb7d9d25ac8cb64a9d147304e3441e98e94c7a4`.

## What this contribution establishes

The native implementation reconstructs a dual graph for the bounded complementary
core of an authenticated normal cut. A rooted spanning tree removes every source
3-handle by geometric 2/3 cancellation, relative to the actual interval-bundle
ports. Maximum-weight selection minimizes retained raw attaching occurrences
after the existing fixed primal forest. It is the new default for
`normal_cut_handlebodies`; `bfs` and `disabled` remain explicit reference modes.

On the unchanged 106-case maintained corpus, complete certified cut censuses
increase from **85 to 92**, preserving all old successes. Every positive
certificate independently replays. An explicit Regina audit completes 99 cases;
all 85 directly comparable native positives agree. Seven huge inputs exceed the
explicit expansion cap. On 16 additional interior-vertex fixtures, BFS completes
11 and maximum weight completes 13. The two extra weighted successes use a
five-tetrahedron solid torus whose BFS residual is a stopping set; the article
proves that *no* positive raw pivot order can repair that residual, while the
weighted forest admits a complete geometric certificate.

The separate `research/quotient` component implements exact integer certificates
for membership or nonmembership in a rational relative-homology image. Under
authenticated Lackenby hierarchy hypotheses, the outside certificate forces a
positive even raw quadratic defect. The geometric source-to-chain compiler is
**not implemented**. The article also proves stopping-set/graphic-rank results,
nonmatroid counterexamples, an unimplemented paired-forest optimization, signed
component-witness reuse, balanced-index criteria, and raw-only potential bounds.

This is a local performance and coverage contribution, with proved mathematical
interfaces. It does not claim a quasi-polynomial bound for complete unknot
recognition. A COMPLETE cut census is not a standalone knot verdict, and an
INCONCLUSIVE result is not a non-handlebody or knottedness proof.

## Validation and measured performance

- Full integrated repository regression: **1,696 tests passed**, no failures or
  errors; `research/data/native_regression.log`.
- Focused native tests: **18 methods**, including independent replay with producers
  disabled, source forgery, wrapper downgrade, loops, dependent orders, all
  spanning trees in 128 small multigraph instances, and huge binary coordinates.
- Exact algebra: **27 methods**, including 400 random instances, 250 independent
  SymPy rank comparisons, empty dimensions, and a 16,384-bit CLI round trip.
- Seven-round randomized timings show no clear runtime difference between BFS
  and maximum weight where both complete: ratios of medians 0.9753–1.0386.
- On one four-tetrahedron Möbius family at multiplicity 512, the explicit cut has
  10,311 tetrahedra and 257 solid-torus components. Native weighted construction
  plus replay takes 29.18 ms median; Regina cut plus recognition takes 73.64 ms.
  Regina is faster on most smaller examples. These are whole-cut timings.
- At multiplicity `2**16384`, both native strategies certify and replay exactly
  `2**16383 + 1` solid tori. Weighted production plus replay takes 0.1088 seconds
  in the recorded single capacity run; the full certificate is 5,429,503 bytes.
  This is not an explicit-cut comparison or an asymptotic performance proof.

The article gives full proofs, limitations, exact source face pairings, and
fifteen concrete research directions. `provenance/claim_ledger.json` supplies
a compact machine-readable statement inventory.

## Contents

| Directory | Contents |
|---|---|
| `article/` | Complete TeX, bibliography, PDF, vector/raster figure, build log |
| `integration/` | Patch and equivalent nine-file repository overlay |
| `runtime/fast/` | Frozen native Python runtime, fixture helpers, focused tests |
| `research/experiments/` | Corpus audits, actual-cut oracle, paired timings, matrix witness, figure/summary scripts |
| `research/data/` | Exact workload, raw results, timing samples, validation logs |
| `research/certificates/` | Twenty saved source-bound census packets |
| `research/quotient/` | Independent algebraic producer/checker, examples, tests, documentation |
| `provenance/` | Source pin, Git tree manifests, environment, integration and package validation |

## Quick reproduction

Python 3.10 or later is needed; the recorded environment used Python 3.12.14.
From the extracted bundle:

```bash
python reproduce.py --quick
```

This checks `SHA256SUMS`, runs the 18 focused native and 27 algebraic test methods,
and independently replays all twenty saved census packets. Native production and
verification use the standard library and do not call Regina. SymPy enables the
independent random rank comparison; without it that comparison is skipped. The
large-decimal quotient test launches its child processes with
`PYTHONINTMAXSTRDIGITS=0`, as documented in its README.

To rerun the 106-case native audit:

```bash
python reproduce.py --full-corpus --output /tmp/proveit_dual_reaudit.json
```

For other scripts, place the frozen runtime on `PYTHONPATH`:

```bash
PYTHONPATH=runtime/fast python research/experiments/core_dual_matrix_witness.py \
  --output /tmp/proveit_matrix_witness.json
PYTHONPATH=runtime/fast python research/experiments/core_dual_benchmark.py \
  --rounds 7 --capacity --output /tmp/proveit_paired_timings.json
PYTHONPATH=runtime/fast python research/experiments/audit_regina.py \
  --corpus research/data/native_corpus.json --output /tmp/proveit_regina_audit.json
```

The last two commands require Regina (recorded version 7.4). See the scripts'
`--help` and `research/experiments/core_dual_experiments.md` for measurement
boundaries. The initial extra-fixture audit has 16 cases; the current benchmark
also includes three no-3-handle controls. Disabled-mode timings on sources with
3-handles measure abstention and are not successful-work speedup baselines.
Every timed strategy was passed explicitly. After timings, the final integration
changed only the default keyword and its docstring; provenance records this.

`research/experiments/summarize_results.py` checks the archived result claims.
`make_figures.py` rebuilds the scientific figure from recorded samples and needs
Matplotlib. Recorded dependency versions are in `provenance/environment.json`.

## Build the article

```bash
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  dual_forests_and_homological_progress.tex
```

The article uses pdfLaTeX, BibTeX's standard `plain` style, and common TeX Live
packages including Latin Modern, AMS math/theorems, microtype, booktabs,
tabularx/longtable, listings, fancyhdr, hyperref, and cleveref. The supplied PDF
was rendered and visually inspected; the final build has no undefined references,
missing citations, or overfull boxes.

## Integrate into ProveIt

Use a complete checkout at the pinned revision. Inspect the patch, then run from
the repository root (replace the example bundle path):

```bash
git apply --check /path/to/bundle/integration/dual_forest.patch
git apply /path/to/bundle/integration/dual_forest.patch
cd Topology/UnknotRecognition/fast
python -m unittest discover -s tests -v
```

The equivalent files are under `integration/overlay/Topology/UnknotRecognition/fast`.
Use either the patch or the overlay. The patch has been applied to a clean
baseline copy and its nine resulting files checked byte-for-byte against the
overlay. Native runtime additions introduce no third-party dependency.

The full historical regression suite expects the project's `reports/` and
`synthesis/` fixtures. One existing test also reads the historical Git object
`1aeabfa735c78a30b732405b101009d376d56f18`; a shallow checkout may need that
history. The frozen runtime is sufficient for this bundle's focused tests and
audits, but does not duplicate those large unrelated historical datasets.

Article and algebraic research files can be integrated into the preferred
incoming/proposal location independently. Native source licensing is preserved
in `runtime/fast/LICENSE`; embedded third-party license notices are retained.

## Priority next work

1. Implement optional alternating primal/dual forest selection, measuring
   actual certified coverage independently of the incidence objective.
2. Resolve the eight oracle-positive remaining stopping obstructions using a
   changed primal forest or an authenticated geometric intersection reduction.
3. Compile and verify the actual relative chain map of an admissible patterned
   handle structure and its interior parallelity bundle.
4. Construct a prescribed cohomology class and extract a component with positive
   signed witness evaluation without expanded normal surfaces.
5. Prove balanced progress or certified alternatives, transport full boundary
   patterns, and bound discarded histories and all maintained encodings.

The precise announced targets remain distinct: `n^{O(log n)}` in the February
2021 slides and `2^{O((log n)^3)}` in the March handout. The article supplies
primary references and states exactly which additional global estimates are
needed for either claim.
