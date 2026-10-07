# Toward quasi-polynomial unknot recognition

Research continuation for Vladimir Reshetnikov's ProveIt project, 7 October 2026.

**This package implements and proves specific performance improvements. It does
not establish general quasi-polynomial unknot recognition.** The detailed
article states what was proved, what was implemented, what was measured, and
which hypotheses are still required for the target complexity.

Start with `article/unknot_progress.pdf`. Its editable source is `article/article.tex`
with the adjacent section files and bibliography. The article includes full
proofs, raw-data-derived tables and figures, and eleven research questions
with concrete milestones.

## Source baseline

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

Pinned revision: `4e6fe879e5238ec0b134b6d33fdca0b8c7c1c711`

Subtree: `Topology/UnknotRecognition/fast`

The 40 selected baseline source/example/test files are byte-exact; their Git
blob hashes and original sizes are in `data/upstream_files.json`. Historical
results files are not needed to run the comparison. `baseline/fast` preserves
the runnable original package. The repository's MIT-0 license is included.

## Implemented changes

| Component | Proposed behavior | Mathematical scope |
|---|---|---|
| Visible factorization | Default checked interlacement decomposition, with an independent partition verifier | O(n alpha(n)) combinatorial core and O(n log(n+1)) checked PD interface; avoids a proved quadratic-work family in the original factorizer |
| Modular Alexander | Incidence-indexed sparse determinant for n >= 256; dense backend retained | O(m+E+F) field operations plus at most m inversions, with logarithmic bookkeeping; cubic worst case remains possible |
| Direct reduced scan | Optional `--pointed`; last-crossing basepoint; exact early knot decision from two isolated objects | Smaller pointed Hom spaces and a proved frontier policy, without a universal multiplicity bound |
| Resource handling | Factorization and surrounding recognition stages share the resource-limit handler | Exhaustion returns `UNKNOWN`; budgets remain cooperative |
| Complexity documentation | General frontier count corrected to (w-1)!!; Catalan requires a certified common disk | A supplied exact counterexample occurs even under an existing fixture's default scan order |

The component/interlacement correspondence, reduced Khovanov construction,
and sparse elimination principles have established precedents. The article
attributes them and identifies the implementation-specific contributions.

The ordinary full-rank scanner is still the default. The final pointed
experiment is mixed: its stress-case paired ratio is about 0.723, while
several small cases are slower. Fixed-size visible trefoil factors show
much larger factorization gains, supported by a structural complexity proof.
For exact times and interval definitions see the article and
`data/benchmark_summary.csv`.

## Run the updated recognizer

Python 3.10 or newer; the recognition package uses only the standard library.
From this unpacked top-level directory:

```sh
PYTHONPATH=fast python3 -m fastunknot recognize fast/examples/conway.json
PYTHONPATH=fast python3 -m fastunknot recognize fast/examples/conway_sum_3.json --legacy-factor
PYTHONPATH=fast python3 -m fastunknot recognize fast/examples/conway.json --no-alexander --no-jones --pointed
```

Exit codes remain 0 for either exact verdict, 2 for invalid input/options,
and 3 for `UNKNOWN`. `--pointed` currently requires minfill pivots, bits
algebra, tail 0, and race 1. The old API remains available for comparisons.

### Evidence and rank interfaces

The default factorization returns `connected_sum_factorization` with a
component partition and an interlacing forest. The legacy backend retains
`connected_sum_cuts`. This evidence schema is an intentional integration
change; clients that parse cut traces should opt into the legacy backend or
adopt the new certificate verifier.

`alexander_obstruction` preserves the original witness dictionary and adds
optional `backend`, `check`, and `statistics` arguments. Its generic sparse
determinant requires a prime modulus; primality is a caller precondition.
Fixed evaluation constants do not supply a probabilistic completeness claim.

`reduced_khovanov_rank` uses **reduced** ranks in both `rank` and
`reduced_rank`, and reduced counts in `by_degree`. The original
`khovanov_rank` continues to use an **unreduced** `rank` and degree counts.
`reduced_khovanov_decision` may stop with `reduced_rank=None`, a lower bound,
and replay data. Those data are not a small independent topological certificate.

## Reproduce correctness checks

```sh
PYTHONPATH=fast python3 -m unittest discover -s fast/tests -v
python3 tools/verify_factorization.py --output data/reproduced_factorization.json
python3 tools/verify_reduced_scan.py --output data/reproduced_reduced.json
python3 tools/verify_frontier_counterexamples.py --output data/reproduced_frontiers.json
python3 tools/hierarchy_budget.py --self-test --output data/reproduced_hierarchy.json
python3 tools/verify_package.py
```

The finite checks cover 146,600 double-occurrence words, 3,323 validated
factorization diagrams, 2,898 dense-cube reference diagrams, 8,002 pointed
rank scans, 2,898 decision scans, and separate algebra and hierarchy audits.
These counts include repeated knot types and overlapping scan variants.
`data/unit_tests.txt` records the final complete regression run.

## Reproduce measurements

```sh
python3 tools/benchmark_progress.py --output data/reproduced_paired.json
python3 tools/benchmark_reduced_scan.py --output data/reproduced_pointed.json
```

These are real repeated computations and take longer than the quick tests.
The baseline factorizer is deliberately run on its quadratic-work family.
For a shorter exploratory run, `benchmark_progress.py` accepts `--kinds`
and `--largest-sum`; such a run is not a reproduction of the complete dataset.

The authoritative article tables use:

- Factorization: `data/paired_benchmarks.json`.
- Sparse determinant and full pipeline: `data/paired_benchmarks_final.json`.
- Pointed scanner: `data/reduced_benchmark_final.json`.

Earlier results remain available. The first paired package sources are
preserved under `data/benchmark_sources/initial`; the final pointed run
captures its exact sources and fixtures before timing. The historical pointed
prototype was not snapshotted before its original run, which its provenance
explicitly records. No historical job order or source hash was fabricated.
The final public API was measured again to remove that ambiguity.

Each paired experiment randomizes A/A/B/B arms and retains controls. The
factor/sparse/pipeline block ratio uses arithmetic arm means and a nominal
96.1% order-statistic interval from nine blocks. The pointed experiment uses
geometric arm means and nominal 95% percentile bootstrap intervals. Pooled
time medians and median paired ratios need not divide to the same number.
Intervals concern fixed inputs in this environment; no distribution over
all knots or CPU isolation is assumed.

## Build the article

```sh
python3 tools/render_results.py
sh tools/build_article.sh
```

Matplotlib is needed only to regenerate the figures. `--tables-only` avoids
that dependency. Pre-generated vector and PNG figures are included. The PDF
build uses `latexmk`, `pdflatex`, BibTeX, and standard LaTeX packages.

## Integrate into ProveIt

Read `integration/README.md`. The patch targets the pinned `fast` subtree
and has been checked by applying it to an isolated copy of that baseline and
comparing the result byte-for-byte with the updated source tree. It does not
change the Rust implementation. The article/tools/data can be placed in a new
dated research directory using the repository's preferred layout.

`SHA256SUMS` covers the deliverable files, excluding itself. The package
verification script checks both that manifest and the archived Git blobs.
It does not modify a user's repository.

## Research directions

The article develops eleven topics: frontier topology; certified noose
decompositions; compositional tangle-complex compression; earlier decision
certificates; pointed-backend selection; Alexander fill bounds; exposure of
hidden decompositions; bounded hierarchy state volume; compressed geometric
operations; a harder filter-surviving corpus; and small formal certificate
checkers. The conditional theorems spell out the missing width, multiplicity,
uniform-cap, epoch, search, and encoded-size bounds.
