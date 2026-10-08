# Unknot recognition by continuation quotients and certified algebraic splitting

**Research continuation and runnable `fastunknot` 0.4.0 implementation.**

This package develops three optional additions to the ProveIt unknot recognizer:

1. **Interval normalization:** an exact binary change of basis decomposes a
   whole differential summand when its objects share one matching and every
   nonzero differential entry is one common square-zero coefficient.
2. **A shorter decision representation:** after that exact decomposition,
   intervals of length greater than two can be replaced by length-two
   intervals while preserving the final unreduced Khovanov rank capped at
   three under every remaining ordinary closure.
3. **Certified scalar Fitting splitting and exact window ordering:** the
   splitter searches for hidden direct summands and verifies accepted basis
   changes; the ordering pass optimizes a precise frontier objective over a
   bounded window of crossings.

The standard scanner remains the default. The new backends and ordering pass
are **opt-in**. The complete recognizer retains an exponential worst-case
upper bound; **this package does not establish a general quasi-polynomial
unknot algorithm**.
The article proves an explicit quasi-polynomial sufficient condition involving
frontier width, suitable normalization checkpoints, and the distances between
them. It does not prove that every knot diagram satisfies that condition.

## Start here

Read [`paper/unknot_continuation_quotients.pdf`](paper/unknot_continuation_quotients.pdf)
for the complete article, proofs, experiments, and research agenda. The LaTeX
entry point is
[`paper/unknot_continuation_quotients.tex`](paper/unknot_continuation_quotients.tex).
[`REPRODUCING.md`](REPRODUCING.md) describes verification, benchmarking, figure
regeneration, and patch checks in detail.

Python **3.10 or later** is sufficient for the recognizer and verification
programs. They use the Python standard library. No installation is needed
when running from the included `fast/` directory:

```bash
cd fast
python -m unittest discover -s tests -v
python -m fastunknot recognize examples/conway.json --backend fitting
python -m fastunknot khovanov examples/conway.json --fitting
```

The recognition command may finish through an existing structural certificate
or polynomial filter before reaching the requested backend. The `khovanov`
command computes the raw exact homology ranks with that backend. The supplied
benchmark bypasses the recognition filters deliberately.

## Exact ranks and decisions have different contracts

| Interface | Representation | Result |
|---|---|---|
| `khovanov --barcode` | Exact interval decomposition and component sharing; complete interval lengths retained | Exact total rank, reduced rank, and raw homological-degree counts |
| `khovanov --fitting` | Verified scalar basis changes, exact interval decomposition, and sharing | The same exact rank information; optional split witnesses through the Python API |
| `recognize --backend barcode` | Interval decomposition, length cutoff two, and multiplicities capped at three | An exact unknot verdict when completed, with capped backend rank |
| `recognize --backend fitting` | Verified scalar splitting followed by the same decision representation | An exact unknot verdict when completed, with capped backend rank |
| `--order-window K --order-passes P` on `recognize` | Optional exact optimization of overlapping windows | A valid scan order with a nonworsening chosen frontier objective |

An exact result contains `rank`, `reduced_rank`, and `by_degree`. A completed
decision result contains `rank_capped`, `rank_cap=3`, and ordinarily
`length_cap=2`. The capped value three means **at least three**, not exact rank
three. On a valid classical knot, unreduced rank is even, so it means at least
four. Rank two characterizes the unknot by the established Khovanov
unknot-detection theorem and the coefficient argument given in the article.

Length shortening preserves the specified final observation. It generally
does **not** preserve exact rank, the chain-homotopy type, homological-degree
counts, or cycle representatives. Do not use the shortened decision model as
an exact homology computation. After shortening, the stage statistic
`weighted_decision_model_objects` describes the altered representation, not
the original chain dimension; `decision_equivalence_only` records this
boundary explicitly.

The low-level Python entry points are:

```python
from fastunknot import Diagram
from fastunknot.barcode_scan import (
    barcode_khovanov_rank,
    barcode_khovanov_decide,
)
from fastunknot.scalar_split import (
    fitting_khovanov_rank,
    fitting_khovanov_decide,
)

diagram = Diagram.from_braid(3, [1, -2, 1, -2])
exact = fitting_khovanov_rank(
    diagram.pd, record_witnesses=True, check_d_squared=True
)
decision = fitting_khovanov_decide(diagram.pd)
assert decision["rank_capped"] == min(3, exact["rank"])
```

These low-level scanner functions assume a validated classical one-component
diagram. Use `Diagram.from_pd`, `Diagram.from_braid`, `Diagram.from_json`, or
the command-line loader. The permissive bare `Diagram(...)` constructor is
not a substitute for validation. Quantum grading is intentionally forgotten;
exact mode retains the existing raw cube homological-degree convention.

## Budgets and optional searches

An example with an additional ordering pass is:

```bash
python -m fastunknot recognize examples/conway.json \
  --backend fitting --order-window 10 --order-passes 2 \
  --seconds 3 --max-objects 50000
```

Run it from `fast/`. The recognizer charges the optional planner to its
recognition budget. Time budgets are cooperative. A global object or time
limit causes low-level `ScanLimit` exhaustion and a pipeline result of
`UNKNOWN`; exhaustion is never a knot verdict. The object ceiling is checked
before building a crossing extension, even when a later normalization might
have shrunk that extension.

The scalar splitter also has local search limits: by default it considers
components of at most 48 objects, at most 1,024 scalar variables, at most 16
accepted splits per crossing, and a bounded deterministic candidate collection.
Exceeding a local search limit simply retains the unresolved component and
continues the complete backend. Failure to find a split is not a proof of
indecomposability. These local limits and the distinction from global scanner
limits are documented in the source and article.

The new compressed command-line routes use minimum-fill pivots, bit algebra,
no tail contraction, and no racing. Incompatible options are rejected. Exact
`--shared`, `--barcode`, and `--fitting` are mutually exclusive and cannot be
combined with `--factor`.

## What the evidence does and does not show

The measured real-diagram corpus contains named examples, an explicitly
unselected seeded braid sample, and one separately labeled example selected
by an exploratory scalar-split search. Accepted scalar Fitting splits occur
on actual diagrams, and their full basis changes are recorded and replayable.

**No eligible nonsingleton barcode component was observed in the measured
real-diagram corpus under the recorded orders and configurations.** The
interval shortening theorem is implemented and tested, including on abstract
valid complexes, but its benefit must not be described as an observed
shortening speedup on those real diagrams. The synthetic representation
stress tests are labeled separately.

Operation savings and smaller representations do not guarantee lower running
time. Solving endomorphism equations, checking certificates, and maintaining
shared templates have costs. The window planner optimizes a frontier proxy,
not elapsed homology time. The article and benchmark records report both
these limitations and the measured outcomes. This README intentionally does
not duplicate timing values that may be regenerated on another machine.

## Package layout

| Path | Contents |
|---|---|
| `paper/` | Complete LaTeX article, compiled PDF, generated tables, and figures |
| `fast/` | Runnable version 0.4.0 source, tests, examples, and license |
| `verification/verify_continuation.py` | Independent finite-matrix continuation check; imports no recognizer code |
| `benchmarks/run_benchmarks.py` | Reproducible paired raw-backend experiment and labeled synthetic tests |
| `benchmarks/paired_results.json` | Recorded inputs, orders, budgets, runs, operation statistics, and environment |
| `benchmarks/verify_fitting_witness.py` | Independent dense verification of emitted scalar split witnesses, with optional full scan replay |
| `benchmarks/summarize_results.py` | Regeneration of summary CSV/JSON and the benchmark audit |
| `benchmarks/make_figures.py` | Regeneration of the article's tables and figures from the raw results and summaries |
| `integration/from_repository.patch` | Cumulative update from the pinned ProveIt repository source |
| `integration/from_structural_0_3.patch` | Incremental update from structural-compression version 0.3.0 |
| `reference/repository-fast/` | Unchanged pinned repository reference files |
| `reference/structural-fast/` | Unchanged structural-compression 0.3.0 reference |
| `provenance/` | Source identities, verification records, build and validation evidence |
| `scripts/verify_manifest.py` | Delivered-file integrity verification |
| `scripts/verify_patches.py` | Independent patch application and output comparison |
| `scripts/build_pdf.sh` | Article build through `latexmk` |

## Integration into ProveIt

The inspected repository revision is
`eb79136d949a1c0e6f4bd2f07e6b3990d1130632`; the relevant `fast` tree has Git
identifier `b99a666269f660d932fc82ac8d1f29d3ae42231f`. The development base
adds the preceding structural-compression 0.3.0 package to those repository
bytes. The supplied references and provenance make both starting points
explicit.

Both patches target `Topology/UnknotRecognition/fast/`. **Choose one patch,
according to the tree you are updating; do not apply both.** From the root
of the destination ProveIt checkout, with a path to this extracted package:

```bash
UNKN_PACKAGE=/absolute/path/to/unknot_continuation_quotients
git apply --check "$UNKN_PACKAGE/integration/from_repository.patch"
git apply "$UNKN_PACKAGE/integration/from_repository.patch"
```

For an already integrated structural 0.3.0 tree, use
`integration/from_structural_0_3.patch` in both commands instead. Run the full
test suite from `Topology/UnknotRecognition/fast/` after applying the selected
patch. The article and evidence directories can be placed with the repository's
other research reports; the patches update the software tree.

The independently developed three-braid, pointed-homology, sparse-Alexander,
or factorization continuation is not claimed to be merged into this package.
If those changes are already present, reconcile shared front-end files and
run the combined tests before relying on the integrated tree. This archive
itself does not modify the remote repository.

Project source is supplied under the included **MIT-0** license. External
mathematical papers and slides are cited by bibliographic links; their full
texts are not redistributed here.
