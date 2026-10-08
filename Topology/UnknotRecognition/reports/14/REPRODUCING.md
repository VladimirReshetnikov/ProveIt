# Reproducing the continuation-quotient research package

This guide distinguishes four different checks: file provenance, executable
correctness tests, recorded algebraic certificates, and performance experiments.
None of them establishes that every knot diagram satisfies the article's
conditional quasi-polynomial checkpoint bound. The mathematical proof of the
continuation quotient is in `paper/mathematics.tex`, with the derived
classification proved in `paper/derived_classification.tex`.

Unless a command explicitly changes directory, run it from the extracted
`unknot_continuation_quotients/` package root. Commands use `python`; substitute
`python3` if that is the name of the appropriate interpreter on your system.

## 1. Requirements and integrity

The recognizer, unit tests, benchmark, continuation checker, and witness
verifier require **Python 3.10 or later** and the standard library. Running
directly from `fast/` does not need a package installation. Git is needed to
apply or verify the integration patches. The PDF build uses a shell,
`latexmk`, and a standard LaTeX installation containing the packages listed
in the main preamble. Figure regeneration additionally requires Matplotlib;
it is not needed for the recognizer or algebraic verification. On Windows,
the shell build command can be run through Git Bash or WSL with the required
LaTeX tools available.

Check the untouched delivered package before regenerating its outputs:

```bash
python scripts/verify_manifest.py
python scripts/verify_patches.py
```

The first check compares delivered files with their recorded integrity data.
The second applies each patch to a fresh copy of its corresponding supplied
reference and checks the resulting source against the delivered `fast/` tree.
It is separate from applying a patch to your working repository.

The references are:

| Reference | Patch | Starting point |
|---|---|---|
| `reference/repository-fast/` | `integration/from_repository.patch` | The inspected ProveIt `fast` tree at revision `eb79136d949a1c0e6f4bd2f07e6b3990d1130632` |
| `reference/structural-fast/` | `integration/from_structural_0_3.patch` | The preceding structural-compression 0.3.0 source |

The relevant pinned repository tree identifier is
`b99a666269f660d932fc82ac8d1f29d3ae42231f`. Source byte identities, including
Git blob identifiers and SHA-256 records, are in `provenance/`.

Keep an untouched copy of the archive if you want to compare regenerated
results with the delivered records. A new run may legitimately change
timestamps, timings, environment descriptions, generated figures, and other
recorded bytes; the delivered manifest describes the original package.

## 2. Run the complete unit suite

```bash
cd fast
python -m unittest discover -s tests -v
cd ..
```

The new checks include binary rank and interval calculations, exact and
decision backend agreement, reconstruction of scalar Fitting witnesses,
configured search limits, order optimization against exhaustive small
permutations, and comparisons on validated knot diagrams. The inherited
tests exercise the structural front end, component sharing, prior scan
implementations, and integration behavior.

For a targeted check, from `fast/`:

```bash
python -m unittest discover -s tests -p 'test_barcode_scan.py' -v
python -m unittest discover -s tests -p 'test_scalar_split.py' -v
python -m unittest discover -s tests -p 'test_order_dp.py' -v
```

The scalar witness tests use a dense verifier in addition to the splitter's
own packed arithmetic. The finite comparisons support the implementation;
they do not replace the theorem justifying interval shortening.

## 3. Independently check the continuation observation

From the package root:

```bash
python verification/verify_continuation.py
```

To save a fresh record at a chosen path:

```bash
python verification/verify_continuation.py \
  --output verification/continuation_results_rerun.json
```

This program imports **no `fastunknot` module**. It enumerates small bounded
complexes equipped with strict square-zero actions, including nonfree
dual-number modules and unit differentials. It constructs the total tensor
differential directly as a binary matrix, checks that it squares to zero,
and computes homology dimensions without using the barcode implementation
or the derived classification.

It checks both relevant assertions:

- For arbitrary such module complexes, rank capped at three is unchanged
  when interval length is capped at three.
- When the length-one continuation has even total homology dimension,
  the cutoff can be reduced to two, as in ordinary unreduced scanner closures.

The record also includes the sharp counterexamples: a simple module defeats
an unconditional cutoff of two, and two simple modules defeat cutoff one
even in the even-rank context. These examples help detect an implementation
that applies the geometric cutoff without its parity hypothesis.

## 4. Verify and replay the actual Conway split certificates

Check the included recorded basis changes independently:

```bash
python benchmarks/verify_fitting_witness.py \
  benchmarks/conway_fitting_witnesses.json
```

The default verifier checks preservation of matching and homological degree,
the equation `Qd=dQ`, invertibility of the basis change, exact transformation
and reconstruction of all differential entries, and vanishing cross terms
between the proposed summands. It uses dense scalar matrix operations and
does not import the recognizer for this local verification.

To reconstruct the scan from the included PD code and recorded order as well:

```bash
python benchmarks/verify_fitting_witness.py \
  benchmarks/conway_fitting_witnesses.json --replay
```

Replay invokes the exact Fitting backend with `check_d_squared=True`, checks
the final rank, and compares its emitted witnesses with the recorded ones.
A local witness certifies an exact basis change of the supplied matrix. The
replay connects those matrices to this particular input and execution.
Neither step formally verifies the inherited cobordism algebra or replaces
the topological unknot-detection theorem.

## 5. Reproduce the paired raw-backend experiment

The published configuration is **19 diagram cases, five backends, and three
interleaved repetitions**, or 285 timed backend calls. Each call has a
cooperative **3-second** budget and a **50,000-physical-object** ceiling:

```bash
python benchmarks/run_benchmarks.py \
  --output benchmarks/paired_results.json \
  --repeats 3 --seconds 3 --max-objects 50000 --random-count 8
```

This command regenerates the canonical raw-results file and the Conway
witness file beside it. To preserve the delivered data, choose an output
path in a separate directory; the script creates that directory and places
its witness export alongside the chosen JSON. The figure-generation command
in the next section uses the canonical package benchmark files.

### Corpus and selection

The 19 cases comprise:

- Seven named examples: `hard_unknot_8`, `conway`, `kinoshita_terasaka`,
  `conway_sum_2`, `conway_sum_3`, `conway_sum_8`, and `stress_braid5_36`.
- Three generated torus-knot braid closures: `torus_3_11`, `torus_4_9`,
  and `torus_5_8`.
- The first eight valid one-component closures produced by the recorded
  random generator and seed `54287`, labeled `random_unselected`.
- The 24th valid closure of that same stream, separately labeled
  `selected_split_example`. An exploratory probe selected this case for
  having a scalar split. It is not part of an unselected random-frequency
  estimate.

The five backend identifiers are:

| Identifier | Computation |
|---|---|
| `standard` | Existing raw exact scanner |
| `component` | Prior literal component-sharing exact backend |
| `fitting_exact` | Scalar Fitting splitting with exact interval lengths |
| `fitting_decision` | Scalar Fitting splitting with length cutoff two and rank cap three |
| `fitting_decision_dp` | The same decision backend after exact window-order optimization |

### Timing and budget accounting

All five backends receive the same initial greedy order, chosen using at most
twelve starting crossings. Its construction time is recorded separately.
The summaries include a measure adding that common initial-order cost back
to the median. The DP variant pays for its additional optimization in its
own measured call and its 3-second budget; its scan and planner times are
also recorded separately.

The benchmark rotates backend order between repetitions, records each run,
and reports medians of completed calls. Import and initialization warmup
uses a small knot outside the measured corpus. The script also runs labeled
synthetic algebraic examples and exports the Conway witness outside the
timed samples. Those extra operations and initial order construction are
not covered by an overall 285-times-3-second wall-clock guarantee. Time
limits are cooperative, so small overruns are possible.

No simplification, Seifert certificate, Alexander/Jones filter, or visible
connected-sum factorization is used in these raw-backend measurements.
Consequently their timings are **not whole-pipeline recognition timings**.
Earlier filters can decide some of the displayed knots before a selected
backend is reached in normal use.

The JSON records complete input descriptions and PD codes, actual orders,
per-call outcomes, statistics, stage histories when available, environment
information, and monitored source hashes before and after the run. Compare
`source_unchanged_during_run` and the recorded source identities before
combining measurements from different executions.

### Interpretation boundaries

An `outcome` of `resource_limit` is an incomplete run, not a wrong answer and
not a mathematical verdict. The script checks agreement among completed
exact results and compares completed capped results with an exact rank when
an exact result is available for that case. A timeout alone establishes no
asymptotic improvement.

The included measured real-diagram corpus has **no observed eligible
nonsingleton barcode components** under its recorded orders and settings.
Thus real-diagram operation changes in this experiment come from exact
scalar splitting, sharing, and ordering, not from an observed application
of long-interval shortening. The synthetic examples separately exercise
the interval representation and its cutoff. They are valid abstract
complexes, not asserted realizable families of knot prefixes.

The deterministic counters isolate some algorithmic work but do not price
all bookkeeping or predict elapsed time. Fewer compositions or stored
objects can coexist with a slower run. Three repetitions characterize this
recorded experiment; they do not provide a universal speed guarantee or a
large-sample statistical claim. For a new performance claim, rerun on the
intended inputs and environment with the full preprocessing and failed
search costs included.

## 6. Regenerate summaries, figures, and the article

After producing the canonical `benchmarks/paired_results.json`, regenerate
the experiment material:

```bash
python benchmarks/summarize_results.py
python benchmarks/make_figures.py
```

The summarizer produces `summary.json`, `summary.csv`, and
`benchmark_audit.json` beside the raw input. It checks completed exact/capped
agreement and, when the supplied earlier record is present, audits the
before/after lazy-normalization comparison. Its `--input` and `--before`
options select the files explicitly. If a changed experiment has different
resource-limited cases or different deterministic counters, inspect the
reported comparison differences rather than interpreting them as a timing
measurement.

The figure script reads the canonical raw results and summary JSON, writes
the LaTeX tables under `paper/tables/`, and places PDF/PNG figures under
`paper/figures/`. Matplotlib is needed for this second command. It is not
necessary merely to rebuild the PDF from the included figures and table
fragments.

Build the article from the package root:

```bash
sh scripts/build_pdf.sh
```

The script changes to `paper/` and invokes `latexmk` with PDF output,
noninteractive processing, file-and-line diagnostics, and stop-on-error
behavior. Its entry point is `unknot_continuation_quotients.tex`; the
result is `paper/unknot_continuation_quotients.pdf`. The bibliography is
included as a LaTeX source fragment, so a separate external bibliography
database is not required.

Rebuilding the figures or PDF does not recreate the original manifest or
recorded verification logs automatically. Preserve the delivered records
when comparing them with a modified research run.

## 7. Apply one integration patch and verify the combined tree

Choose the patch according to the source already in the destination checkout.
The cumulative patch is for the pinned repository tree; the incremental
patch is for an already integrated structural 0.3.0 tree. **Do not apply both.**
All patch paths are rooted at `Topology/UnknotRecognition/fast/`.

For the cumulative update, from the destination ProveIt repository root:

```bash
UNKN_PACKAGE=/absolute/path/to/unknot_continuation_quotients
git apply --check "$UNKN_PACKAGE/integration/from_repository.patch"
git apply "$UNKN_PACKAGE/integration/from_repository.patch"
cd Topology/UnknotRecognition/fast
python -m unittest discover -s tests -v
```

For the incremental update, substitute `from_structural_0_3.patch` in the
two patch commands. If the destination includes other work, first inspect
and reconcile any overlapping changes; successful reproduction against the
included references is not a proof that an unrelated branch can be merged
without review. In particular, this package does not claim to include the
independent three-braid, pointed-homology, sparse-Alexander, or factorization
continuation. Shared front-end and configuration files require combined
testing after those branches are reconciled.

The included complete `fast/` tree also permits a direct source comparison
when reviewing a merge. The article, verification programs, benchmark
records, and provenance can be stored with the repository's research reports;
the software patches intentionally target the recognizer tree.

## 8. What each level of verification establishes

| Evidence | What it establishes | What it does not establish |
|---|---|---|
| Source identities and manifest | Identity of the recorded and delivered file bytes | Correctness of every mathematical assertion |
| Patch verification | Each supplied delta reproduces the delivered source from its corresponding reference | Automatic compatibility with another development branch |
| Unit tests | The enumerated finite implementation comparisons and regression checks | Correctness solely from testing on all future inputs |
| Independent continuation checker | Finite matrix consequences and sharp cutoff counterexamples, without importing the implementation | A replacement for the all-continuations proof |
| Fitting witness verification | The recorded complete basis changes and direct-summand splits | A complete indecomposable decomposition algorithm |
| Scan replay | Agreement of one recorded input execution, rank, and witnesses | Formal verification of the entire inherited category |
| Paired benchmark | Observations on the recorded inputs, settings, and host | A general speedup or a general quasi-polynomial bound |

The new backends remain optional. Without global resource limits, unresolved
components continue through the complete inherited scanner. The central open
complexity obligation is to prove sufficiently frequent suitable checkpoints
with controlled frontier and coefficient complexity for a substantial
uniform class of residual diagrams.
