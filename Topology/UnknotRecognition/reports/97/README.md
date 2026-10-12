# Stopping Sets, Saturated Bundles, and Exact Raw Cancellation

Research continuation for ProveIt's unknot-recognition project, 12 October 2026.

**Start with [the article](article/Stopping_Cores.pdf).** Its complete TeX source is
[article/Stopping_Cores.tex](article/Stopping_Cores.tex). The article develops the
proofs, identifies prior art, explains the source contracts, reports the complete
measurements, and proposes ten concrete research directions.

This package targets ProveIt commit
`704600626606a9097cfd89d4e3d2bbc63c8dd1cb`. It is prepared for review and integration
into `Topology/UnknotRecognition`; no remote repository was modified.

## Main contributions

1. **Complete rectangular raw cancellation.** For a nonnegative integer matrix,
   complete positive singleton elimination is equivalent to complete unit-column
   peeling. A nonempty stopping set persists under every allowed positive pivot.
   The resulting indexed kernel takes linear structural work in sparse source
   incidence and supplies either a complete schedule or a stopping obstruction.
2. **Independent certificates and exact count transport.** A separate checker
   validates schedules from source deletion timestamps. An additional module
   transports exact, uncapped passenger counts through the resulting donor DAG,
   with a proved polynomial bound on bit growth.
3. **Saturated interval bundles.** Each fully attached bordered base contributes
   one aggregate relation on old core cocores. Every additional relative band
   column is even and can never be a singleton pivot. Complete cancellation can
   therefore omit all numerical base-genus expansion. The implementation binds
   those rows to authenticated source annular charts and independently verifies
   the resulting whole-cut handlebody census.

The peeling/stopping-set construction is classical in coding theory. The article
attributes that prior art and develops the persistence and geometric consequences
needed here. The incoming hierarchy report already proves one residual two-handle
per saturated base; this work adds exact source incidences, excluded band columns,
and native joint cancellation. No exhaustive literature-priority claim is made.

The old minimum-fill capped planner was already complete for full raw cancellation.
Its replacement improves the algorithm and proof, not its complete-success class.
The separate saturated-bundle extension supplies the new geometric coverage.

## Recorded outcomes

| Evidence | Result |
|---|---|
| Exhaustive small-matrix comparison | 31,096 matrices; all legal saturated pivot schedules agree with peeling and the baseline |
| Random all-subset and matching comparison | 350 seeded matrices |
| Maintained suite | 1,687 tests passed in 365.654 s |
| Later-added passenger module | 10 tests passed separately; final tree collects 1,697 tests |
| Core-only substitution in the old cut consumer | Unchanged: 78/106 complete; 156 successful old/new proofs replayed |
| New saturated cut consumer | **85/106 complete**, preserving all 78 previous successes |
| Independent new source replays | 85/85 passed |
| Fresh Regina comparisons | All 78 successful cases within the literal expansion cap agree, including all seven new cases |
| Remaining refusals | 11 combined raw stalls and 10 cores with three-handles |

The seven new cases and the seven large-coordinate successes without literal
expansion are different sets. Full native inputs and source certificates for the
new cases are included. `worked_case_019.json` provides the exact small matrix
printed in the article.
All eleven remaining raw stalls also have independently verified source stopping
witnesses in `stopping_obstructions.json`: six already occur in the original core,
and five require the added saturated disk relations. These are obstructions to
the specified raw rule, not negative topological certificates.

### Paired performance results

Five alternating-order paired trials, CPython 3.12.14 in the recorded shared
runtime. Ratios divide the baseline median by the new median.

| Scope | Baseline | New | Ratio |
|---|---:|---:|---:|
| Synthetic bidiagonal producer, 4,096 rows | 7.457 s | 7.258 ms | 1,027.45× |
| Synthetic conditional replay, 256 rows | 729.837 ms | 0.776 ms | 939.98× |
| All 106 prepared source core producers | 4.807 ms | 6.515 ms | **0.738×** |
| The 24 affected source core producers | 1.397 ms | 0.974 ms | 1.435× |
| All 90 successful core replays | 7.084 ms | 5.703 ms | 1.242× |
| Complete 106-case old cut query | 36.515 s | 36.211 s | **1.008×** |

The aggregate small-core measurement regresses. The complete query is effectively
unchanged. The synthetic gains isolate avoidable kernel work and are not a
thousand-fold speedup of knot recognition. The new saturated audit is a coverage
experiment, not a paired speed comparison.

## Package map

| Location | Contents |
|---|---|
| `article/` | Complete TeX, references, compiled PDF, scientific figure, build and figure scripts |
| `integration/` | Repository-relative patch, 14 full updated files, base/new hashes, portable application checker, isolated application evidence |
| `artifacts/column_cancellation/` | Raw timing samples, exact operation counters, source outcomes, focused 36-test log |
| `artifacts/saturated/` | Full audit, seven source certificates, exact new cases and worked matrix, 17-test log, provenance, portable driver |
| `artifacts/source/` | Exact retained corpus and historical comparison audit |
| `artifacts/validation/` | Maintained-suite log, separate passenger log, validation summary |
| `CLAIMS.json` | Machine-readable status and scope of the principal results |
| `SHA256SUMS.txt` | Package file checksums |
| `verify_package.py` | Standard-library checksum verifier |

## Integrate and reproduce

Follow [integration/README.md](integration/README.md) for the clean-worktree
workflow. The helper checks the pinned HEAD, original affected files, fixture,
patch and resulting hashes. It defaults to checking; `--apply` explicitly applies
the prepared patch. It never stages, commits or pushes.

The overlay changes two existing core files and adds twelve files, including the
new modules, tests, benchmark, baseline copies and results. Legacy v1 core proofs
remain supported; the new column path uses nested core v2. The saturated wrapper
is opt-in and does not change the main recognizer dispatcher.

From `Topology/UnknotRecognition/fast` in the patched checkout:

```sh
python3 -m unittest tests.test_column_cancellation tests.test_normal_cut_saturated tests.test_raw_passenger_transport -v
python3 -m unittest discover -s tests
python3 benchmark_column_cancellation.py --trials 5 --output results/column_cancellation_local.json
```

The [saturated audit instructions](artifacts/saturated/README.md) explain the
`--checkout` / `PROVEIT_CHECKOUT` driver and optional fresh Regina oracle. The
article's reproduction appendix gives complete examples for single-certificate
replay, source-cut production and exact passenger transport.

Rebuild the article with:

```sh
python3 article/build.py
```

The included figure is already built; `article/make_figures.py` regenerates it
from the retained benchmark JSON with Matplotlib. The LaTeX build uses `latexmk`
or `pdflatex` and the packages listed in the TeX preamble.

## Mathematical boundaries and next milestone

A raw stopping set obstructs the selected positive cancellation model. It is not
a nonhandlebody or knottedness certificate. Combined full cancellation implies
that the original-core row submatrix is also fully cancellable; joint scheduling
preserves compatibility with the attached bundles, rather than curing an old-core
raw obstruction. The article gives a counterexample to committing prematurely
to an arbitrary core-only schedule.

The new geometric output is an **unmarked, supplied-cut handlebody census**.
It does not construct inherited embedded boundary patterns, find useful normal
surfaces, or prove a bound on total hierarchy branching and rebuilding. The
global `n^{O(log n)}` target remains open for this implementation.

The next substantive milestone is to transport an authenticated embedded boundary
pattern through a complete no-fill schedule, retaining cyclic order and source
addresses, and then certify one subsequent hierarchy cut. The exact passenger
theorem supplies numerical transport, but that geometric step still needs proof
and implementation. The article also proposes work on stopping-core repairs,
source-forest changes, three-handle cancellation, the remaining eleven stalls,
reuse of incoming interface kernels, useful-surface coverage, and a global
branching/state-size potential.

This is a ChatGPT-assisted research development with separate mathematical
derivations, independent code replay and explicit experiments. Those checks are
documented here; they do not constitute external peer review.
