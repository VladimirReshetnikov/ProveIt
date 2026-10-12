# Exceptional Rows and Fast Certificate Replay for Unknot Recognition

Research continuation for ProveIt, 12 October 2026.

**Read the article:** `article/exceptional_rows_and_certificate_replay.pdf`.
Its complete LaTeX sources, figures, and bibliography are in `article/`.

This delivery contains proved local algorithms, verified native improvements,
reproducible experiments, and twelve further research projects. It does **not**
claim a complete quasi-polynomial unknot-recognition algorithm.

## Main results

1. **Exact exceptional-row reduction.** Tree-compatible unsigned peeling is
   characterized by a fixed collection of ordinary source-SCC requirements
   and a monotone closure function on the exceptional rows.
2. **Order-ideal algorithms.** If the nonfree special-SCC reachability poset
   has `J` ideals and width `w`, discovery takes `J poly(N)` time with one-sided
   randomization, or `J (m+1)**w poly(N)` deterministically in polynomial space.
   For `k` native unit-triple columns, `J <= 2**d <= 8**k`. Fixed width therefore
   gives a deterministic polynomial local algorithm. A deterministic
   `2**q J poly(N)` Kirchhoff counting alternative is proved but not separately
   implemented.
3. **An optimal raw lower-forest parameter.** The minimum remaining triple
   count is `|E3| - rank_G(E3)`. Choosing `E3` first achieves it. In this corpus
   it reduces the histogram from `(81,12,5,7,1)` for `k=0..4` to `(94,12)` for
   `k=0..1`. Raw finite completion changes from 100/106 to 106/106; attachment
   and terminal topology must still be checked.
4. **Measured native speed.** The behavior-preserving speed patch reduces
   the sum of per-case median full-query times from 55.7582 s to 42.6671 s,
   a 1.3068× speedup or 23.48% reduction. Independent replay improves by
   1.5431×. Five paired rounds cover all 106 native cases, with exact equality
   of all returned results, statistics, censuses, and certificates.
5. **Five additional full native certificates.** An optional bounded
   lower-forest portfolio increases whole-cut census coverage from 92/106
   to 97/106. All five new packets pass the unchanged public source-bound
   verifier. These are source-cut results, not standalone knot verdicts.

The article separates written proofs, finite audits, fresh source geometry,
native certificate replay, historical oracle classifications, and conditional
global-complexity statements. The proofs have not been formalized in Lean.

## Contents

| Location | Contents |
| --- | --- |
| `article/` | PDF, main TeX, section sources, bibliography, vector and raster figures |
| `code/triple_forest_research/` | Standalone finite discovery algorithms and unchanged independent checker |
| `code/lower_forest_research/` | Optional native producer portfolio and complete refusal audit |
| `code/independent/` | Independently written schedule, basis-polynomial, ideal-transform, and solver audits |
| `code/tests/` | New finite and native regression tests |
| `code/*.py` | Native export, paired benchmark, profile, figure rebuild, and delivery checks |
| `examples/` | Minimal positive and obstruction examples |
| `results/` | Raw timing, source export, finite audit, profiles, and historical oracle provenance |
| `results/native_packets/` | All-14-refusal audit and five complete source-bound certificates |
| `integration/` | Four separate patches, exact source hashes, and patch order |
| `PROVENANCE.json` | Pinned revision and hashes of the corpus and all five inspected incoming archives |
| `CLAIMS.md` | Claim-to-evidence map and explicit limits |
| `MANIFEST.sha256` | Hash inventory of the packaged files |

## Repository integration

The reviewed baseline is:

```text
c6d0ec8aa0b6308310ab6c081ba29d8bc363ede5
```

No commit, push, or PR is part of this delivery. Apply in a review branch or
worktree at that pin. If the target has advanced, review and adapt the patches
against its changes rather than assuming the internal APIs are unchanged.

Set these paths to your local locations:

```sh
RESEARCH_PACKAGE=/absolute/path/to/unknot_exceptional_rows_20261012
PROVEIT_REPO=/absolute/path/to/ProveIt
```

From the repository root, check the four patches together:

```sh
git apply --check \
  "$RESEARCH_PACKAGE/integration/source-reuse.patch" \
  "$RESEARCH_PACKAGE/integration/orbit-contraction.patch" \
  "$RESEARCH_PACKAGE/integration/lower-forest-portfolio.patch" \
  "$RESEARCH_PACKAGE/integration/exceptional-row-solvers.patch"
```

Apply with the same command after removing `--check` when ready to integrate.
The first two patches preserve the default native outputs. The third adds a
separate optional portfolio and its tests. The fourth adds the finite research
package and its tests; it does not insert a graph/matrix result into the native
recognition schedule. No certificate schema or public verifier trust boundary
is weakened.

`integration/INTEGRATION.json` records 24 resulting source files. All four
patches were checked and applied against exact pinned touched files in a
temporary directory, with byte-for-byte hash comparison against the delivery.
Two docstring-only corrections after the timing run are recorded separately
in `results/delivery_provenance.json`; executable ASTs are unchanged, and the
original benchmark file is preserved untouched.

## Quick standalone reproduction

The finite research package uses Python's standard library. CPython 3.12 was
used for this delivery. From the package root:

```sh
PYTHONPATH=code python -m unittest discover \
  -s code/tests -p test_triple_forest_research.py -v
PYTHONPATH=code python -m triple_forest_research.nonlinear \
  examples/three_row_choice.json --deterministic-width
PYTHONPATH=code python -m triple_forest_research.nonlinear \
  examples/three_row_choice.json --seed 20261012
python code/verify_delivery.py
```

Every success must be replayed with `base_verify.verify(problem, result)`
before a caller relies on it. The audit programs do so. A randomized zero or
resource limit is inconclusive. Most exhaustive deterministic finite negatives
are algorithmic conclusions without an exported portable negative proof.

To rerun the independent mathematical audits without changing the recorded
reports:

```sh
mkdir -p reproduced/independent
python code/independent/independent_exceptional_audit.py \
  --output reproduced/independent/exceptional.json
python code/independent/independent_boolean_sieve_audit.py \
  --output reproduced/independent/boolean.json
python code/independent/independent_ideal_transform_audit.py \
  --output reproduced/independent/ideals.json
python code/independent/review_root_solvers.py \
  --fast code --native results/native_core_sources.json \
  --output reproduced/independent/delivered_solvers.json
python code/audit_forest_solvers.py \
  --fast code --input results/native_core_sources.json \
  --output reproduced/native_forest_solver_audit.json
```

The saved native matrices are data for a finite replay. Fresh source
authentication requires the exporter below.

## Native source and packet reproduction

Use the repository's normal Python dependencies. After applying the patches:

```sh
python "$RESEARCH_PACKAGE/code/export_native_core_sources.py" \
  --repo "$PROVEIT_REPO" --output "$RESEARCH_PACKAGE/reproduced/native_core_sources.json"
python "$RESEARCH_PACKAGE/code/verify_delivery.py" \
  --repo "$PROVEIT_REPO" --output "$RESEARCH_PACKAGE/reproduced/delivery_validation.json"
```

The second command verifies the patch bytes and replays all five saved native
packets using the public whole-cut verifier. It does not modify the repository.

From `Topology/UnknotRecognition/fast` in the patched checkout:

```sh
python -m lower_forest_research.audit \
  --baseline "$RESEARCH_PACKAGE/results/paired_native_benchmark.json" \
  --output "$RESEARCH_PACKAGE/reproduced/native_packets"
python -m unittest tests.test_lower_forest_portfolio
```

The final optional adapter uses two deterministic policies, with at most four
alternative forests across raw and augmented core calls by default. All 14
original refusals are rechecked. The remaining nine refusals comprise two
annular-attachment cases, one raw-core stall in the whole-cut path, and six
historically classified inputs containing non-handlebody components.

The complete 100-test speed regression command and the separate nine-test
portfolio command are in `results/validation/native_validation.json`.

## Timing and figures

The full benchmark reconstructs the exact pinned baseline using `git archive`.
The commit's objects must therefore be locally available; a partial clone may
need Git to fetch missing objects. It uses warmups and five paired repetitions,
so it takes materially longer than the sum of case medians in the article.

```sh
python "$RESEARCH_PACKAGE/code/benchmark_source_contraction.py" \
  --repo "$PROVEIT_REPO" --output "$RESEARCH_PACKAGE/reproduced/native_timings.json" \
  --rounds 5 --ablation
python "$RESEARCH_PACKAGE/code/benchmark_gap_prefix.py" \
  --repo "$PROVEIT_REPO" --output "$RESEARCH_PACKAGE/reproduced/prefix_timings.json"
python "$RESEARCH_PACKAGE/code/profile_native_reproduce.py" \
  --repo "$PROVEIT_REPO" --output "$RESEARCH_PACKAGE/reproduced/profile" --variant baseline
```

The 509× median paired ratio in the synthetic prefix test is **only endpoint
mapping**, not full replay or recognition. The full native speedup is 1.3068×.
The corpus has raw dual rank at most one, and all optimized raw positives are
found by the deterministic candidate before the determinant sieve. Those
limitations are stated in the article.

Rebuild figures and article from the package root:

```sh
python code/plot_results.py
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error exceptional_rows_and_certificate_replay.tex
```

Use the archived figures if NumPy or Matplotlib is unavailable. Standard
LaTeX packages suffice to compile the source. The final PDF was rendered and
visually inspected, with no undefined references, compilation warnings, or
overfull boxes.

## Most useful next research step

Continue the source-authenticated annular attachments for the index-eight and
index-ten Fibonacci examples. In parallel, investigate whether geometric
simplification controls implication width across a complete hierarchy. These
are the concrete points connecting the new native coverage and deterministic
local complexity theorem to the announced quasi-polynomial goal.
