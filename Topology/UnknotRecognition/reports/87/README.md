# Certified reductions for unknot recognition

Research continuation for `VladimirReshetnikov/ProveIt`, 12 October 2026.

The full article is **`article/article.pdf`**. Its editable source is
`article/article.tex`, with five included theory/experiment files and generated
tables. The article contains the definitions, detailed proofs, implementation
contracts, positive and negative experimental findings, and twelve further
research problems.

## What this package adds

1. A complete primal–dual support certificate for a nonnegative rational
   matching cone, verified exactly before ray enumeration. The source version
   uses an actual normal vector and multipliers on original face-matching rows.
   A proved alternative direct formulation gives an `O(t^2)`-bit source
   certificate without triangle elimination; the benchmarked producer still
   uses the quadrilateral quotient.
2. Proofs of support reuse, dual activation, a quotient extension theorem,
   sparse bounded-row obstruction families, intrinsic-dimension conflict
   branching, and a conditional global search-budget theorem.
3. Compressed recovery of signed cyclic port words, zero-gap incidence and
   relative fibre gauges; independently checked disc-product templates with at
   most `9q` tetrahedra for `q` attached disc ports.
4. A separate theoretical extraction using `O(q log(q+1))` ordinary AHT
   orbit-count calls when the source component partition is supplied.
5. New opt-in Python interfaces, independent verifiers, tests, a geometric
   fixture, source audits and paired timing scripts.

The general quasi-polynomial recognition theorem remains open for this code.
The article gives explicit sufficient bounds and identifies the missing
geometric coverage, hierarchy, pattern-transport and dimension-growth results.
The delivered LP backends do not carry a polynomial worst-case guarantee;
accepted certificates are exact regardless of the proposal backend.

## Main measured results

- **59 focused regression tests pass**, including 24 new tests.
- On 188 maintained higher-dimensional sectors, maximal support agrees with
  the archived complete standard vertices. There are 24 raw/effective dimension
  reductions, but the incumbent two-row rules already find the same zeros.
- A genuine 36-tetrahedron fixture has one additional zero missed by one fixed
  row pass. Iterated rebuilding and two-row closure finds it too; both final
  dimensions are five. The new complete supplied-sector route nevertheless
  reduces median time from **0.890 s to 0.538 s**, and from **0.876 s to 0.513 s**
  with a common prepared source. Both routes examine the same 1,835 bases and
  emit the same 31 combined Q/standard rays. Five small cases incur overhead.
- A subsequent bounded search covers 4,864 sectors in 38 sources and finds no
  extra zero beyond iterated rebuilding and pair closure. This is finite
  negative evidence, not a completeness theorem.
- The geometric audit checks 129 finite and eight binary cases, 329 disc
  templates, and 3,067 exact port subdivision charts. All 21 distinct emitted
  complexes pass Regina's actual ball-recognition check.
- In the largest paired geometric benchmark, compressed port recovery takes
  **65.84 ms**, versus **885.90 ms** for literal traversal, with a median paired
  literal/compressed ratio of **13.455**. The returned common data are
  byte-identical. Small cases favor direct traversal.

These are supplied-sector and supplied-surface results. They are not timings
for complete recognition from arbitrary knot diagrams. Consult the article
for the exact timing boundaries, controls and limitations.

## Repository checkpoint and integration

The inspected checkout is:

```text
90e16db798c8d976bbe0c062e07cf20565e0b63a
```

Its relevant trees agree with the topology update:

```text
e7b51c4708baefbc5836ef233301a7de3552f86b
fast tree:      8c4dc4593997772b6da3cadb36ebbafd6f9574b3
synthesis tree: 4802840aa6be0867f317b5e5d1edaf55ed9d64ce
```

`code_overlay/` contains only additions, with paths relative to the repository
root. `implementation.patch` adds the same files. No maintained default
recognition behavior is modified. Review/apply the patch from a compatible
ProveIt checkout:

```bash
git apply --check /absolute/path/to/implementation.patch
git apply /absolute/path/to/implementation.patch
```

Alternatively copy the `code_overlay/Topology/` subtree into the repository.
Do not both apply the patch and copy its files. On a later checkout, inspect
interface changes and rerun the focused verification before integration.

The article is standalone so it can be integrated into the repository's
preferred research/report location without editing the maintained synthesis
report. Keep all its `.tex` files and the `tables/` directory together.

## Compile the article

No network or Python dependency is needed to compile the supplied TeX:

```bash
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The source uses standard TeX Live packages: Latin Modern, AMS mathematics,
microtype, geometry, TikZ, booktabs, longtable, tabularx, enumitem, fancyhdr,
xurl and hyperref. The bibliography is embedded in `article.tex`.

The tables are already included. To regenerate them from the archived JSON:

```bash
python3 tools/build_evidence_tables.py
```

This also regenerates the compact CSV tables and `evidence/summary.json`.

## Reproduce code verification

Use Python 3.12 in a compatible checkout. The exact environment used is
recorded in `environment.txt`. `requirements-research.txt` pins the optional
solver and audit packages used for this research; these are not new mandatory
imports for existing default production paths.

```bash
python3 -m pip install -r /absolute/path/to/requirements-research.txt
cd Topology/UnknotRecognition/fast
PYTHONPATH=.:tests python3 -m unittest \
  tests.test_sector_maximal_support \
  tests.test_matching_support \
  tests.test_sector_support \
  tests.test_sector_sparse \
  tests.test_normal_sector_integration \
  tests.test_parallelity_port_words \
  tests.test_parallelity -q
```

This runs the 59 tests in the saved final regression command. The repository's
existing fixtures must be present, particularly `reports/57/results/`,
`synthesis/data/` and `fast/tests/`. A sparse checkout must include the files
recorded in `provenance.json`; the patch is an overlay, not a replacement for
the underlying package.

## Reproduce the experiments

Run these commands from `Topology/UnknotRecognition/fast/`, one at a time.
Use an otherwise idle machine for comparisons. All output paths below are
examples for a new run; preserve the delivered evidence if comparing results.

```bash
python3 maximal_support_research.py \
  --output /tmp/maximal_support_results.json --repeats 3

python3 maximal_support_geometric_search.py \
  --output /tmp/maximal_support_geometric_search.json \
  --seconds 180 --sectors 128 --minimum-dimension 4

python3 maximal_support_geometric_search.py \
  --output /tmp/maximal_support_geometric_iterated.json \
  --seconds 150 --sectors 128 --minimum-dimension 4 --iterate-incumbent

python3 maximal_support_benchmark.py \
  --output /tmp/maximal_support_final_benchmark.json --repeats 9

python3 parallelity_port_research.py \
  --output /tmp/parallelity-port-audit-final.json --benchmark-rounds 7
```

The bounded geometric search has a wall-clock limit as well as a fixed seeded
schedule. On another machine it may stop at a different prefix. The preserved
36-tetrahedron fixture and all recorded sources permit exact reproduction
without depending on finding that example again within the same deadline.

## Evidence and artifact map

| Path | Contents |
|---|---|
| `article/` | PDF, complete editable TeX and generated tables |
| `code_overlay/` | New Python modules, independent checkers, tests, fixture and research scripts |
| `implementation.patch` | The code additions in reviewable patch form |
| `evidence/maximal_support_results.json` | Abstract cases, 188-sector audit and explicitly preliminary three-repeat timings |
| `evidence/maximal_support_geometric_search.json` | First bounded search, actual source pairings and fixed-pass counterexample |
| `evidence/maximal_support_geometric_iterated.json` | The 4,864-sector search against iterated rebuilding and pair closure |
| `evidence/maximal_support_final_benchmark.json` | Nine paired trials per support case/scope and identical-code controls |
| `evidence/parallelity-port-audit-final.json` | Finite/binary audit, 86 full source certificates, template validation and seven-pair geometric timings |
| `evidence/*.csv` | Compact tables for further analysis |
| `evidence/pilots/` | The preliminary single-query geometric support pilot, not used as the final timing result |
| `validation/` | Focused regression output, patch validation, TeX compile and visual QA records |
| `provenance.json` | Baseline identities, input/source hashes and package file inventory |
| `SHA256SUMS` | Checksums of deliverables inside this directory |

## New APIs

From `fast/` after applying the overlay:

```python
from fastunknot.sector_maximal_support import (
    certify_nonnegative_kernel_support,
    certify_maximal_support,
    discover_in_maximal_support_sector,
)
from fastunknot.sector_maximal_support_verify import (
    verify_nonnegative_kernel_support_certificate,
    verify_maximal_support_certificate,
)
from fastunknot.parallelity_port_words import normal_parallelity_port_words
from fastunknot.parallelity_port_words_verify import verify_parallelity_port_words

result = certify_nonnegative_kernel_support([[1, 1, 0]])
assert result['status'] == 'COMPLETE'
assert result['retained_indices'] == [2]
assert verify_nonnegative_kernel_support_certificate(
    [[1, 1, 0]], result['certificate'])

# `triangulation`, `allowed_types` and `normal_coordinates` use existing
# source formats. The current source validator requires a finite connected
# orientable compact manifold with exactly one torus boundary.
answer = discover_in_maximal_support_sector(
    triangulation, allowed_types, max_bases=1000)

ports = normal_parallelity_port_words(
    triangulation, normal_coordinates,
    record_certificate=True, max_cycles=100000)
if ports['status'] == 'COMPLETE':
    assert verify_parallelity_port_words(
        triangulation, normal_coordinates, ports['certificate'])
```

An exhausted allowance is inconclusive. A support certificate proves no
essential-disc or unknot verdict by itself. A disc-product template is a
replacement with recorded attachments, not a deletion. Arbitrary inherited
boundary patterns and non-disc bases require the additional interfaces
identified in the article.
