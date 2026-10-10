# Causal Localization and Shared Region Search for Bounded Pachner Simplification

Research continuation for Vladimir Reshetnikov's ProveIt project, 9 October 2026.

The complete article is `article/article.pdf`; its master source is
`article/article.tex`. This package proves and implements a complete
fixed-parameter **bounded simplification** primitive, develops a stronger
multiunit theorem, and states the precise additional structural theorem
needed for the project's quasi-polynomial recognition route.

## Main results

For generalized face-pairing triangulations with the specified formal
relative-boundary 2–3 and 3–2 replacements:

1. If any descending trace uses at most `U` **total** upward moves, a
   connected first-descent witness exists with `u <= U`, `d = u+1`,
   length `2u+1`, and at most `3u+3` consumed original tetrahedra.
2. Complete bounded-upward descent is decidable in
   `2^{O(U)} poly(t+B)` bit time. No supplied spatial locality hypothesis
   is needed for this objective. The six-tetrahedron ball makes the
   footprint bound sharp at `U=1`.
3. Reducing by at least `k` tetrahedra under one joint upward budget is
   decidable deterministically in `2^{O(U+k)} poly(t+B)` time. The proof
   combines the new localization/composition lemmas with standard perfect
   hash families and color coding.
4. Exact shared-cover search eliminates independent restarts on overlapping
   allowed regions. Genuine upward-required solid-torus controls show
   **12.69–59.85×** median speed ratios for complete family exhaustion and
   **39.50–83.29×** for first verified descent, with all raw paired timings
   retained. These are bounded simplifier measurements, not end-to-end
   knot-recognition results.

The budget is total upward events, not maximum excess tetrahedra. A complete
bounded negative result is not a nontrivial-knot certificate. The article's
conditional closure theorem explains exactly what additional topological
structure would turn this primitive into a complete quasi-polynomial
recognizer.

Generic endpoint callbacks must respect marked-endpoint and commutation
equivalence for complete predicate conclusions. Tests that depend on an
arbitrary certificate history or witness-cover choice are outside that
guarantee. The built-in descent and supplied-vector disc predicates respect it.

A custom endpoint predicate must be invariant under marked endpoint
equivalence and commuting reorderings for a complete negative predicate
conclusion. A history-sensitive callback or a predicate on the arbitrarily
selected cover does not generally satisfy this contract. The built-in
descent and supplied-vector disc predicates do.

## Implemented and proved components

| Component | Location | Status |
|---|---|---|
| Shared exact cover search and default-radius descent | `repro/fast/fastunknot/pachner_cover_search.py` | Implemented, independent positives, cap-safe outcomes |
| Source-bound cover/descent verifier | `repro/fast/fastunknot/pachner_cover_verify.py` | Independent of search and move/transport producers |
| Birth analysis, connected extraction, disjoint composition | `repro/fast/fastunknot/pachner_causality.py` | Implemented, declared frames retained, final replay required |
| Colorful item packing | `repro/fast/causal_research/colorful_packing.py` | Exact for one supplied coloring |
| Complete deterministic splitter generation | Article §9 | Theorem uses the cited construction; full generator not implemented here |
| General recognition consequence | Article §13 | Conditional on an explicit global structural and terminal hypothesis |

The article contains full proofs, bit accounting, a category counterexample,
implementation contracts, numerical tables, and twelve research questions.
Its mathematical arguments are written proofs with independent reasoning
and code audits; no Lean formalization or external peer review is claimed.

## Reproduction

Python **3.12.14** was used. Optional external reproduction packages and
their recorded versions are in `repro/requirements.txt`; the new runtime
search and certificate modules use the standard library and maintained
native code. Regina engine 7.4 (Python distribution 7.4.1) supplies independent
topological controls. A TeX Live installation with `latexmk` builds the paper.

From the package root:

```bash
python scripts/verify_package.py --strict
bash article/build.sh
python scripts/run_regression.py --output-dir reproduced/regression
python scripts/plot_benchmarks.py --output reproduced/benchmarks.pdf
python scripts/audit_fixtures.py --output reproduced/fixture_controls.json
```

The regression runner requires a fresh output directory and runs the full
test inventory in six fresh interpreters with both inherited helper import
conventions configured explicitly. The recorded final evidence covers
**1,483 distinct tests in 187 modules**, all passing, with no failures,
errors, or skips. An initial runner import-path failure and a later incoming
test compatibility issue are retained in provenance; the affected 315-test
batch was rerun after the narrow test adaptation. Native production bytes
remain unchanged.

From `repro/fast`:

```bash
python -m unittest tests.test_pachner_cover_search \
  tests.test_pachner_causality tests.test_pachner_composition \
  tests.test_colorful_packing -v

python -m shared_cover_research.benchmark \
  --replay shared_cover_research/results/exhaustion.json
python -m shared_cover_research.benchmark \
  --replay shared_cover_research/results/descent.json

python -m shared_cover_research.benchmark --sizes 1,2 --repeats 3 \
  --output reproduced/exhaustion.json
python -m shared_cover_research.benchmark --descent-only \
  --sizes 1,2,4,8 --repeats 3 --output reproduced/descent.json

python -m causal_research.composition_audit \
  --replay causal_research/results/disjoint_composition.json \
  --output reproduced/composition_replay.json
python -m causal_research.frame_audit --output reproduced/frame_audit.json
python -m causal_research.composition_frame_audit \
  --output reproduced/composition_frame_audit.json
python -m causal_research.six_tetra_ball > reproduced/six_tetra_ball.json
```

The small ball driver has no external input and prints its complete inventory
as JSON. The other audit drivers accept output paths; use `reproduced/`
paths to retain the original evidence. Their `--help` options describe
additional fixture-selection controls.

## Evidence map

| Evidence | Path |
|---|---|
| Paired benchmark samples, endpoint proofs and source digests | `repro/fast/shared_cover_research/results/` |
| Independent validity, solid-torus recognition, and move inventories for all four timed source sizes | `provenance/fixture_controls.json` |
| Complete six-tetrahedron ball inventory | `provenance/six_tetra_ball_inventory.json` |
| Derived exact table | `repro/fast/shared_cover_research/results/summary.json` |
| All 144 extraction-frame variants | `repro/fast/causal_research/results/frame_audit.json` |
| Twelve focused composition-frame interactions | `repro/fast/causal_research/results/composition_frame_audit.json` |
| Genuine colorful packing, exact subset oracle | `repro/fast/causal_research/results/colorful_packing.json` |
| Two disjoint source proofs and their composed 13→11 proof | `repro/fast/causal_research/results/disjoint_composition.json` |
| Independent composition replay | `repro/fast/causal_research/results/disjoint_composition_replay.json` |
| Final full-suite aggregate, every test ID and current hashes | `provenance/full_tests.json` |
| Narrow incoming-test compatibility change | `provenance/normal_ray_blocks_compatibility.patch` and `.md` |
| Isolated additive-integration checks | `provenance/integration_audit.json` |
| File origin and exact integration actions | `integration_manifest.json` |

## Integration

The source baseline is ProveIt revision
`8188525b70033dcfe7c51ea5ae2c8723ad0c0198`. The current native tree is
preserved. Earlier incoming dependencies absent from it are supplied, and
one of their tests is adapted to the current native optimization without
weakening its original fallback-budget coverage.

`repro/` is a self-contained reproduction snapshot. **Use the additive
integrator rather than copying that snapshot over the repository.** Read
`INTEGRATION.md`, then run:

```bash
python scripts/integrate.py --repo /path/to/ProveIt
python scripts/integrate.py --repo /path/to/ProveIt --apply
```

The first command is a dry run. The script validates prerequisites and all
destinations before writing, refuses differing existing files, and only
adds absent files or accepts byte-identical ones. It creates no commit and
performs no remote operation. The repository license is preserved in
`LICENSE-ProveIt.txt`.

The article PDF and the entire archive can also be placed in `docs/incoming`
for review before integrating the additive runtime files.
