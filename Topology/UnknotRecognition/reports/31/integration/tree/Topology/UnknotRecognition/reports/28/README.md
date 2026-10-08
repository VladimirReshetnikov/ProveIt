# Classical-Closure Rigidity and Single-Survivor Resets

A research contribution for `ProveIt/Topology/UnknotRecognition`.

**Article:** `article/article.pdf` (19 pages) and `article/article.tex`.

## Results

For a whole complex on one nonempty matching whose actual remaining closure is a knot, write its dot-polynomial differential as `Q = A + sum_i x_i B_i + higher terms` and put `B = sum_i B_i`. Its completed total unreduced F2 Khovanov rank is

`(dim H(V,A) - rank B_*) * rank Kh(K; F2)`.

Only the scalar and total-linear terms determine this observation. The proof uses an explicit matrix-valued basepoint-sliding conjugation, not just a homology-level identification of dot operators. In the radical case `A=0`, the multiplier is `N - sum_h rank B_h`; no barcode or ranks of matrix products are needed.

Pure blocks have stronger all-classical-closure tests: odd linear parity permits exact total-rank compression to matching copies, while any nonzero even-parity pure differential forces completed rank at least four. An inconclusive all-pure checkpoint therefore has one matching survivor. The first-jet theorem permits additional nonpure checkpoints when their actual matching completion is a knot.

Splicing a lone survivor into the remaining PD diagram and restarting gives a proved bit bound `n^O(1) 2^O(g)`, where **g is the actual maximum number of crossings processed between resets or the final decision for a specified order policy**. Polylogarithmic gaps give quasi-polynomial complexity. No universal polylogarithmic-gap theorem is proved, and the unrestricted worst-case bound remains exponential.

## Run

Python 3.10 or newer; standard library only for computation. A LaTeX installation is needed only to rebuild the PDF.

```sh
export PYTHONPATH="$PWD/src:$PWD/reference_upstream"
python -m unittest discover -s tests -v
python experiments/audit.py
python experiments/benchmark.py
python -m closure_reset examples/figure_eight.json --check-d2
sh article/build.sh
```

`sh reproduce.sh` runs all these validation/build stages and replays the examples. The test/benchmark JSON is reproducible structurally; wall times and build timestamps are environment-dependent.

Inputs are `{"pd": [[...], ...]}` or supported `{"strands": 3, "word": [1,-2,1,-2]}` braid presentations. The original diagram must be a validated classical knot. Empty PD means the unknot. The braid converter rejects untouched strands that would introduce unencoded circles.

Verdicts are `UNKNOT`, `NONTRIVIAL`, or `UNKNOWN` on resource exhaustion. The API returns capped rank, not exact homology after resets. It does not output a knot isotopy or preserve quantum/homological degree profiles. CLI exit codes are 0 for a completed verdict, 2 for invalid input, and 3 for `UNKNOWN`.

## Validation actually completed

- **29 unit tests**, including exhaustive/sampled dot-polynomial identities, local saddle and matrix gauge identities, pure and mixed polynomial matrices, scalar-unit first-jet formulas, invalid input, attachment safety, limits, and corrupted replay evidence.
- **160 independent-cube audit diagrams**, with 480 driver comparisons, 480 additional interval-rank checks, and 130 additional quiver-rank checks. All passed. The reset arm reset on 80 diagrams and returned 2 early nontrivial verdicts.
- Eight paired raw-backend benchmark cases, nine randomized-order rounds each. The results include gains and overhead. The greatest measured full/reset ratio in this table is about **2.24**, on a selected trefoil-plus-curls input, not a new recognition family.

**No nonsingleton pure or first-jet block was observed in the diagram audit or benchmark corpus.** The new polynomial-matrix compression is validated by exact algebraic fixtures and the proofs, not a claimed occurrence in those diagrams. Existing Euler/structural methods may already handle the benchmark gains.

## Integration and provenance

This is an additive research package, not a patch already applied to the user's repository. The driver imports `fastunknot.scan_fast.FastScan` and can use a local ProveIt checkout. See `integration/INTEGRATION.md`.

The bundled `reference_upstream` directory is a **retained source-derived scanner fixture**, not a full checkout. Comments/docstrings were shortened in the earlier bundle; its geometry import surface is intentionally minimal. No normalized-AST comparison against the actual checkout was executed here, and the production test suite was not run. The independent cube imports no scanner code. The exact scope is recorded in `provenance/` and `CLAIMS.md`.

The local saddle identities and vertical differential are established Khovanov tools. The article credits the literature, including the 2026 basepoint paper, and claims the explicit rank/compression application and strengthened reset bound relative to the inspected repository. It does not establish global priority for every corollary.
