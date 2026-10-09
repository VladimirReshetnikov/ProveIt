# Beyond the Minimum-Span Face

Defect-stratified Euler optimization, small residual components, and a two-flow connected-surface selector. Research continuation for ProveIt, 9 October 2026.

The self-contained 22-page article is `article/article.pdf`; its compilable source is `article/article.tex`. The repository revision inspected was `8188525b70033dcfe7c51ea5ae2c8723ad0c0198`.

## Results

For a coherent height model with T tetrahedra, a verified minimum span D*, and nonnegative Euler edge weights, the radius-k band is covered exactly by

    H(T,k) = sum_j binom(2T,j) * 3^j * binom(k,j)

constant-span difference-constraint systems. Exact integral Euler optimization in each gives a complete band profile in H(T,k) times a bit-polynomial factor. With polynomial-size input and k = O(log n), this is n^{O(log n)}.

In a primitive coherent surface of a knot exterior, all components except any chosen positive primitive core have at most D-D* normal pieces altogether. If q negative primitive components occur, 2qD* <= D-D*. A fixed nine-tetrahedron solid torus realizes equality for every q.

Two polynomial network solves minimize the Euler edge penalty F, then minimize span over the entire F-optimal face. Under authenticated primitive knot-exterior hypotheses, the output is connected. The sufficient threshold F* <= 2D* produces a disc or cappable annulus; any coherent disc with at most D*+1 pieces guarantees success.

The anchor identity, Euler cell formula, and bounded-flow solver construction build on existing ProveIt work and are credited in the article and source. No claim of priority over all unpublished incoming archives is made.

## Boundaries

This is not a complete quasi-polynomial unknot recognizer. No universal logarithmic span-excess theorem or completeness of the coherent disc family is proved. A maximal aggregate Euler characteristic does not in general solve disc existence. Every arithmetic API and CLI leaves the knot verdict null. A failed sufficient test or exhausted work budget must not become a KNOTTED result.

The native adapter is opt-in and **NOT_RUN** against a repository checkout in this delivery. Its private source interfaces were inspected. No production dispatch, default allowance, existing certificate format, or fallback is modified. Incoming ZIP listings were inspected, but the latest binary archives were not unpacked.

## Reproduce

Python 3.10 or later is required; the executed environment used Python 3.13.5. No Python third-party package is required. From the package root:

```sh
PYTHONPATH=src python -m unittest discover -s tests -v
python scripts/audit.py
python scripts/benchmark.py
python scripts/check_examples.py
./build.sh
```

`build.sh` generates the self-contained TeX from the saved benchmark JSON and compiles it three times. A TeX installation with the listed standard packages is required. The retained article template is `article/article.tex.in`; all generated numerical tables derive from recorded benchmark medians.

Replay an existing complete certificate without running an optimizer:

```sh
PYTHONPATH=src python -m span_excess examples/solid_torus_band.json --verify
```

Run the polynomial two-network selector on the same saved model:

```sh
PYTHONPATH=src python -m span_excess examples/solid_torus_band.json \
  --lex --output lex-result.json
PYTHONPATH=src python -m span_excess lex-result.json --verify
```

A default CLI work cap limits research search; change `--max-work` explicitly. Exhaustion returns INCONCLUSIVE. Large integer witnesses use a signed hexadecimal JSON encoding when needed.

## Recorded validation

There are 66 passing unit test methods. Independent audits compare 600 signed-flow models against 418,908 boxed potentials; compare 80 complete bands against 51,824 potentials; check 6,000 stratum memberships; and replay 3,725 arithmetic stratum records. The geometric audit constructs 100 solid tori by 800 legal simplicial moves, glues 1,200 normal surfaces literally, and checks 1,360 positive-core piece budgets. Eight complete geometric radius-one searches replay 1,544 additional cells.

All 100 geometric lexicographic outputs are connected and primitive. **Both the old minimum-face objective and the new selector yield Euler characteristic one on every constructed mesh:** these tests show no added recognition coverage. The paired timing study uses a separate abstract height family, not a native knot corpus. Small instances are slower with stratification; larger numerical boxes favor it. Binary-size stress keeps 79 strata and the same instrumented combinatorial work through heights of 2^16384. Raw samples, not only summary ratios, are included.

## Integration

Read `docs/INTEGRATION.md` before using `integration/native_adapter.py`. Read `docs/SOURCE_AUDIT.md` for the exact review scope and `docs/CLAIMS.json` for the theorem and execution ledger. The tests and constructed-source histories should be retained during intake. A report number is intentionally not preassigned.

This work has human-readable proofs and finite computational support. It has not been externally peer-reviewed or proof-assistant verified.
