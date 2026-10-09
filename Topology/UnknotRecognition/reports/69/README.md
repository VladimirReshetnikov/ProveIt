# Support-sensitive certificates for unknot recognition

Research continuation for Vladimir Reshetnikov's ProveIt project, 9 October 2026.

**Main result:** a checked unit-pivot ray path substantially improves essential-disc counting on the dense layered Fibonacci family. The general support-coordinate compiler has useful optimality and representation theorems, but the retained benchmarks show regressions on important cases, so it remains an explicit optional interface. This package does **not** prove quasi-polynomial complexity for unrestricted unknot recognition.

## Read first

- `article/article.pdf`: the 27-page mathematical article, with proofs, measured positive and negative results, certificate contracts, and 15 proposed research topics.
- `article/article.tex` and companion TeX files: complete editable article sources. Bibliography entries are included; no external bibliography service is required.
- `INTEGRATION.md`: exact patch and test workflow.
- `PROVENANCE.json`: the pinned source revision, original Git blob hashes, delivered-file hashes, incoming archive provenance, and independent primary references.
- `SHA256SUMS`: integrity manifest for the complete unpacked package.

The baseline is ProveIt commit `3a90fb34146c915328ab8eac6250cc2514f74ed0`. The additive implementation is under `repo_overlay/Topology/UnknotRecognition/fast/`. The compact `reference_snapshot/fast/` contains unchanged maintained source and fixtures needed for reproduction, with historical result archives and unrelated large artifacts omitted. It is a source subset, not a complete repository checkout.

## Mathematical contributions

For the positive support of a supplied normal vector, let `d` be the rational nullity of its supported matching equations, and let `a` count supported vertex-link types.

1. An exact decoder from `d` retained coordinates, with independently checked kernel identities and a modular nonsingular-minor witness.
2. A minimum allocated binary-slot projection by maximum-weight column-basis selection; safe reuse under uniform scaling stays within `d` bits of a newly optimized projection.
3. Scalar packing whose fibre invariant preserves the canonical weight runs of the same selected vector observer.
4. The full component-type bound `H <= 2d - a`, improved to `H <= d` for two-sided components.
5. A conservative geometric support partition and complete rank-one essential-disc count, with correct treatment of one-sided multiples.
6. A unit-pivot transcript proving both a one-dimensional rational kernel and the primitive integer lattice. It reconstructs the primitive generator with additions, without gcd or division on the successful branch.
7. An all-size theorem for the Fibonacci meridian family: exactly `3t - 1` discovery steps, direct Euler/boundary verification, and arbitrary binary multiplicity.

The article credits the classical AHT component algorithm, the HLP primitive vertex-surface principle, Edmonds's matroid theorem, and earlier maintained/incoming ProveIt results. It distinguishes an established compressed-cutting theorem from the executable source-bound integration still to be built.

## Recorded evidence

- 146 focused new/affected regression tests passed, including all optional Regina checks in the recorded run.
- 2,980 normal sources across 48 triangulations agreed with the maintained implementation and Regina 7.4 on full component vectors and essential-disc counts.
- 8,940 independent new-certificate replays accepted; 27 deliberately corrupted profile proofs rejected.
- An additional exact rational audit checked 40 systems and 420 eligible bases; unit tests include 100 further randomized exhaustive basis comparisons.
- 27 completed benchmark cohorts, 652 successful calls, 538 measured calls, 114 retained warm-ups, no timeouts, and unchanged source hashes.
- Offline replay accepted all 57 distinct retained benchmark certificates and 20 additional sample certificates, without invoking producers, basis compilation, surface search, or fixture generation.
- A fresh assembly through the delivered reproducer passed all 146 tests and the same 77-certificate replay. The additive patch applied cleanly, reproduced all 105 overlay files exactly, and left all 566 supplied baseline files unchanged.

At 256 tetrahedra the checked disc query has separate median times **1,351.121 ms old** and **72.965 ms new**, with **18.704x median within-round speedup**. Its certificate shrinks from **7,098,789 to 15,368 bytes**. Generation includes the new producer's internal replay, and each arm also receives an external replay.

The same family's complete coordinate census regresses: **1,335.527 ms old** versus **1,707.417 ms packed**, paired ratio **0.782**. Small mixed/link controls also expose ray-interface overhead. Fixed-basis scalar transport has no robust timing advantage in the retained controls. Both favourable and unfavourable results are in the paper and raw records.

## Reproduce

Python **3.10 or newer** is required, matching the maintained package's declared minimum; the recorded run used Python 3.12.14. Its standard library suffices for the new production code, algebra audit, benchmarks, and focused tests without optional geometric oracles. Regina is a separately installed optional dependency; version 7.4 produced the recorded geometric comparison. Matplotlib is needed only for plots.

From the unpacked package root:

```bash
python3 reproduce.py --task tests
python3 reproduce.py --task algebra
python3 reproduce.py --task example
python3 reproduce.py --task audit --regina
python3 reproduce.py --task benchmark
python3 reproduce.py --task replay
```

Each command assembles a fresh working source directory from the verified reference snapshot and overlay, then runs there. It prints that directory for inspection. Use `--work-dir /absolute/new/directory` to choose it. If Regina is installed outside the interpreter's normal path, add `--regina-path /absolute/dependency/directory`.

The recorded results are under `repo_overlay/Topology/UnknotRecognition/fast/support_research/results/`. The benchmark retains raw nanosecond measurements, A/A controls, paired summaries, compact input records, and deduplicated gzip-compressed exact certificates. Time-limit callback overhead is included in all measured arms. The 512-tetrahedron point is a predeclared new-ray-only capacity measurement.

To rebuild the article:

```bash
cd article
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

To regenerate the exact tables and plots from retained data:

```bash
python3 repo_overlay/Topology/UnknotRecognition/fast/support_research/render_results.py --article-dir article
```

## Scope and integration

The new production code consists of nine modules and five new test files. No existing default or production file is modified. `integration.patch` and `repo_overlay/` encode the same additions. The source-bound wrapper can issue a checked positive unknot certificate for a supplied surface in the canonical exterior; it does not perform complete surface discovery. Zero essential discs in one source remains inconclusive about the knot.

The code and article are prepared with ChatGPT and independently reviewed through separately implemented checks and mathematical review. They are not proof-assistant formalizations or peer-reviewed claims of a general quasi-polynomial recognizer.
