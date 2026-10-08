# Modular boundary responses for unknot recognition

**A ProveIt research continuation and optional backend, 8 October 2026.**

This package adds a finite-field implementation of the existing marked-continuation Euler observer. It prepares a checked suffix boundary response once and reuses it across completed boundary matchings. The article proves the integer meaning of the modular observations, handles singular interior matrices, and gives a deterministic criterion for recovering the existing integer observer's threshold decision.

The improvement is substantial on repeated-query workloads with large suffix interiors. Complete raw recognition scans on the seven recorded examples are slower. The new `shadow-modular` backend is therefore optional; the default remains `standard`. A general quasi-polynomial complexity bound for the maintained recognizer remains an open obligation.

Start with the [article PDF](article/unknot_modular_boundary.pdf), its [LaTeX source](article/unknot_modular_boundary.tex), and the [claim and evidence ledger](CLAIMS.md). The article contains the proofs, detailed measurements, source audit, and twelve proposed research questions.

## What the continuation contributes

The implementation extends the repository's marked four-residue obstruction and earlier rational boundary-response prototype. Its principal results are:

- **An exact interface count.** A checked suffix with `b > 0` frontier darts has `b/2` black open face fragments. Each potentially nonzero residual determinant has dimension at most `b - 2`.
- **Sound modular observation.** Residues are aggregated across a whole differential component before taking a norm. Chinese remaindering and the exact component Euler sum give a deterministic lower bound on reduced Khovanov rank. The Khovanov complex remains over **F₂**; auxiliary odd primes compute residues of integer Euler data.
- **Threshold completion without full reconstruction.** If each component coordinate is bounded by `C_a`, a modulus greater than every `C_a` suffices to decide whether the existing integer bound exceeds one. A supplied finite prime palette may be insufficient, and the output records that distinction.
- **A reviewable implementation.** The package includes public dispatch, resource-aware fallback, replay of positive raw observations using the old integer evaluator, independent finite arithmetic checks, actual-diagram audits, and complete timing samples.

The exact-sum enhancement sharpens the completion criterion. After the existing exact Euler prefilter has failed to reject, it does **not** add threshold-one rejections beyond those already exposed by balanced modular residues. The article proves this limitation as well.

## Performance evidence at a glance

The following ratios are medians of five **within-round** old/new time ratios. Values above one favor the modular evaluator. Every arithmetic sample includes fresh geometry and response setup.

| Interior vertices | Actual matching queries | Direct integer / modular | Earlier rational / modular |
| ---: | ---: | ---: | ---: |
| 0 | 200 | 0.670 | 0.608 |
| 3 | 200 | 1.878 | 0.573 |
| 15 | 200 | 6.499 | 1.016 |
| 47 | 200 | 26.666 | 3.968 |
| 127 | 50 | 10.743 | 10.218 |

The last row uses the first 50 of 200 available matchings. A 200-query pilot exceeded the direct evaluator's allowance; its censored times are preserved but do not supply a speed ratio. All timed modular interiors have nullity zero. Separate correctness audits exercise singular cases.

The broader comparison gives essential context:

- Every raw-scan median favors the existing direct observer; direct/modular ratios range from **0.536 to 0.987**.
- Public recognition with its preceding filters deliberately disabled also favors the direct observer on all seven examples, with ratios **0.515 to 0.969**.
- With normal filters enabled, all seven examples are decided before either shadow observer runs. Those timings measure the front end, not a benefit of the new backend.

These results support optional boundary reuse and a subsequent scheduling study. They provide no measured whole-recognizer acceleration on this corpus. See the [recorded benchmark](reproducibility/ProveIt/Topology/UnknotRecognition/fast/results/modular_benchmarks.json) and article Section 7 for the inputs, controls, absolute times, and limitations.

## Package contents

| Path | Purpose |
| --- | --- |
| `article/` | PDF, complete LaTeX sources, references, generated tables and figures, and the asset-generation script. |
| `patches/modular_boundary.patch` | Integration patch for the pinned upstream source: new production modules, dispatch changes, tests, research drivers, and backend documentation. |
| `reproducibility/ProveIt/Topology/UnknotRecognition/fast/` | Source snapshot with the additions, examples, research drivers, and recorded JSON results. |
| `reproducibility/ProveIt/Topology/UnknotRecognition/reports/` | Selected archived reference code needed by the audits and predecessor comparison: report 24's one-file reference, report 26's `detshadow`, and report 28's `closure_reset`. Preserve this sibling layout. |
| `verification/` | Test logs, independent arithmetic script and result, and the inherited normal-surface worker issue record. |
| `provenance.json` | Upstream revision, local snapshot identity, and artifact provenance. |
| `MANIFEST.sha256` | File integrity manifest for the supplied package. |
| `CLAIMS.md` | Precise mathematical, implementation, experimental, and literature claim boundaries. |

The source snapshot is a runnable subset of ProveIt, with the relevant reference dependencies. It is not a complete copy of the upstream repository.

## Source identity and integration

The upstream integration target is:

```text
8a95834940cf77cdab1b39571ffc102ca8b6bede
```

The benchmark's `revision` field records the local materialized snapshot:

```text
3179d245a6752749c09d4fe79c018c79d2209c2d
```

These are different Git identities. The local identifier must not be substituted for the upstream base when describing or applying the patch. Recorded per-file hashes identify the actual timed code; every recorded source file was unchanged during that run. The subsequently added replay verifier is outside that timed observer path. The manifest and provenance record cover the delivered files.

### Review the patch in an upstream checkout

From an existing ProveIt checkout containing the pinned upstream commit, set the package's absolute path and create an isolated review checkout:

```bash
MODULAR_PACKAGE=/absolute/path/to/unknot_modular_boundary

git worktree add --detach ../ProveIt-modular-review \
  8a95834940cf77cdab1b39571ffc102ca8b6bede
git -C ../ProveIt-modular-review apply --check \
  "$MODULAR_PACKAGE/patches/modular_boundary.patch"
git -C ../ProveIt-modular-review apply \
  "$MODULAR_PACKAGE/patches/modular_boundary.patch"

cd ../ProveIt-modular-review/Topology/UnknotRecognition/fast
python -B -m unittest discover -s tests -p 'test_modular_*.py' -v
```

The source snapshot already contains the additions. Apply the patch to the upstream checkout, and use the snapshot separately for reproduction. The patch carries code and documentation; the supplied result JSON files and article are separate review artifacts.

A proposed article destination is `Topology/UnknotRecognition/synthesis/modular_boundary/`, preserving the `sections/`, `tables/`, and `figures/` subdirectories. The accompanying result files can be retained under `fast/results/`, with this package's provenance and verification records beside the article. This is a proposed integration layout; the package does not publish or modify the upstream repository.

## Run the source snapshot

Python **3.10 or newer** is declared by the package; the recorded runs used **CPython 3.12.14 on Linux x86_64**. Production modular code uses the standard library and the maintained `fastunknot` package. It has no dependency on the archived rational prototype or Regina. Research audits use the bundled archived reference code. The benchmark additionally requires POSIX signal support and Git metadata.

From the package root:

```bash
cd reproducibility/ProveIt/Topology/UnknotRecognition/fast
python -B -m unittest discover -s tests -p 'test_modular_*.py' -v
python -B modular_research/demo.py --output results/modular_demo_rerun.json
python -B -m fastunknot recognize examples/conway.json \
  --backend shadow-modular --shadow-primes 65521
```

The first command runs the **31 new modular tests**. The demonstration includes a proper-prefix modular obstruction and replay, as well as an unknot whose verdict comes from the final closed rank. The normal `recognize` command can stop in an earlier filter, so it is not an isolated observer demonstration.

The public Python selector is `recognize(diagram, backend="shadow-modular", shadow_primes=(65521,))`. The default palette contains only `65521`; supplied primes must be distinct, odd, and below `2**31`. For direct raw observations and replay, see [the backend guide](reproducibility/ProveIt/Topology/UnknotRecognition/fast/MODULAR_BOUNDARY.md) and `modular_research/demo.py`.

An observation greater than one certifies knottedness. A small modular observation is inconclusive, even when its comparison with the exact integer observer has been completed. Local observer exhaustion falls back to the existing Euler or capped scan path. Global time or object exhaustion yields `UNKNOWN` through the public recognizer.

### Reproduce the diagram audit

From the same `fast` directory:

```bash
python -B modular_research/audit.py --help
python -B modular_research/audit.py \
  --seed 26100858 --random-count 64 \
  --output results/modular_audit_rerun.json
```

These are the recorded default selection parameters. The saved [audit JSON](reproducibility/ProveIt/Topology/UnknotRecognition/fast/results/modular_audit.json) also contains the accepted input list, mirrors, and crossing orders. The audit compares 138 diagrams with independent reduced F₂ cubes, checks 868 proper prefixes and 15,096 modular vectors over six primes, and replays 50 positive raw claims. Prime three alone misses 70 real obstructions; it produces no false positive in this audit. The six-prime adaptive palette certifies all 868 recorded threshold comparisons.

The independent arithmetic check runs from the **package root**, requires no `fastunknot` imports, takes no command-line options, and writes its result to standard output:

```bash
python -B verification/arithmetic_audit.py \
  > verification/arithmetic_audit_rerun.json
```

Compare the counts with [arithmetic_audit_result.json](verification/arithmetic_audit_result.json): 33,300 minimum-norm cases and 1,496,340 weighted threshold cases. These finite checks complement the general proofs.

### Test-suite status

The [modular test log](verification/modular_tests.log) records all 31 new tests passing. The [broader suite log](verification/full_tests.log) records **708 discovered tests: 704 passed, three skipped, and one error**. That broader run preceded the addition of the ten replay tests; those ten are included in the complete 31-test modular run.

The error is an inherited normal-surface subprocess communication defect, reproduced in isolation and against unchanged baseline worker source on the recorded runtime. It is documented in [normal_surface_baseline_issue.md](verification/normal_surface_baseline_issue.md), its [JSON record](verification/normal_surface_baseline_issue.json), and [the isolated rerun log](verification/normal_surface_rerun.log). No worker fix is included in the integration patch. **The full maintained suite is not reported as green.**

To repeat that broader run from `fast`:

```bash
python -B -m unittest discover -s tests -v
```

The supplied evidence establishes a stalled optional-worker request and timeout on the recorded runtime; it does not establish a false topological verdict.

### Reproduce the benchmark in the patched Git checkout

Run this from `Topology/UnknotRecognition/fast` in the upstream review checkout created above. The driver records `git rev-parse HEAD`, so the standalone source subset without Git metadata is intended for tests, the audit, and the demonstration.

```bash
python -B modular_research/benchmark.py --help
python -B modular_research/benchmark.py \
  --rounds 5 --seconds 3 --seed 20261008 \
  --scopes streams raw pipeline disabled \
  --output results/modular_benchmarks_rerun.json \
  --summary results/modular_benchmarks_rerun.txt
```

These reproduce the driver's recorded defaults while preserving the supplied result file. Keep source files unchanged throughout the measurement. The driver records hashes before and after its run, all raw samples, paired arm orders, individual short-call repetitions, input and order hashes, and censored pilots.

There is one excluded warm-up per arm, five shuffled paired rounds, fresh preparation inside each measured call, and an identical integer control. Calls receive a three-second cooperative allowance and a separate **3.15-second in-process POSIX signal cap**. Correctness comparisons and digests are outside timing. A censored long stream triggers a separately recorded shorter-stream pilot; hardware differences can therefore change which query count is measurable. Compare matching counts and complete samples before comparing ratios. The `disabled` scope deliberately turns off earlier filters and must remain separate from normal pipeline results.

## Rebuild the article

The generated tables and figures are included. From the package root:

```bash
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  unknot_modular_boundary.tex
```

This requires a LaTeX installation providing the packages named in the preamble and `latexmk`. To regenerate the tables, CSV measurements, and performance figure from the supplied JSON records, use Python with Matplotlib:

```bash
python -B build_assets.py
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  unknot_modular_boundary.tex
```

`build_assets.py --fast-root PATH` selects a different `fast` source/result directory. Its default is the bundled reproducibility layout. The asset provenance file records the inputs used to produce the tables and figure. For package integrity, run `sha256sum -c MANIFEST.sha256` from the package root before generating new outputs.

## Research direction and current literature

The near-term performance priorities are response scheduling, reuse across suffix changes, singular-safe articulation-block compression, tighter certified coefficient bounds, and memory accounting. The asymptotic target requires a constructive bound on the size of continuation-compatible complex representations and on the work before a decisive observation. A small determinant or a small frontier alone does not supply either bound.

The article distinguishes the [March 2021 Lackenby handout](https://people.maths.ox.ac.uk/lackenby/quasipolynomial-talk-oxford-compressed.pdf) announcing `2^{O((log n)^3)}` time from the [July 2026 hierarchy preprint](https://arxiv.org/abs/2607.23350v1), which leaves possible speed-ups to further work. It also acknowledges [Musick's September 2026 preprint](https://arxiv.org/abs/2609.06492v2) claiming polynomial-time recognition without validating or adopting that claim. The [January 2026 Kelomäki–Schütz preprint](https://arxiv.org/abs/2601.02119v1) supplies a concrete warning about explicit basis growth even for three-braids, alongside polynomial-time structural formulas.

This package is an AI-assisted working paper and implementation continuation prepared for Vladimir Reshetnikov. Its proofs, source changes, finite audits, experimental findings, and unresolved obligations are separated so that repository review can assess each on its own evidence.
