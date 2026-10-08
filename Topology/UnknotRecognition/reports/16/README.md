# Faster cobordism algebra and certified finite-quotient filters

Research continuation for Vladimir Reshetnikov's ProveIt project, 8 October 2026.

The article is **`article/unknot_dense_algebra.pdf`** (32 pages). Its complete
TeX source, proofs, bibliography, tables and vector figure are included.

## Main results and their status

1. **An exact dense coefficient algorithm.** Compiled characteristic-two
   cobordism composition factors into input-variable contraction, multiplication
   in a squarefree algebra, and output reconstruction. Ranked subset convolution
   replaces a dense `4^m` term-pair loop by `poly(m) * 2^m` bit work for a frontier
   of `2m` endpoints. The implementation avoids repeated updates to exponentially
   long packed integers. This is a proved local bound, using the established
   Björklund–Husfeldt–Kaski–Koivisto convolution algorithm.
2. **A recovered grading and sharper component-type bound.** Genuine differential
   entries remain homogeneous in dot degree despite the scanner erasing the
   quantum grading. This gives a cheaper homogeneous multiplication path and
   improves the sufficient component-sharing exponent from `b^2 * 2^m` to
   `b^2 * binomial(m, floor(m/2))`. A bound on actual component size `b` remains
   necessary; this archive does not claim an already benchmarked merge with
   report 07.
3. **A bounded A5 witness backend.** Checked Wirtinger seed plans and exact
   centralizer-orbit enumeration produce explicit nonabelian permutation
   certificates. A separate checker replays every witness. Exhaustion returns
   `INCONCLUSIVE`, never an unknot verdict.
4. **A palette-size obstruction.** For prime `p > 3`, the nontrivial,
   determinant-one torus knot `T(3,p)` has no nonconstant coloring by a finite
   quandle with fewer than `p` elements. Its standard input diagram has `2p`
   crossings. In addition, `T(3,p)` has no nonabelian A5 image for prime `p >= 7`.
   These knots are not asserted to be difficult for the entire portfolio.

**A general quasi-polynomial recognition algorithm is not established.** The
precise missing structural hypotheses and 15 proposed research questions are
developed in the article. Mathematical arguments are written out and supported
by independent computational checks; they are not Lean-formalized or externally
peer reviewed.

## What the timings show

The cold dense-algebra benchmark reaches a baseline/adaptive median ratio of
117.28 at `m=11` (1.378 seconds versus 11.749 milliseconds). This measures one
deliberately dense algebra operation, not complete recognition. All nine
ordinary scanner fixtures select only sparse paths in adaptive mode, and several
complete scans regress. Both the dense mode and A5 filter remain optional:

```python
composition = "legacy"          # default
quotient_max_assignments = 0    # filter disabled by default
```

The archive includes all raw samples, negative results, measured fixture bytes,
exact crossing orders, output invariants, and source hashes. Read Article §10
before comparing numbers from the different timing protocols.

## Verify a fresh extraction

Run the commands below from the extracted `unknot_dense_algebra` directory.
Use Python 3.10 or newer. Do not use `python -O`, which disables assertions.
The recognizer, tests and reproduction scripts need only the standard library.

```bash
python -B tools/verify_bundle.py
python -B verification/finite_quotient/replay_certificates.py
python -B verification/finite_quotient/benchmark_finite_quotient.py --smoke
```

The first command verifies the complete manifest, all 40 exact baseline Git
blobs, measured source and input hashes, and consistency of all 135 recorded
scanner outputs. It applies the patch in a temporary directory and compares
the result byte for byte with the supplied implementation. It does not touch
your repository. Git is required for that application check; `--no-patch`
performs the remaining checks without Git.

The second command replays all ten stored nonabelian certificates. The third
checks that the production and baseline packages load from separate bundled
trees. These commands perform no timing benchmark.

## Run the recognizer and integrated tests

```bash
cd implementation/fast
python -B -m fastunknot khovanov examples/conway.json \
  --composition adaptive --check-d2
python -B -m fastunknot recognize examples/conway.json \
  --no-jones --quotient-max-assignments 5000 --quotient-seconds 0.1
python -B -m unittest discover -s tests -v
```

The recorded suite passes **74 tests**: all 41 original regressions, 11 dense
algebra tests, 11 finite-target tests, and 11 integration tests. The `--no-jones`
example exposes the new fallback on Conway; the existing default Jones stage
already decides that fixture efficiently. See `implementation/fast/INTEGRATION.md`
for the full API, unsupported option combinations, shared deadlines, factor
evidence, and race-worker behavior.

## Reproduce the independent checks and measurements

From the bundle root:

```bash
python -B verification/algebra/test_fast_compose.py
python -B verification/algebra/referee_fast_compose.py
python -B verification/algebra/audit_grading.py
python -B verification/algebra/benchmark_dense.py --max-m 11 --repeats 5
python -B verification/finite_quotient/benchmark_finite_quotient.py \
  --repeats 9 --include-csp
python -B implementation/fast/benchmark_composition_scanner.py \
  --baseline-root baseline/fast --repeats 5 \
  --output paired_scanner_benchmark_rerun.json
```

These commands write new reproduced/rerun JSON files; the recorded measurements
are retained. Use the stated repetition count to recover the dense benchmark's
exact seeded input sequence. The individual verification READMEs document
all seeds and scopes. Timings vary with hardware and system load. The complete
scanner benchmark uses one isolated child process per timed sample, while the
finite-target comparison uses warm calls in one process. They are distinct
protocols and should not be combined into a single speedup calculation.

The 8,637 scalar composition comparisons span all 2,879 **noncrossing** matching
triples through eight endpoints with three sampled morphism pairs each. They
are not an exhaustive test of all unrestricted matchings or all coefficients.
The separate checks include 700 abstract plans, 2,100 associativity identities,
8,768 transfer comparisons and the recovered-grading audit.

## Rebuild the article

The generated tables and figure are included, so a PDF build requires only
a usual LaTeX installation with pdfLaTeX, AMS packages, Latin Modern,
microtype, TikZ, listings, hyperref, fancyhdr and needspace. No BibTeX or
Biber step is required.

```bash
make paper
```

Equivalently, run `pdflatex -interaction=nonstopmode -halt-on-error
unknot_dense_algebra.tex` three times from `article/`.

To regenerate tables from the archived JSON, without rerunning any measurements:

```bash
python -B tools/build_tables.py --tables-only
```

To regenerate the static performance figure as well, run without `--tables-only`.
That optional operation requires Matplotlib; the recorded build used version
3.10.8. PDF metadata and font output can differ across TeX installations, so
rebuilding is not a promise of an identical PDF byte stream. Verify the supplied
manifest before editing or rebuilding; it describes the delivered bytes.

## Apply the integration patch

The patch targets ProveIt commit:

```text
ca61a1a5f967999d778d6efd7c882e77a2eb379d
```

Its `fast/` tree is `b99a666269f660d932fc82ac8d1f29d3ae42231f`.
From your ProveIt checkout, substitute the actual extracted bundle path:

```bash
git apply --check /path/to/unknot_dense_algebra/patches/fast_dense_algebra_and_a5.patch
git apply /path/to/unknot_dense_algebra/patches/fast_dense_algebra_and_a5.patch
```

The patch includes the optional modules, narrowly scoped existing-file edits,
tests, example, benchmark script, recorded scanner data and integration notes.
It does not delete existing result directories. It can be regenerated with
`python -B tools/build_patch.py`. The article and verification supplement can
be placed in a new report directory, for example
`Topology/UnknotRecognition/reports/dense-algebra-2026-10-08/`.

If your checkout has advanced, reconcile its changes and rerun the suite.
This is not a tested aggregate merge of the earlier pointed scanner,
report-07 sharing, three-braid specialization, and newer preprocessing work.

## Provenance and file map

| Location | Contents |
| --- | --- |
| `article/` | Complete 32-page article, TeX sections, self-contained bibliography, exact tables and figure. |
| `implementation/fast/` | Runnable integrated code and all 74 tests. |
| `baseline/fast/` | Canonical source files verified against pinned Git blob hashes. |
| `verification/algebra/` | Portable algebra checks, grading audit and dense measurements. |
| `verification/finite_quotient/` | Portable comparison, exact measured fixtures, ten witnesses, five plans, negative controls. |
| `provenance/` | Source revisions, byte normalization record, baseline test log and artifact validation summary. |
| `patches/` | Git-compatible patch. |
| `tools/` | Build, verification and patch-reproduction helpers. |
| `manifest.json` | Byte sizes and SHA-256 hashes of delivered files (excluding the manifest itself). |

Each initially materialized baseline source file had one extra terminal LF.
The delivered baseline removes precisely that byte and matches all 40 original
Git blob identities. Recorded benchmark hashes identify the measured bytes;
the verification tools allow only this documented one-byte difference when
checking measured source hashes. Exact measured fixture streams are preserved
separately. No timing sample has been rewritten to conceal that distinction.

The source audit includes the pinned ProveIt report 07 and earlier continuation
archives, and the README/catalogue of `openai/math` at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The latter audit found no directly
applicable unknot-recognition theorem; no theorem from that catalogue is assumed.
The article's 16-item bibliography supplies version-pinned primary references.
