# Arithmetic Continuations and Local Certificates for Unknot Recognition

This package continues the exact unknot-recognition work in
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt),
using the pinned baseline commit
[`86f23490006c880cd01db9bec10761d39c6395c8`](https://github.com/VladimirReshetnikov/ProveIt/commit/86f23490006c880cd01db9bec10761d39c6395c8).
It contains a detailed article, executable improvements, proofs of explicit
representation barriers, an integration patch and the raw verification and
benchmark records.

**The package does not establish a general quasi-polynomial unknot-recognition
algorithm.** It supplies exact polynomial arithmetic on a significant explicitly
presented class, a checked local obstruction for ordinary diagrams, and precise
lower bounds explaining why certain full-complex or linear-summary approaches
cannot obtain the desired bound at the specified checkpoints.

## Article

- [Complete PDF](article/unknot_arithmetic_continuations.pdf)
- [Complete LaTeX source](article/unknot_arithmetic_continuations.tex)

The numbered source fragments are retained in `article/`. The combined `.tex`
contains the article text and tables; supplementary benchmark figures are used
when available. The paper states the imported topology, proves the new
construction and accounting claims, reports both improvements and regressions,
and ends with further research questions and concrete completion criteria.

## What the contribution does

| Component | Established scope | Principal limitation |
|---|---|---|
| Rational continuation family | An explicit Boolean unknot-acceptance identity matrix of order `2^m`, realized by rational tangles of linear crossing size | This bounds continuation states or exact linear Boolean summaries; it is not a general running-time lower bound |
| Arithmetic representation | Primitive slope columns use linearly many bits, with a rank-at-most-two signed determinant pairing followed by nonlinear readout | Rationality of the supplied pieces is part of the checked input |
| Full-complex checkpoint barrier | A specified four-ended prefix in an actual family of unknots forces exponentially many explicitly delooped summands in any homotopy-equivalent complex of that form | It does not quantify over all scan orders or arbitrary succinct representations |
| Supplied Montesinos classifier | Complete `UNKNOT`/`KNOTTED` decision for numerator closures of an integer plus separately supplied finite rational tangles | It does not discover arbitrary Montesinos decompositions hidden in a PD |
| Local obstruction | Checked literal occurrences of non-embeddable Montesinos disk tangles inside otherwise arbitrary validated knot PDs | The fixed catalogue and optional custom templates detect exact diagram patterns; they do not search arbitrary tangle isotopies |

The decision classifier uses established rational-tangle and Seifert-cover
theorems. It does not promote determinant one to an unrestricted unknot test:
the package includes determinant-one nontrivial Montesinos knots. Every rational
summand retains its own primitive denominator. Numerically reducing the sum of
fractions would lose essential information and is deliberately avoided.

The local search is a separate **opt-in Python wrapper**. Existing Seifert and
invariant filters sometimes decide its examples more cheaply; the recorded
regressions are a reason to preserve that option. Resource-limited incomplete
runs remain `UNKNOWN` and are retained as censored observations.

## Start with the executable code

Python **3.10 or later** and its standard library are sufficient for recognition,
tests and arithmetic diagnostics. The recorded measurements used Python 3.12.14.
Installing a package or fetching dependencies is not required when running from
the supplied `fast/` directory.

From any initial working directory:

```bash
cd /absolute/path/unknot_arithmetic_continuations/fast
python -m fastunknot recognize examples/trefoil.json
```

For a supplied Montesinos source:

```python
from fastunknot import Diagram, recognize

diagram = Diagram.from_rational(0, [[2, 3], [-2, -2, -1, -2]])
result = recognize(diagram)
assert result.status == "UNKNOT"

# Same validated PD, with the new source stage disabled.
baseline = recognize(diagram, use_rational=False)
assert baseline.status == "UNKNOT"
```

The corresponding JSON grammar is:

```json
{"montesinos":{"e":0,"tangles":[[2,3],[-2,-2,-1,-2]]}}
```

Each inner list is an ordinary continued fraction. The constructor builds its
actual crossings, glues the tangles and validates the closed PD. It attaches
immutable checked provenance; a bare PD plus an unsupported source assertion
cannot trigger this classifier. `--no-rational` disables that stage in the CLI.

Binary coefficients can describe exponentially many expanded crossings. Use
the direct arithmetic API when no PD expansion is desired:

```python
from fastunknot import montesinos_certificate

witness = montesinos_certificate(0, [[0, (1 << 20000) + 1]])
assert witness["status"] == "UNKNOT"
```

The ordinary CLI constructs a Diagram and applies the default 100,000-crossing
expansion cap. The compressed API is explicit; the CLI does not silently switch
representations. Detailed grammar, provenance, local-wrapper and certificate
examples are in the final section of [fast/README.md](fast/README.md).

## Reproduce checks without overwriting the recorded evidence

The entry point accepts an absolute script path and works from any directory:

```bash
python /absolute/path/unknot_arithmetic_continuations/experiments/reproduce.py --quick
```

It copies the frozen code and fixtures into a new reproduction workspace under
`reproductions/<UTC timestamp>/`. New logs, results and generated examples stay
there. The supplied `results/` records remain unchanged. Use `--output-dir` to
select a different **new** directory outside the code and fixture trees being
copied.

| Mode | Work selected |
|---|---|
| No mode, or `--quick` | Both new test suites, finite Montesinos and local-certificate audits, the included checkpoint diagnostic, and identity levels through `m=4` |
| `--full-tests` | All 152 combined test methods |
| `--identity` | Original exhaustive identity diagnostic through `m=10`: 1,398,101 matrix entries across all levels |
| `--benchmarks` | Paired capped recognition, local-wrapper and compressed-arithmetic benchmarks, seven repeats by default |
| `--all` | All stages; full tests and benchmark reruns are explicitly selected and may be slow |

Modes may be combined. When full tests are selected, the new suites are not run
again separately. Useful commands are:

```bash
python /absolute/path/unknot_arithmetic_continuations/experiments/reproduce.py --full-tests
python /absolute/path/unknot_arithmetic_continuations/experiments/reproduce.py --identity --max-m 10
python /absolute/path/unknot_arithmetic_continuations/experiments/reproduce.py --benchmarks --repeats 7
python /absolute/path/unknot_arithmetic_continuations/experiments/reproduce.py --all --output-dir /absolute/path/new-unknot-reproduction
```

The benchmark defaults retain a 3-second cooperative recognition budget and
20,000-object scanner cap, configurable with `--seconds` and `--max-objects`.
Timing depends on the host. A censored baseline run is not counted as a completed
solve and receives no finite speedup estimate.

The launcher records full stage commands, exit codes, elapsed times and paths in
`reproduction_summary.json`, with complete per-stage output under `logs/`. It
stops on the first failure and preserves the partial record. The launcher is a
convenience wrapper around the actual diagnostics, not a replacement for them.

### Individual diagnostics

All scripts below resolve their input paths from their own file location.
Running them directly writes their conventional output under this package's
`results/` directory, so use the launcher when preserving the bundled evidence
is desired.

| Script | Purpose |
|---|---|
| `experiments/verify_identity_family.py` | Integer matrix identity, parity, crossing budgets and off-diagonal separation; accepts `--max-m` and `--output` |
| `experiments/verify_checkpoint_family.py` | Fixed-prefix recurrence, actual PD crossing counts, closure decisions and small independent scalar homology checks |
| `experiments/audit_montesinos.py` | 1,200 seeded source, component-parity, exact-Alexander and serialization checks |
| `experiments/audit_subtangles.py` | Forged certificates, relabelling/rotation/mirror invariance, known-unknot controls and inapplicable templates |
| `experiments/benchmark.py` | Raw paired measurements; accepts `--repeats`, `--seconds` and `--max-objects` |
| `experiments/corpus.py` | Deterministic rational-pair, pretzel and local-insertion constructors used by the experiments |

Finite diagnostics verify implementations and conventions. The article's
mathematical proofs supply the asymptotic and topological conclusions.

## Rebuild figures and the PDF

Recognition and all checks above require no plotting or TeX libraries.
**Matplotlib** is needed only to regenerate the optional research figures;
a **LaTeX installation** with the packages named in the source is needed only
to rebuild the PDF.

```bash
python /absolute/path/unknot_arithmetic_continuations/experiments/make_figures.py
python /absolute/path/unknot_arithmetic_continuations/article/build_article.py --pdf
```

The figure script reads recorded measurements and writes
`article/figures/benchmarks.png` and `article/figures/benchmarks.svg`; it does not
rerun the benchmarks. The combined LaTeX source remains usable when these
supplementary figures are absent.

## Integrate into ProveIt

The complete modified `fast/` snapshot is included. Its original
[MIT No Attribution license](fast/LICENSE) is preserved. The patch changes
13 paths and includes every new source, test, local example and certificate
required by the new tests.

See [integration/README.md](integration/README.md) for exact application commands.
The patch applies at the ProveIt repository root:

```bash
git apply --check /absolute/path/unknot_arithmetic_continuations/integration/fast_arithmetic_continuations.patch
git apply /absolute/path/unknot_arithmetic_continuations/integration/fast_arithmetic_continuations.patch
```

The authoritative pinned source inventory is
[integration/source_manifest.json](integration/source_manifest.json).
[integration/patch_manifest.json](integration/patch_manifest.json) identifies
the exact baseline and resulting file bytes. The patch was applied to a fresh
baseline copy, all resulting files were compared byte-for-byte, and the 18 new
test methods passed in that isolated copy without experiment-directory imports.

## Recorded results and package map

The final combined run passed **152 test methods**, comprising **134 inherited**
and **18 new** methods. Its `unittest` duration was 30.415 seconds; measured
process wall time was 30.651362 seconds, with exit code zero. These are host
observations, not guaranteed execution times.

| Path | Contents |
|---|---|
| `article/` | Complete `.tex` and `.pdf`, retained numbered fragments and optional figures |
| `fast/` | Complete modified Python recognizer, test suites, examples, certificates and preserved license |
| `integration/` | Repository patch, application guide, pinned source inventory and patch file manifest |
| `experiments/` | Reproduction launcher, independent diagnostics, deterministic corpus and benchmark/figure scripts |
| `results/integrated_tests.txt` | Final complete 152-method run |
| `results/patch_verification.txt` | Exact-baseline application and isolated new-suite replay |
| `results/benchmarks.json` | Full paired samples, control measurements, censored runs, local regressions and compressed inputs |
| `results/identity_verification.json` | 1,398,101 exact identity-family matrix-entry checks |
| `results/checkpoint_family_verification.json` | Concrete fixed-prefix lower-bound diagnostics |
| `results/montesinos_audit_results.json` | 1,200-source audit, including 718 knot-PD Alexander and 482 link-component comparisons |
| `results/subtangle_audit_results.json` | Local adversarial and invariance audit |
| `research_notes/` | Implementation and independent mathematical audit notes |
| `RESEARCH_PROVENANCE.md` | Exact repository scope, narrow external inspiration and limits of the claims |

The original observation files distinguish recognition-only timing from PD
construction. They retain cases where the baseline returned `UNKNOWN` and cases
where the opt-in local stage was slower. The empirical improvements support the
implemented specializations; they do not substitute for a general complexity
proof.

The assembled article includes all text and bibliography directly. The optional
`article/references.bib` is supplied for reuse in another document.
`results/claim_ledger.json` records the precise proved/implemented scope, and
`results/portable_reproduction_check.json` records a successful isolated quick replay.

## Check the distributed bytes

Before modifying the package or regenerating any results, run:

```bash
python /absolute/path/unknot_arithmetic_continuations/experiments/verify_package.py
```

This checks every listed deliverable against `SHA256SUMS`. It verifies archive
integrity, not mathematical correctness. Regenerated timing or PDF files will
naturally have different hashes.
