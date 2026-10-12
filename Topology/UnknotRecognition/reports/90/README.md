# Three reductions for certified unknot hierarchies

Research continuation for Vladimir Reshetnikov's **ProveIt** project, prepared
12 October 2026 against repository commit
`a28a49ee5c4145db0facbeb1e7f65cd8a2816775`.

Start with the comprehensive article,
[hierarchy_kernels.pdf](article/hierarchy_kernels.pdf), whose complete source is
[hierarchy_kernels.tex](article/hierarchy_kernels.tex). The article gives the
proofs, comparisons with the incoming reports and external literature,
experimental evidence, and a prioritized research program. This archive adds
research modules and certificates; it does not change the maintained
recognizer's default dispatch or claim a completed quasi-polynomial recognizer.

## What is established

| Layer | Result supplied here | Limit that remains |
|---|---|---|
| Normal-disc discovery | Complete search in a specified cancellation class in `t^(r+O(1)) (C d^2)^k poly(k,B)`, where `k` counts exceptional edges, `r` their incidence components, and `d` the maximum tetrahedron incidence of an edge. A certified 15-tetrahedron meridian has two disconnected cancellation components. | No general geometric bound on these parameters; exhaustion concerns only the searched class. |
| Interval-bundle attachments | A genuine orientable interval bundle over a bordered base `B`, attached along nonempty proper `A ⊊ ∂B`, adds exactly `a - chi(B)` relative one-handles, where `a` counts attached intervals. This gives free-product and exact handlebody-census formulas, including proper annular attachments. | Marked-curve transport requires additional source geometry. Saturated bases leave genuine two-handle attaching curves. |
| Repeated graph patterns | Component routing and bounded reblocking give a threshold-three marked-query kernel of size at most `6 d^2 Q` for a binary power of a size-`Q` tile with `d` components, provided every component meets both interfaces. The first aligned power is at most `d`, sharply. | A geometric producer must supply a faithful descriptor. Large powers with a component missing an interface and unrestricted nested reuse are outside this implementation. |
| Exact connected cutoff | For the two exact edge-presence marks and unit edge costs, the optimal universal cutoff is `b(0)=1`, `b(1)=3`, `b(2)=4`, and `b(k)=k+1` for `k≥3`. | The certificate CLI is the threshold-three cubic-graph query; other thresholds are exposed through the kernel-building API. |

The native geometric extension completes **35 of the retained 106 cuts**, up
from 30, preserving every earlier completion. All five new cases have saved
source certificates and independently agree with the retained Regina audit.
This is additional certified coverage: on these small fixtures the compiled
Regina oracle was faster than the Python source-certificate path.

The routing examples include multiplicities with 4,097-bit encodings and retain
original cut-edge addresses. Complete graph-query measurements show both the
overhead on small instances and the benefit of eliminating long explicit
repetitions. Cancellation measurements distinguish complete candidate
generation from positive queries with different topology gates. The raw
samples and measurement boundaries are retained; none is an end-to-end
knot-recognition speed claim.

## Validate the archive

Use Python 3.12; the retained environment used Python 3.12.14. The production
modules, saved-certificate checkers, and default validation need only the
standard library and the source dependencies already bundled here. No external
checkout, network access, Regina installation, or package download is needed.

From this directory:

```bash
python verify_all.py
```

The runner checks the pinned upstream module hashes and executes each subsystem
in a separate process with its correct local import paths. The current suite
contains **52 named test methods**: 27 routing, 14 geometry, and 11 cancellation.
It also independently replays the four graph examples, five saved native
geometry certificates, and the saved positive cancellation witness. Producer
entry points are disabled during these ten saved-certificate replays. Missing
fixtures, import failures, skipped tests, failed checks, and timeouts produce a
nonzero exit status.

The observed counts and outcomes are written to
[`results/verify_all.json`](results/verify_all.json), with full per-group logs and
JSON records under `results/verification/`. To replay only the saved proofs:

```bash
python verify_all.py --only replays --output results/replay_only.json
```

`--only tests` runs the test groups. `--timeout 600` is the default per-group
limit; it can be increased for a slower machine. The default runner does not
repeat benchmarks, external oracle censuses, or the article build.

The equivalent test commands, using a POSIX shell, are:

```bash
PYTHONPATH=code python -m unittest discover -s tests -v
(cd geometry && PYTHONPATH=code:vendor python -m unittest discover -s tests -v)
(cd cancellation && python -m unittest discover -s tests -v)
```

The bundled runtimes are the default for this complete archive. The standalone
subpackage READMEs also describe their earlier extraction layouts and external
checkout options; those are unnecessary for `verify_all.py`.

## Use the graph certificate CLI

An aligned example:

```bash
PYTHONPATH=code python -m routed_patterns examples/routed_4097_bits.json \
  --output results/new_routed_certificate.json
PYTHONPATH=code python -m routed_patterns examples/routed_4097_bits.json \
  --verify results/new_routed_certificate.json
```

For arbitrary through-component tiles, enable exact reblocking on generation:

```bash
PYTHONPATH=code python -m routed_patterns examples/through_4097_bits.json \
  --through --output results/new_through_certificate.json
PYTHONPATH=code python -m routed_patterns examples/through_4097_bits.json \
  --verify results/new_through_certificate.json
```

Verification detects the ordinary or reblocked certificate schema
automatically. These commands return graph-query certificates. A positive
graph query becomes a boundary-pattern essentiality statement only after the
separate spherical embedding, ball, and source-chart hypotheses are certified.

## Artifact inventory

| Path | Contents |
|---|---|
| `article/hierarchy_kernels.pdf` | Complete research article. |
| `article/hierarchy_kernels.tex`, `article/sections/`, and other article `.tex` files | Main source, full proofs, literature context, evidence, research questions, and bibliography. |
| `article/build.sh`, `article/figures/` | PDF build entry point and retained static performance figures. |
| `code/routed_patterns/` | New component routing, through reblocking, independent source reconstruction/checking, and CLI. |
| `code/pattern_kernel/` | Reused incoming connected-pattern types, graph proof machinery, and finite signature implementation. |
| `tests/` | Routing/reblocking test methods, including full-signature comparisons, sharpness, source lifting, and mutations. |
| `examples/` | Four graph inputs and their saved certificates, including huge binary multiplicities and a positive flow certificate. |
| `experiments/` | Reproducible routing benchmarks, independent finite oracles, partition reblocking audit, cutoff audit, and fixture generators. |
| `results/` | Raw routing measurements, exhaustive finite comparison summaries, source-review provenance, and validation outputs. |
| `geometry/article/`, `geometry/code/unsaturated_bundles/` | Full geometric extension proofs, finite reduction, independent census replay, and native source adapter. |
| `geometry/tests/`, `geometry/tools/`, `geometry/evidence/` | Fourteen tests, native audit/benchmark tools, the complete retained coverage summary, timing samples, and five new source certificates. |
| `geometry/vendor/` | Thirty pinned upstream source modules, minimal namespace shims, and the 106-case native corpus. |
| `cancellation/fastunknot/`, `cancellation/bootstrap.py` | New cluster search, unchanged incoming rank gate, and local research-overlay loader. |
| `cancellation/tests/`, `cancellation/artifacts/`, cancellation audit/benchmark scripts | Eleven tests, disconnected meridian, finite one-edge inventory, external full-census evidence, and paired timing records. |
| `cancellation/runtime/` | Forty-two pinned source dependencies and the coherent-obstruction fixture used by the standalone overlay. |
| `provenance/cancellation_dependencies.json`, `geometry/evidence/upstream_dependencies.json` | Upstream paths, commit/archive provenance, dependency hashes, and namespace-shim explanations. |
| `provenance/source_checkpoint.json`, `provenance/NEW_AND_REUSED.md` | Exact repository/archive checkpoint and separation of new work from reused material. |
| `integration/INTEGRATION.md` | Additive integration guidance, API examples, schemas, interpretation of outcomes, and reproduction commands. |
| `verify_all.py` | Standard-library orchestration of retained tests and independent saved-proof replays. |
| `requirements-audit.txt`, `LICENSE` | Optional oracle/figure dependencies and the supplied license. |

Regina 7.4 is optional for repeating the external topology oracles and full
vertex census. Matplotlib is optional for regenerating article figures. A TeX
installation with the packages named in the main source is needed only to
rebuild the PDF. The optional Python dependencies are listed in
`requirements-audit.txt`. To regenerate the figure and its accompanying routing
table from retained measurements:

```bash
python experiments/make_report_figures.py
```

With `latexmk` installed, build the article using:

```bash
sh article/build.sh
```

For integration details, use [INTEGRATION.md](integration/INTEGRATION.md). The
first integration step should preserve this isolated research package and its
source/checker separation; promotion into the maintained recognizer should
follow explicit compatibility and dispatch decisions.
