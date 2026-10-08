# Toward Quasi-Polynomial Unknot Recognition

## Research continuation for ProveIt — 8 October 2026

This package contains the complete article **Presentation complexity, early first-jet certificates, and streaming boundary responses**, its editable LaTeX sources, exact implementation experiments, raw results, and a reviewable integration patch.

The source baseline is Vladimir Reshetnikov's ProveIt revision
[`1be2abc8cc743c1a3b5cb7fdfeb650697f8e2d5b`](https://github.com/VladimirReshetnikov/ProveIt/tree/1be2abc8cc743c1a3b5cb7fdfeb650697f8e2d5b/Topology/UnknotRecognition).

**Scope:** the article proves parameterized sufficient conditions for quasi-polynomial recognition and improves exact supporting computations. It does not prove a quasi-polynomial bound for the complete maintained recognizer. The proofs are supplied for mathematical review; they are not represented as formally verified. Literature provenance, implementation contracts, negative results, and open structural obligations are stated explicitly.

## Main results

1. An explicit presentation of a knot group with `r` generators and total relator length `N` gives the deterministic bit-complexity bound `poly(N+r) (2+N/r)^{O(r)}`, including dense polynomial construction and coefficient growth. Verified straight-line word circuits and cuts give further bounds `poly(S+r+s) 2^{O(r+s)}` and `poly(S+r+s) (d+2)^{O(r+t)}`. The article separates presentation construction from the decision procedure and proves why small presentations of every entire knot group cannot be expected. It also records the known complete traceless-meridian theorem and an additional coordinate reduction that is **not implemented in the present benchmarked solver**.

2. A first-jet observer computes scalar survivors and a closure multiplier using two binary matrix ranks before cobordism elimination. A multiplier-one rigidity theorem justifies total-rank replacement under every classical link continuation. A flat-origin constraint explains the absence of more exotic minimal interval behavior in genuine complexes. The implementation preserves interruption and whole-component contracts, and its timing regressions are retained.

3. A reverse filtration of actual suffix cut faces constructs all signed-Laplacian boundary responses in `O(n (W+1)^2)` field operations. Singular interior directions, grounding, characteristic two, terminal identifications, and phase conventions are included in the proof. The improvement concerns shared all-suffix setup; it is not a measured speedup of the full recognizer.

The article ends with **18 research questions**, grouped into structural quasi-polynomial targets, algebraic compilation and exact certificates, homological and geometric improvements, and evidence needed for dispatch decisions.

## Package map

| Path | Contents |
| --- | --- |
| `article/unknot_presentations_and_early_certificates.pdf` | Complete compiled research article |
| `article/unknot_presentations_and_early_certificates.tex` | Main LaTeX source |
| `article/sections/` | Proofs, experiments, literature audit, and research agenda |
| `article/references.bib` and the included `.bbl` | Bibliography with source links and a generated fallback |
| `article/figures/` | PNG and SVG figures generated from the archived measurements |
| `article/scripts/plot_results.py` | Reproduction of both figures from raw JSON |
| `integration/unknot_research.patch` | Code, tests, experiment scripts, documentation, and raw results against the pinned baseline |
| `integration/tree/` | The same changed and new repository files as a directly inspectable tree |
| `integration/changed-files.json` | Delta inventory and SHA-256 hashes |
| `integration/verify_patch.py` and `patch-validation.json` | Repeatable clean-copy patch verification and its recorded result |
| `snapshot/Topology/UnknotRecognition/` | Runnable updated `fast/` tree and unchanged reference modules used by existing tests |
| `provenance/` | Source manifests, environment, test records, and PDF validation |
| `MANIFEST.sha256` | SHA-256 digests of all other archived regular files |

The snapshot retains existing project material for reproducibility. The new work is identified by the integration delta; it should not be inferred from every file in the snapshot.

## Build the article

From `article/`:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  unknot_presentations_and_early_certificates.tex
```

A standard TeX Live installation with `latexmk`, BibTeX, `natbib`, `xurl`, `listings`, and the mathematical and layout packages named in the source is sufficient. The complete `.bbl` is included; a network connection is unnecessary. For a build that uses that existing bibliography, run `pdflatex` twice.

Regenerate the figures from the supplied measurements, with Python and Matplotlib:

```bash
python3 article/scripts/plot_results.py \
  --results snapshot/Topology/UnknotRecognition/fast/results \
  --output article/figures
```

## Reproduce the code checks and experiments

From `snapshot/Topology/UnknotRecognition/fast/`:

```bash
python3 -m unittest discover -s tests -q
```

The recorded environment used Python 3.12.14. The optional exact real solver used `z3-solver==5.1.0.0` (core version 5.1.0). The symbolic compiler, first-jet observer, streaming responses, and finite-group checks do not require Z3. Solver-specific tests skip if Z3 is absent; existing Regina-dependent tests skip if Regina is absent.

Read `fast/RESEARCH_20261008.md` for the exact API boundaries, all audit and benchmark commands, timing scopes, and expected interpretation. The seven new result files are:

```text
results/su2_audit.json
results/su2_benchmark.json
results/first_jet_discovery.json
results/first_jet_benchmark.json
results/streaming_response_audit.json
results/streaming_response.json
results/streaming_response_large.json
```

Use fresh output names when rerunning an experiment to preserve the archived observations. Timings are measurements in the recorded environment, not performance guarantees or statistical confidence intervals.

### Recorded validation

- The integrated suite ran **728 tests**, with **3 optional tests skipped**, and passed. After a final public generic-presentation API restriction, the **10 SU(2) tests** were rerun and passed. The timed diagram and word-circuit paths were unaffected by that restriction.
- The response audit compared **19,520** values against independent integer Bareiss cofactors, including singular cases and characteristic two, with zero mismatches.
- The SU(2) audit ran **96** queries on **48 sample entries / 38 distinct PD arrays**: 90 definite outcomes agreed with their oracle and 6 remained inconclusive. Inconclusive queries are not counted as recognition successes.
- The first-jet corpus contained 180 accepted knot samples, with 360 scans and 2,898 stages. All 117 eligible observations agreed with explicit pre/post elimination checks; no odd-total-linear entry occurred among 8,183 inspected minimal entries.

The optional real backend checks exact algebraic models through the same Z3 engine that produced them. It does not supply an independent UNSAT proof checker. Cooperative allowances do not promise a hard operating-system memory or wall-clock cap. The article and implementation documentation give the precise contracts.

## Integrate into ProveIt

Review `integration/changed-files.json` and the patch first. At a clean repository checkout of the pinned revision, with `PACKAGE` set to this unpacked package's absolute path:

```bash
git apply --check "$PACKAGE/integration/unknot_research.patch"
git apply "$PACKAGE/integration/unknot_research.patch"
```

The patch contains **24 files: 22 additions and two modifications**, with no deletions. It adds optional research backends and their evidence. The two modifications are the existing `fast/README.md` notice and an inherited `normal_surface.py` subprocess correction. That correction is attributed to the preceding research continuation and is not claimed as a new mathematical contribution. The default recognition dispatcher does not automatically select the new experimental methods.

A suggested location for the article is:

```text
Topology/UnknotRecognition/research/presentations_early_certificates/
```

Copy the contents of `article/` there. This preserves the relative proof links in the new research documentation. The article is intentionally supplied separately from the code patch so its placement can follow the repository's editorial conventions. No repository push or publication is part of this package.

The package's provenance records document a clean-copy patch check against the pinned files and exact target-file comparison. All 399 selected pinned originals—382 files under `fast/` and 17 test references—were checked against recorded Git blob hashes and byte lengths before packaging.

The clean-copy comparison can be repeated without modifying the supplied checkout:

```bash
python3 integration/verify_patch.py \
  --repo-root /path/to/pinned/ProveIt \
  --output local-validation.json
```

## Review priorities

The highest-value next steps are a precisely defined residual corpus, shared verified presentation provenance, implementation of the known complete traceless-meridian specialization, incremental first-jet component maintenance, and an adaptive consumer of the reusable suffix responses. The mathematical objective is to prove a small circuit cut or controlled checkpoint-gap/frontier bound on that residual class. Cheaply colorable high-rank examples obstruct universal whole-group compression, but they do not settle this filtered-class question.

The complete proofs, qualifications, counterexamples, bibliography, numerical tables, and all 18 proposed questions are in the article.
