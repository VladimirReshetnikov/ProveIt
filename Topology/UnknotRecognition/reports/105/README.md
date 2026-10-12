# Deferred forests and exceptional incidence

Research continuation for Vladimir Reshetnikov's **ProveIt** project, dated 12 October 2026.

The complete article is [Deferred_Forests_and_Exceptional_Incidence.pdf](article/Deferred_Forests_and_Exceptional_Incidence.pdf). Its master [TeX file](article/Deferred_Forests_and_Exceptional_Incidence.tex), section sources, bibliography, and figure are included. The article contains full mathematical proofs and sixteen proposed research directions.

## Main results

1. **Deferred primal forests.** For a fixed source-authenticated raw occurrence matrix whose rows restrict to closed walks in the zero/one-handle graph, full-matrix column peeling succeeds exactly when some primal spanning forest permits complete raw positive-singleton cancellation. Discover the pivots first, choose a forest in their complement, and execute the usual forest-first certificate. A full-matrix stopping set obstructs all primal forest choices in this fixed raw model.
2. **Exceptional-interface dual selection.** If `u` rows meet active columns supported on more than two rows, the finite graph/matrix problem is decidable in `2^{O(u log(u+2))} poly(N)` time, using at most `Bell(u+1)` polynomial independent-representatives calls. The native `u <= 3k` specialization applies to original source-core columns; additional annular rows require the actual general parameter.
3. **Further proved consequences.** The article gives a geometric theta-block family with `3^h` candidate primal trees, an exact coupled-forest corollary under explicit geometric contracts, and a represented binary-matroid extension of deferred basis selection. A separate triangle-column example shows that three-occurrence sparsity and dual-cycle parity alone do not imply dual-tree invariance.

These are local results. **This package does not establish a complete quasi-polynomial unknot recognizer**, a logarithmic exceptional-interface bound, or a complete marked hierarchy engine. Novelty claims are relative to the inspected ProveIt baseline and five incoming packages. Classical prerequisites and prior project results are attributed in the article.

## Native results

| Operation | Corpus | Canonical | Deferred |
|---|---|---:|---:|
| Core certificates | Historical, 106 cases | 100 | 106 |
| Core certificates | Additional, 14 cases | 10 | 12 |
| Whole-cut census | Historical, 106 cases | 92 | 99 |
| Whole-cut census | Additional, 14 cases | 10 | 12 |

All old positive cases remain positive. All **213 canonical/deferred positive whole-cut outputs** passed independent replay. The nine new whole-cut packets and eight new core packets retain their source inputs in `certificates/`.

Regina's literal oracle completed on 113 of 120 sources and agreed with all 104 deferred positives in that subset. Seven further native positives exceeded the 4,096-normal-disc expansion cap and are not claimed to have literal oracle comparisons. All native certificates replayed. Of the nine remaining native refusals, eight contain a nonhandlebody according to the literal oracle; `pilot/finite_figureEight/0` is a missed union of genus-one and genus-two handlebodies. Every native refusal remains `INCONCLUSIVE`.

The standalone dual selector matched an independent exhaustive oracle on **50,658 finite inputs**, with **5,183 independently replayed successes** and zero discrepancies. These matrices are not asserted to be native geometric sources.

All **1,707 distinct real tests** pass across the main run and targeted recovery. The initial sparse checkout omitted historical dependencies, and the recovery harness initially used the wrong working directory for three CLI subprocess tests. `results/failed_module_recovery.json` records the exact accounting and correction; this is not presented as a single clean full-suite invocation.

## Performance interpretation

On the 110 native cores that both strategies solve, the final median batch timings were 116.115 ms canonical and 161.272 ms deferred for 2,750 producer calls: deferred was **1.389 times slower**. Source preparation and replay were excluded from that microbenchmark. Whole-query comparisons, including production and replay, and six explicit-Regina comparisons are reported separately in the article and raw JSON.

The exact asymptotic improvement is elimination of primal-forest enumeration within the supported raw model. The current Python implementation is not uniformly faster on small cases. The canonical strategy therefore remains the default; deferred behavior is explicitly enabled. The geometric family benchmark compares with a **specified unpruned lexicographic enumerator**, not every possible competing algorithm.

## Source baseline and integration

Baseline commit:

```text
c6d0ec8aa0b6308310ab6c081ba29d8bc363ede5
```

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

`patches/deferred_forests.patch` changes four production modules and adds two test modules. `overlay/` contains the same six files using repository-relative paths. Use either the patch or overlay, not both. `baseline/` contains the original four production modules for comparison.

The patch was applied successfully in an isolated minimal checkout of the pinned baseline; every resulting file matched the overlay byte for byte. `results/patch_application_check.json` records that validation. No commit, push, PR, or merge was performed.

From a checkout of the baseline:

```bash
git apply --check /absolute/path/to/package/patches/deferred_forests.patch
git apply /absolute/path/to/package/patches/deferred_forests.patch
cd Topology/UnknotRecognition/fast
python3 -m unittest tests.test_deferred_forest tests.test_deferred_boundary_kernel -v
```

An isolated worktree is appropriate for reviewing the patch against an existing project checkout. For a newer baseline, inspect conflicts and schema interactions before applying.

### API

Run with the patched `fast` directory on the Python import path:

```python
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies

result = normal_cut_handlebodies(
    triangulation,
    coordinates,
    record_certificate=True,
    forest_strategy="deferred",
)
if result["status"] == "COMPLETE":
    assert verify_normal_cut_handlebodies(
        triangulation, coordinates, result["certificate"]
    )
```

The same optional strategy is accepted by `core_handlebody_certificate` and `bundle_boundary_kernel`. Invalid strategies raise `ValueError`. Canonical defaults are preserved. The core schema stays `normal-core-handlebody-v2`; deferred finite-boundary proofs use `bundle-boundary-kernel-v3`. Older boundary schemas retain their canonical forest meaning.

The all-primal-forests completeness statement applies to each supported fixed core or finite boundary matrix, not every conservative branch of the wrapper. Geometric source authentication, omitted-column lifting, dual selection, and marked successor transport remain distinct contracts.

## Reproduce the packaged evidence

The native checks were run with CPython 3.12.14 and Regina 7.4. The finite selector needs only the Python standard library. The project’s broader tests also require historical reference files outside `fast`; a sparse checkout containing only `fast` cannot run all of them. Exact restored directories are listed in `results/failed_module_recovery_commands.txt`.

Set paths for your local checkouts:

```bash
PACKAGE_DIR=/absolute/path/to/ProveIt_Deferred_Forests_2026-10-12
PROVEIT_FAST=/absolute/path/to/ProveIt/Topology/UnknotRecognition/fast
```

Replay the delivered source-bound packets:

```bash
python3 "$PACKAGE_DIR/tools/verify_packets.py" --fast-root "$PROVEIT_FAST"
```

Reproduce core and whole-cut coverage into **new** result files:

```bash
python3 "$PACKAGE_DIR/tools/audit_core.py" \
  --fast-root "$PROVEIT_FAST" --output /tmp/core_audit_new.json
python3 "$PACKAGE_DIR/tools/audit_whole.py" \
  --fast-root "$PROVEIT_FAST" --output /tmp/whole_audit_new.json \
  --certificates /tmp/deferred_packets_new
```

The whole audit’s explicit oracle uses a 20-second subprocess timeout and the baseline oracle’s 4,096-normal-disc expansion cap. The portable core driver was run from the package and exactly reproduced the archived core JSON.

Run the finite theorem audit and the triangle witness:

```bash
cd "$PACKAGE_DIR/finite_selector"
python3 audit_exceptional.py --output /tmp/exceptional_audit_new.json
python3 check_triangle_witness.py
python3 exceptional_forest.py examples/triangle.json
```

`SUCCESS` includes a tree and peel trace. `NO_FOREST` is exhaustive failure for this finite graph/matrix class; it is not a knot or manifold negative. `INCONCLUSIVE` means interrupted search. The finite solver has **no native source adapter in this package**.

Reproduce timings with other CPU-heavy work stopped:

```bash
python3 "$PACKAGE_DIR/tools/benchmark_core.py" \
  --fast-dir "$PROVEIT_FAST" --output /tmp/benchmark_core_new.json
python3 "$PACKAGE_DIR/tools/benchmark_whole.py" \
  --fast-root "$PROVEIT_FAST" --output /tmp/benchmark_whole_new.json
```

The core benchmark alternates order across nine batches; the whole benchmark uses seven randomized-order pairs and three deferred/deferred A/A pairs per case. Raw samples, seeds, environments, and timer boundaries are recorded. Median paired ratios need not equal ratios of separately computed medians.

## Build the article and figure

```bash
python3 "$PACKAGE_DIR/tools/generate_figures.py"
bash "$PACKAGE_DIR/article/build.sh"
```

The PDF build uses `latexmk`, `pdflatex`, BibTeX, and ordinary TeX Live packages including `mathpazo`, `lmodern`, `microtype`, `hyperref`, `cleveref`, and `placeins`. The figure is already supplied; regenerating it needs Matplotlib and NumPy. All TeX inputs needed to rebuild the article are included. Final layout verification is recorded in `results/article_validation.json`.

## Research priorities

The article develops sixteen questions. The immediate priorities are:

- Add the authenticated native adapter for exceptional dual selection and find a source-bound gain after deferred primal selection.
- Resolve the remaining literal handlebody cut `pilot/finite_figureEight/0` with a certificate beyond the current raw model.
- Reuse source data in an adaptive canonical/deferred path.
- Improve the exceptional parameter dependence, prove native structural restrictions, and seek compact certificates of exhaustive finite failure.
- Implement marked successor transport and bound state size, hierarchy depth, repairs, and terminal completion in one complete complexity theorem.

The terminal free-group route in the article is a **proposal using a classical theorem**. It requires verified irreducibility and whole-cut presentations. It contributes no reported native successes and gives no certificate-search bound or marked meridian system.

## Attribution and integrity

`finite_selector/degree_two_backend.py` is an unchanged, attributed copy from the incoming Dual Forest Normalization package. Its SHA-256 is recorded in `SOURCE_AUDIT.json`. The new reduction is in `exceptional_forest.py`; the classical matroid-intersection algorithm is not claimed as new. `LICENSE_NOTES.md` records the provenance of copied material.

`CLAIMS.json` maps the principal claims to their scope and evidence. `SHA256SUMS` covers the complete deliverable other than the checksum file itself. From the package root, verify it with `sha256sum -c SHA256SUMS`.
