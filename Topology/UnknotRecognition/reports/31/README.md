# Certified primitives for faster unknot recognition

**Research continuation for ProveIt — 8 October 2026**

Start with [the article PDF](article/unknot_certified_primitives.pdf). Its editable main source is [unknot_certified_primitives.tex](article/unknot_certified_primitives.tex). The article gives self-contained proofs, exact implementation contracts, independent audits, controlled measurements, negative results, and twelve research questions organized into three priorities.

This package improves several exact primitives. It does **not** establish a quasi-polynomial worst-case bound for the complete maintained recognizer.

## Results

### 1. A stronger implemented bound for the full Jones polynomial

The new binary planar tensor backend uses at most `2^w` frontier states and polynomial-size exact arithmetic. With the existing checked separator order, its bit time and space are `poly(n) 2^{O(sqrt(n))}`, improving the repository's faithful equality-partition bound `poly(n) 2^{O(sqrt(n) log n)}`.

The proof builds an integral rotation cochain, proves the correct turn for every smoothed circle using face disks and bands, and derives the precise writhe and loop normalization. The implementation supplies Laurent reference arithmetic, exact integer decoding, and valuation-normalized integer arithmetic. The last removes large monomial offsets without numerical approximation.

This realizes an established square-root-exponential principle in the present code. Ellenberg, Newman, Sawin, and Shi already proved such a bracket-computation bound in 2013; the article does not claim priority for that exponent. A full polynomial different from one proves knottedness. Identity remains inconclusive in this implementation.

The full six-arm benchmark retains all 630 measured queries: 588 complete and 42 capped, plus 90 excluded warmups. The new tensor backend does not dominate faithful Potts on this corpus. Within tensor arithmetic, the normalized integer mode improves several cases and cuts the tree254 scalar precision from 130,177 bits to a 1,536-bit mantissa. Full results and controls are in `results/tensor_jones_valuation_20261008.json`.

### 2. Certified minimum-disc cocycle seeds

For local heights `h[t,i]` and global vertex potential `f`, the normal-disc objective is

`D(f) = sum_t (max_i(h[t,i] + f[v[t,i]]) - min_i(h[t,i] + f[v[t,i]]))`.

A sparse integral flow minimizes this objective exactly over all vertex-potential changes. The certificate is an integral potential plus one matched corner pair per tetrahedron. Equality of the recomputed primal span objective and the matching's lower bound proves optimality over both real and integral potentials, without rerunning the solver.

The conservative bit bound is `O(T^3 (B + log(T+1)))`. Under the article's compact orientable manifold, coorientation and integral-class hypotheses, a minimum has no nonempty relatively null-homologous component union. In primitive rank one it is connected and nonseparating. The article explicitly notes that the original spanning-tree gauge already has the related connectedness property; optimization preserves it after leaving that gauge.

On the two finite 56-tetrahedron knot exteriors, disc counts change from **109 to 54** for the trefoil and **60 to 38** for the figure-eight. Independent Regina checks give connected orientable surfaces with Euler characteristic minus one and one boundary component. These are geometric-primitive measurements, not end-to-end recognition speedups. A constructed nine-tetrahedron family also handles a 4,103-bit initial disc count and returns a three-disc meridian surface.

Additional proved opportunities include transport of an optimal certificate through a known gauge change and a compressed Euler-characteristic positive disk test, with all required geometric hypotheses stated. Those two opportunities are not new public APIs in this patch.

### 3. An optional strict-majority overlap policy

Compressed relator search can ask first for a witness longer than half the donor, then extend its selected alignment using at most two exact LCP queries. It preserves uncapped local-existence completeness and the existing independent certificate boundary.

On the proved family `D=(ab)^N cTa`, `R=(ab)^N aTb`, `T=aabbccacbabc`, the optimum overlap is exactly `2N`. For `N=2^500`, the optional prefix and interior operations complete in recorded medians of 5.220 ms and 8.100 ms, while the old arms exceed the two-million-work allowance. No numerical speedup ratio is assigned to capped runs.

The first witness can have arbitrarily worse gain than the global optimum, so the policy remains optional. The supplied whole-knot corpus does not reach the changed helper and shows no demonstrated causal recognition improvement. A reachable Gordian residual produces a separately replayable 142-move original-diagram certificate.

### 4. A reproduced external-worker bug repaired

Full validation found that a large request could stop writing to the existing normal-surface worker after a communication timeout on Python 3.12.14. A single payload submission through a communication thread fixes the failure while preserving caller-thread cancellation/deadline checks and process cleanup. The unchanged 500 KB delayed-reader regression now passes; an added cleanup regression covers setup and communication errors.

## Validation

- Passing module runs cover **721 current tests across 83 modules, with no skips**. The exact composition is 712 passing tests from 82 unchanged modules plus the final nine-test worker module. Six public integration tests were rerun afterward and are not counted twice.
- The comprehensive pre-repair batch and the reproduced worker error are retained. An earlier single-process attempt that ended without a unittest summary is separately marked incomplete. This package does not mislabel it as a successful full-suite run.
- The independent tensor audit records **1,260 full-polynomial comparisons**, **23,676 smoothing states**, and **71,860 circle-turn checks**.
- A separate Regina audit checks **210 full-coefficient comparisons** across 70 diagram/mirror variants and all three arithmetic modes.
- The **18-file integration patch** passes a temporary-index apply check against the pinned baseline; every reconstructed changed file matches the supplied snapshot byte for byte.

Details and exact logs are under `validation/`. AI-assisted mathematical and algorithmic reviews are documented separately from executed tests and are not external peer review or proof-assistant formalization.

## Integration

Baseline commit:

```text
8a95834940cf77cdab1b39571ffc102ca8b6bede
```

The source patch is `integration/changes.patch`; `integration/tree/` contains 350 current source, fixture, metadata and reference files with repository-relative paths. The required report02, report24, report26 and report28 reference packages are included. No remote repository write was performed.

At the baseline checkout:

```sh
git apply --check /path/to/package/integration/changes.patch
git apply /path/to/package/integration/changes.patch
cd Topology/UnknotRecognition/fast
python -B -m unittest discover -s tests -v
```

Use `python -B -m fastunknot jones INPUT.json --backend tensor` for the optional exact polynomial backend, `--jones-backend tensor` within `recognize`, and `--group-overlap-witness` for the optional compressed overlap policy. Default matching and historical overlap policies are retained. Cocycle optimization is a standalone primitive.

See [reproduce/README.md](reproduce/README.md) for dependency versions, complete commands, historical-Git prerequisites for the paired overlap benchmark, source assembly, independent audits, certificate replay and interpretation. The optional external package used in geometric validation is Regina 7.4.1.

## Rebuild the article

```sh
python -B reproduce/make_research_tables.py
sh article/build.sh
```

The first command regenerates tables and the figure from archived JSON; it does not rerun timings. Use `--tables-only` if Matplotlib is unavailable and retain the supplied vector figure. Standard TeX Live packages and latexmk build the PDF without shell escape.

The delivered PDF has 38 pages. Its final compiler and visual checks are recorded in `validation/article-qa.json`. To check the extracted files, run `sha256sum -c SHA256SUMS` from this package directory. To rebuild the ZIP and its checksum, run `python -B reproduce/package_release.py`; it excludes caches and intermediate TeX files and verifies every archived member against the manifest.

## Further research

The article prioritizes complete compressed cutting and boundary data, certified parallelity reduction, curve normalization with all relevant size parameters, independently replayed geometric certificates, stronger reset accounting, and bounds on total represented state size. It also proposes a bounded faithful-Potts prelude, weighted/class-aware cocycle objectives, useful vertex freedom, tensor order/outer-face selection, witness-quality guarantees, and complete bounded group discovery.

The key global obligation is to control both the number of states visited and the complete binary size of every state. Polynomial local word operations or small normal-coordinate encodings alone do not establish that obligation. The article gives a precise conditional composition theorem and falsifiable milestones for the next stage.
