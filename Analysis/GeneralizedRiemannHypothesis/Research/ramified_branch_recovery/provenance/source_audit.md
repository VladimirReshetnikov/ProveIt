# Source audit and provenance

Prepared 26 November 2026, America/Los_Angeles. The final public-source check occurred just after midnight on 27 November UTC, still 26 November locally. This note records the sources behind the accompanying research paper and the extent of the comparison. The machine-readable companion is `source_manifest.json`; the full packet-level inventory is `proveit_inventory.json`.

## 1. Current RH and Dirichlet-GRH status

The sources inspected support the current announcement of a formal proof of RH and GRH for Dirichlet L-functions. The [joint statement by the Lean FRO and Mathlib Initiative](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) reports successful compilation, comparison with Mathlib's RH statement, and checks by several proof kernels. [Andrew Sutherland's verification record](https://math.mit.edu/~drew/grh/), updated 25 November 2026, reports completion of its checks for the original proof and identifies a separate verification page for the shorter proof. These are attributed external verification reports; this project did not reproduce their runs.

The requested [Wikipedia article](https://en.wikipedia.org/wiki/Riemann_hypothesis), read again on 26 November locally (27 November UTC), describes RH as a theorem, discusses Alpöge's November 2026 formal proof and its endorsement, and says a natural-language proof had not been published as of 25 November. Its permanent-link target exposed revision `1387920342`; the live article was read successfully, while attempts to retrieve that revision URL timed out. Wikipedia provides context here. The formal theorem's scope and the verification claim were checked against the code interface and primary verification records.

## 2. The inspected Lean repository

- Repository: [lsernau/grh-lean](https://github.com/lsernau/grh-lean).
- Commit: `72fead102f663d5c7a407964a13dc0cf9d977207`.
- Commit date: 25 November 2026, 20:38:07 UTC; message: `Lean proof of GRH`.
- Root Git tree: `5eb1240f03e791edd3fc7aa84a3a7d8dc3997b7f`.
- Immutable entry points: [Statements.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Statements.lean), [Main.lean](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Main.lean), [GUIDE.md](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/GUIDE.md), and [grh/README.md](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/README.md).

The public interface includes Mathlib's `RiemannHypothesis`, a written-out zeta zero statement, nonvanishing of Dirichlet L-functions to the right of one half with the principal-character exception at one, and critical-strip zero statements for all Dirichlet characters and for primitive characters. Thus the inspected GRH scope includes imprimitive Dirichlet characters. It does not assert general Artin or automorphic GRH.

The repository's readable documentation pins Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. It reports the standard three dependency axioms and independent exported-proof checks. Our work was source inspection: **no fresh upstream build, Lean kernel replay, exported-proof check, or new Lean formalization was performed**. The accompanying mathematical proof and exact Python checks have a separate verification scope.

The source analysis followed the determinant-versus-divisibility comparison, local twists, spanning estimates, and the one-sided prime-remainder argument. Relevant inspected paths include `New/Reduction/MainInequality.lean`, `New/Reduction/Lattices/TwistedLattice.lean`, `Lib/Analytic/Landau.lean`, `New/Reduction/Zeros/Criterion.lean`, and `New/Spanning/SecondMoment/PositiveType.lean`, all under `grh/src/`. The present paper transfers local coefficient-recovery ideas through the ProveIt branch packets. Its new theorem is unconditional and does not assume RH.

## 3. ProveIt snapshot and exact screening scope

- Repository: [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt).
- Commit: `4d7990202f9f106b2ffe8c209f073ad01d5e1987`.
- Commit date: 26 November 2026, 23:37:47 UTC; message: `New research report(s)`.
- Scope: [Analysis/GeneralizedRiemannHypothesis](https://github.com/VladimirReshetnikov/ProveIt/tree/4d7990202f9f106b2ffe8c209f073ad01d5e1987/Analysis/GeneralizedRiemannHypothesis).
- Git tree identifiers: `afe85c5d41d6de892a8eb3e5230497efd53e2551` for `Research`; `7343257914165a02ae27575744e200b86e853c9a` for `docs`.

The scoped collection contained 61 older unpacked packets and 39 newer ZIP packets. We screened **all 61 older delivery READMEs**, read **six relevant mathematical TEX sections in full**, and inspected text members of **seven selected newer ZIPs**. This is not a full mathematical review of all 100 packets. The repository's own scoped README says that placing the older packets there did not rebuild or independently review their claims and did not incorporate them into the root Lake build.

### Direct branch-recovery predecessors

Each path below is relative to `Analysis/GeneralizedRiemannHypothesis/Research/` at the pinned commit. Full immutable URLs and Git blob hashes are also in `source_manifest.json`.

| Path | Prior contribution relevant here | Git blob |
|---|---|---|
| [grh_transfers_cycle_signings_and_lubin_tate/lubin_tate.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/4d7990202f9f106b2ffe8c209f073ad01d5e1987/Analysis/GeneralizedRiemannHypothesis/Research/grh_transfers_cycle_signings_and_lubin_tate/lubin_tate.tex) | Sharp residue-field precision for clean branches; optimal directions; finite coefficient-precision formulation. | `93fcf9cf65cfcd2208a1c32eb7e478a365569597` |
| [grh_transfers_lubin_tate_and_graph_towers/branches.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/4d7990202f9f106b2ffe8c209f073ad01d5e1987/Analysis/GeneralizedRiemannHypothesis/Research/grh_transfers_lubin_tate_and_graph_towers/branches.tex) | Exact componentwise cutoffs, all-precision clean direction designs, inverse-pole computation, and eventual periodicity. | `50b914abc1d738fdeae53dd39296254461c6279a` |
| [grh_method_transfers_orthogonal_jets_2026-11-26/sections/jets.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/4d7990202f9f106b2ffe8c209f073ad01d5e1987/Analysis/GeneralizedRiemannHypothesis/Research/grh_method_transfers_orthogonal_jets_2026-11-26/sections/jets.tex) | Sharp higher-precision bounds, carry criteria, depth-one formulas, and explicit periods. | `1ed8f9ebfe7001c1c5a82798edd218215d22f514` |
| [grh_prime_patterns_and_branch_precision/branch_poles.tex](https://github.com/VladimirReshetnikov/ProveIt/blob/4d7990202f9f106b2ffe8c209f073ad01d5e1987/Analysis/GeneralizedRiemannHypothesis/Research/grh_prime_patterns_and_branch_precision/branch_poles.tex) | Higher coefficient precision and related binomial congruences. | `09c3931ed56c21c9dba60cf3cbd45de996737822` |

Two further sections were read to screen alternative directions: `grh_fixed_field_transfer_2026-11-25/sections/04_multivariate.tex` (fixed-field multivariate torsion selection; blob `90b91aec0992aa5d650f38fab68e73045c59d57d`) and `grh_transfer_synthesis_2026-11-25/sections/mean_pointwise.tex` (sharp mean-to-pointwise estimates; blob `b922e099e767a5e6f06327f1bf4c0c293f071dbe`).

The seven inspected newer ZIPs were:

1. `grh_new_results_2026-11-26.zip`
2. `orthogonal_nullity_and_prime_products.zip`
3. `symplectic_rank_blindness_2026-11-26.zip`
4. `sparse_grh_balanced_windows.zip`
5. `sparse_dirichlet_zero_tests.zip`
6. `grh_zero_certificates_2026-11-26.zip`
7. `rh_sampling_and_small_deviations_2026-11-26.zip`

These were selected to check overlap in recovery, rank, sparse tests, and exceptional-set arguments. In particular, the last packet already treats irregular sparse sampling, and `sparse_dirichlet_zero_tests.zip` has erasure-tolerant zero-test designs. The inspected text did not develop adversarial corruption of Lubin–Tate branch records.

## 4. Established ideas credited

- **Valuation orderings and integer-valued Newton bases:** Bhargava, [1997](https://doi.org/10.1515/crll.1997.490.101) and [2009](https://doi.org/10.1090/S0894-0347-09-00638-9). These are classical ingredients of the proof. The 2009 publication details were checked against the author's institutional record; its full AMS PDF was inaccessible during this search.
- **Fixed weighted-tree factorials and recursive merging:** Amini, [Logarithmic Tree Factorials](https://arxiv.org/abs/1611.02142), especially Theorem 2.7 in the [author text](https://www.math.ens.psl.eu/~amini/Publications/TreeFactorials.pdf). The fixed-tree recursion is credited to this framework.
- **Qualitative reduced Lubin–Tate recovery:** Berger–Sprang, [Integer-valued polynomials and p-adic Fourier theory, version 2](https://arxiv.org/abs/2502.18053v2), Lemmas 4.1–4.2, cited in the accompanying paper.
- **Removed orderings and related algorithms:** Johnson, [2010](https://www.numdam.org/item/10.5802/acirm.31.pdf), and Krachun–Mirgalimova, [2024](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v31i4p40/pdf/). Removing factors within a greedy product differs from choosing a fixed adversarial set of sample branches to delete. The paper gives an explicit three-branch comparison.
- **Ultrametric greedy structures and algorithms:** Grinberg–Petrov, [2021](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v28i3p6), and Gulati–Chakrabarti–Mittal, [2020](https://arxiv.org/abs/2011.10978), were included in the prior-art screen.
- **Error and erasure distance arguments:** these are standard coding theory. Quintin–Barbier–Chabot's [2013 work on generalized Reed–Solomon codes over rings](https://doi.org/10.1109/TIT.2013.2264797) is relevant background. Their subtractive evaluation-set case assumes unit differences. Reduced branches have nonunit differences, and their contact orders control the precision loss studied here.

## 5. Candidate novelty and its limits

The narrow proposed extension is the optimization over **which branches survive**, expressed by a dynamic program maximizing retained-leaf cardinality subject to a target-jet failure threshold. The paper derives the exact relative block distance, sharp error/erasure recovery criteria, and explicit ambiguity constructions from that optimization. It also exhibits a sixteen-branch case in which packing survivors into a largest residue ball does not produce the worst adversary.

Targeted searches combined `P-orderings`, `logarithmic tree factorials`, `Bhargava`, and `Lubin–Tate` with terms including `adversarial`, `erasures`, `removed`, `pruning`, `deletion`, `interdiction`, and `error correction`. We did not locate the exact proposed optimization in the screened corpus or the primary literature examined. This establishes the relationship to those sources, **not a guarantee of worldwide novelty or publication priority**. A specialist review may identify additional antecedents.

This archive contains original analysis, mathematical exposition, code, results, and source metadata. Upstream Lean files, research TEX files, and downloaded papers are not redistributed here.
