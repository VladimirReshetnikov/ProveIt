# Sub-exponential 3-SAT (the Exponential Time Hypothesis)

This project collects claims that 3-SAT, and more generally #k-SAT, can be
solved in time `2^{o(n)}` on `n` variables. Such an algorithm refutes the
**Exponential Time Hypothesis** (ETH) of Impagliazzo and Paturi: that some
`δ > 0` makes `O(2^{δn})`-time 3-SAT impossible. It also collects external
reports that analyse or refine one of those algorithms.

**Trust status.** Nothing here has been checked in ProveIt. No Lean or Rocq
development exists in this repository yet, so there are no `Lean/` or `Coq/`
directories. The manuscripts and packets are external research material,
filed as delivered. Their proofs, constants and verification claims are the
authors' own. The thirty-four packets below assume the unchanged arguments of the
OpenAI preprint. None of them claims an end-to-end SAT solver or a measured
speedup, and none was formalized.

## Primary manuscripts

| Manuscript | Date | Where | Claim |
|---|---|---|---|
| OpenAI, *The Exponential Time Hypothesis is False* | 25 October 2026 | vendored copy [`lib/openai-math/preprints/…/paper.pdf`](../../lib/openai-math/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf), with LaTeX sources in [`build/`](../../lib/openai-math/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex) and [provenance](../../lib/openai-math/preprints/PROVENANCE.md); upstream [`openai/math` preprint directory](https://github.com/openai/math/tree/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026) (67 pages) | A deterministic exact counter for satisfying assignments of a k-CNF. For each fixed `k ⩾ 2` it uses `poly_k(n, m)` space and runs in time `(n+m)^{O_k(1)} · 2^{n/(log n)^{1/2+o(1)}}`. Its Appendix D gives `(n+m)^{O_k(1)} · 2^{O_k(n log log n/√(log n))}` in general and `2^{O_{k,D}(n/√(log n))}` when `m ⩽ Dn`. |
| *A 2^{o(n)} time algorithm for 3-SAT*, credited to Claude (Anthropic) | 26 October 2026, 3:13 PM PT | [`Research/claude-2o-n-3sat/eth.pdf`](Research/claude-2o-n-3sat/eth.pdf) (49 pages) | A deterministic #k-SAT algorithm with time `2^{O(min{km/√(log m), k²·n·log log n/√(log n)})}`. Appendix E states `ETHIsFalse` and `MainTheorem` as Lean 4 propositions over Mathlib's multi-stack Turing machines. It reports proofs in a 1,881-file Lean 4.33.1 development, checked by the kernel, `leanchecker` and nanoda, with no axioms beyond the standard three. The PDF says the development's link is "to be added when a public location exists". It has since been published in [`anthropics/formal-math`](https://github.com/anthropics/formal-math); see [the Lean development of `eth.pdf`](#lean-development-of-ethpdf) below. The listing's comments cite the paper under the earlier title *The Exponential Time Hypothesis is False*. |

The OpenAI preprint directory is vendored unmodified under
[`lib/openai-math/preprints/`](../../lib/openai-math/preprints/PROVENANCE.md),
the repository's only vendored-code root. Its `PROVENANCE.md` gives the
upstream URL, the pinned commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`,
the fetch date and per-file Git blobs, and the Apache 2.0 `LICENSE`. The
delivered `paper.pdf` (887,884 bytes) is byte-identical to the vendored
[`paper.pdf`](../../lib/openai-math/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf).
It is therefore not filed here a second time.
[`Research/OMITTED.tsv`](Research/OMITTED.tsv) lists it and every other
omitted upstream copy.

**Upstream Lean.** `openai/math` also has a Lean development for this preprint
under `lean/OAI/Algorithms/SubexponentialSAT/` (3,977 files at `7ef5c0cc5c`).
Its scope page,
[`lean/docs/378.md`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/docs/378.md),
states a weaker bound than the manuscript:
`(L+1)^{O_k(1)} · 2^{O_k(n (log log n)²/√(log n))}` time on a canonically
encoded k-CNF of bit length `L`, in polynomial space. That development is not
vendored here.

### Lean development of `eth.pdf`

The Lean 4 formalization of *A 2^{o(n)} time algorithm for 3-SAT*, which
Appendix E of `eth.pdf` describes, is public in
[`anthropics/formal-math`](https://github.com/anthropics/formal-math).
It was added by pull request
[anthropics/formal-math#31](https://github.com/anthropics/formal-math/pull/31),
*Add eth: paper and Lean 4 formalization of "A 2^o(n) Time Algorithm for
3-SAT"*:

- Files and commit: the PR's changes at commit
  [`1a6eee293b9e00cb432eef6018a21f523623a9af`](https://github.com/anthropics/formal-math/pull/31/changes/1a6eee293b9e00cb432eef6018a21f523623a9af)
  (also
  [as a commit](https://github.com/anthropics/formal-math/commit/1a6eee293b9e00cb432eef6018a21f523623a9af)
  and as
  [the `eth/` tree at that commit](https://github.com/anthropics/formal-math/tree/1a6eee293b9e00cb432eef6018a21f523623a9af/eth)).
  The PR was merged into `main` on 2026-10-27 as merge commit `16a5ce4130`.
- Contents, as the PR describes them: `eth/` is a self-contained Lake project
  (Lean and Mathlib `v4.33.1`).
  - `MainResults.lean` states the two propositions on Mathlib's Turing
    machines: `ETHIsFalse` and the paper's main theorem.
  - `Solution.lean` proves both from the files under `proof/`.
  - `comparator.json` names them for Comparator.
  - The only two `sorry`s are in `Challenge.lean`, which states the theorems
    without proofs for that check.
  - `eth/README.md` says how to check everything.

  At the merge commit, `eth/` holds 1,062 files, 1,052 of them `.lean`.
- Its `eth/paper.pdf` (900,337 bytes, blob `77f4a8f043`) is a different
  revision from the `eth.pdf` filed here (868,673 bytes, blob `d2ad67d5b8`).

This development is linked, not vendored. Nothing in ProveIt builds or
checks it.

## Analysis and refinement packets

Every packet was prepared for Vladimir on 26 October 2026. Each one's source
manifest records the upstream paths and Git blob hashes it used. The packets
pin `openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` or
`42907c9e999cc00d6abe7a50bfc1023250edd1b9`; in the first round, the two marked
‡ pin the latter. The preprint directory is blob-for-blob identical at the two
commits, so every packet analyses the same text. Proofs are in natural
language, with exact finite checks in standard-library Python.

There are five rounds. The first seven packets work from the preprint alone.
The eight of the second round also review the first round and its placement
here, and they build on it. The five of the third round review all fifteen
earlier packets. They combine compatible ingredients, and they add the first
measured (kernel-level) speedups. The nine of the fourth round push the
coefficients further with adaptive partitions and contraction trees, and
the five of the fifth round use affine-plane geometry and pairwise
certificates.

### Round 1: proved refinements of the preprint's upper bounds

| Directory | Archive | Claim | Scope stated by the packet |
|---|---|---|---|
| [`cauchy_mode_improvement/`](Research/cauchy_mode_improvement/README.txt) | `cauchy_mode_improvement_2026-10-26.zip` | Replaces the contraction's geometric-series modes by a finite integral Cauchy separation, with certified mode weight `w_b = 1 + b + 2·v₂(b!) = 3b + 1 − 2·popcount(b)`. Leading logarithmic mode-enumeration counts drop by a factor of `1/√3`, with a correspondingly smaller explicit contraction upper-bound coefficient. [`report.pdf`](Research/cauchy_mode_improvement/report.pdf), 15 pages. | The order stays `poly(n,m) · 2^{O(n log log n/√(log n))}`. The comparison is between certified enumeration work and upper bounds, not SAT runtimes. `code/cauchy_modes.py` is a kernel prototype, not a solver. Novelty is not established. |
| [`eth_contraction_improvements/`](Research/eth_contraction_improvements/README.txt) | `eth_contraction_improvements.zip` | Three changes. (1) An exact count of tapered Hermite conditions takes `h` from about `3M/u` to `M/u`, and the precision allowance from `24MD/u` to `6MD/u`. (2) A revised schedule has base-2 coefficient 648.44… in the `s/√(log₂ s)` exponent, against 18,535.75… for the source schedule under the same analysis. (3) Streamed finite-difference packet extraction uses at most `2^L` grid evaluations instead of `exp(O(L log s))`, in polynomial space. [`report.pdf`](Research/eth_contraction_improvements/report.pdf), 15 pages; [`INTEGRATION.txt`](Research/eth_contraction_improvements/INTEGRATION.txt) maps each change to source labels. | The global orders do not improve: `2^{O_k(n log log n/√(log n))}` in general, and `2^{O_{k,D}(n/√(log n))}` at fixed clause density. The 648 against 18,535 comparison is between proved upper bounds, not measured times. This is not an independent proof of the ETH claim. |
| [`3sat_precision_refinement/`](Research/3sat_precision_refinement/README.md) ‡ | `3sat_precision_refinement_2026-10-26.zip` | Exact Hermite-condition counts and the exact two-adic recovery loss bring the dominant working precision from `(24+o(1))MD/u` to at most `(6+o(1))MD/u`. This halves the leading constant of the mode-enumeration bound. The real full-loss taper minimax problem is solved exactly. [`report.pdf`](Research/3sat_precision_refinement/report.pdf), 16 pages. | The logarithmic order is unchanged. A proposed structured-mode summation would give `2^{O(n log log n/log n)}` in general and `2^{O(n/log n)}` at fixed density, but it rests on a stated **unproved** algorithmic hypothesis. |
| [`sat_density_improvement/`](Research/sat_density_improvement/README.txt) | `sat_density_improvement.zip` | A density-aware exact counter in `poly_k(n,m) · 2^{O_k((n/√(log n)) · min{log(2+m/n), log log n})}`, with constants uniform in the density. At `m = Θ(n log log n)` the exponent improves from `O_k(n log log n/√(log n))` to `O_k(n log log log n/√(log n))`. It uses explicit Margulis–Gabber–Galil expanders, local codes and greedy elimination. [`density_aware_sat_improvement.pdf`](Research/sat_density_improvement/density_aware_sat_improvement.pdf), 13 pages; [`PROOF_STATUS.txt`](Research/sat_density_improvement/PROOF_STATUS.txt) lists imported and new results. | Neither the worst-case `n`-only exponent nor the fixed-density exponent improves. The constants are very large. The Margulis–Gabber–Galil spectral theorem is cited, not tested. The packet contains no tensor-contraction engine or full solver. |
| [`eth_density_refinement/`](Research/eth_density_refinement/README.txt) ‡ | `eth_density_refinement.zip` | For `m ⩽ Bn` with `1 ⩽ B ⩽ (log n)^A`, exact counting in `poly(n,m) · 2^{O(n log(2+B)/√(log n))}` time and polynomial space. At `B = Θ(log log n)` the exponent numerator improves from `n log log n` to `n log log log n`. Smaller Hermite precision budgets cut the matched leading mode-enumeration coefficient by a factor of 16. [`report.pdf`](Research/eth_density_refinement/report.pdf), 14 pages; [`integration_notes.txt`](Research/eth_density_refinement/integration_notes.txt) maps the changes to source lemmas. | The unrestricted worst-case exponent is unchanged, as is the `√(log n)` denominator. The factor 16 is between upper bounds, not a measured speedup. It overlaps `sat_density_improvement/` in result and method. Its `LICENSE-UPSTREAM.txt` is the upstream Apache 2.0 text. |

### Round 1: barriers and conditional proposals

| Directory | Archive | Claim | Scope stated by the packet |
|---|---|---|---|
| [`3sat_refinement/`](Research/3sat_refinement/README.md) | `3sat_refinement_package.zip` | For sparse degree-k parity tests, a scalar lift `E_i(z) = (1 + ∏(1 − 2m(z)))/2` is proved. Modulo `2^p` it leaves no incidence monomial of degree above `k(p+a−1)`; at `p = n+1` that is `k(n+a)`, against the source's `k(2n+a)`. A second contraction over compactly indexed mode tuples would give `2^{O_k(n (log log n)^{3/2}/log n)}`. [`3sat_refinement_report.pdf`](Research/3sat_refinement/3sat_refinement_report.pdf), 17 pages; [`data/research_status.json`](Research/3sat_refinement/data/research_status.json) separates proved, inherited and assumed results. | The leading bound stays `2^{O_k(n log log n/√(log n))}`. The stronger exponent needs a compact factorization that is **not supplied**; compacting index strings alone gives tensors with too many wires. |
| [`3sat_asymptotic_analysis/`](Research/3sat_asymptotic_analysis/README.md) | `3sat_asymptotic_analysis_20261027.zip` | **No stronger unrestricted bound is established.** It proves restricted barriers: weighted-budget tightening, taper retuning and Newton modes do not by themselves improve the exponent. Two **missing** interfaces are identified. A degree-preserving recursive interface would give `O(n √(log log n/log n))`; a uniform linear-wire compression interface would give `O(n/√(log n))`. [`report/report.pdf`](Research/3sat_asymptotic_analysis/report/report.pdf), 11 pages; [`research_decision/findings.md`](Research/3sat_asymptotic_analysis/research_decision/findings.md). | Neither interface is constructed. It includes three upstream Lean files in `audit/lean_selected/`, identified by `manifest.json`; they are not built. The bundled copy of the preprint and upstream README/license (`source/`) is omitted as byte-identical to upstream; `source/manifest.json` and the derived `source/paper.txt` are kept. |

### Round 2: sharper contraction coefficients

All eight second-round packets bound the preprint's normalized Boolean
tensor contraction. A root network has at most `s` wires, initial precision
and truncation order at most `s`, and maximum degree at most `⌈s^{9/10}⌉`. Each
packet bounds the time by `poly(s + description length) · 2^{(C+o(1)) s/√(log₂ s)}`
and states an explicit coefficient `C`. The common baselines are the first
round's 648.44… (`eth_contraction_improvements/`) and 374.38…, which is that
schedule combined with `cauchy_mode_improvement/`'s factorial modes. Every
packet states that `C` is per normalized wire, not per SAT variable, and that
the SAT order `n log log n/√(log n)` is unchanged. Archive arrivals:
`3e57705cf1`, and `d098ba436b` for `eth_matching_refinement/`.

| Directory | Archive | Claim | Scope stated by the packet |
|---|---|---|---|
| [`eth_asymmetric_packet_balancing/`](Research/eth_asymmetric_packet_balancing/README.txt) | `eth_asymmetric_packet_balancing_2026-10-26.zip` | `C = π·√(5/2)·(9+√3)/ln 2 = 76.90899…`, in polynomial space. It uses deterministic asymmetric pair-load balancing, near-unit packet padding, the fresh side's smaller recursive degree and a logarithmic precision buffer. These are added to the first round's Hermite precision and factorial Cauchy modes. A low-degree specialization (maximum degree at most `⌈s^{1/12}⌉`) gives 31.0641…. A separate annulus Cauchy basis has fixed-level slopes 4, 16/5, 64/21, 256/85, … tending to 3, so it gives no global gain. [`report.pdf`](Research/eth_asymmetric_packet_balancing/report.pdf), 18 pages; [`PROOF_STATUS.json`](Research/eth_asymmetric_packet_balancing/PROOF_STATUS.json), [`INTEGRATION.txt`](Research/eth_asymmetric_packet_balancing/INTEGRATION.txt). | Proofs were independently reviewed within the effort, and there is no Lean or Rocq build. The low-degree figure has stronger input assumptions. Its bundled upstream copies are omitted; `sources/upstream/PROVENANCE.txt` is kept. |
| [`3sat_round2_refinement/`](Research/3sat_round2_refinement/README.md) | `3sat_round2_refinement_20261027.zip` | `C = 84.06627…` (safe eventual 85) on `s/√⌈log₂ s⌉`. It uses a deterministic matching-potential packing lemma, a thin precision gap, an exact crossing fraction and a two-stage schedule. It adds an independent review and checker (`research_verification/`), an actual-domain rank gate (`research_frontier/`), and an audit of `eth.pdf` with scoped Heisenberg barriers (`research_alternate/`). [`report/report.pdf`](Research/3sat_round2_refinement/report/report.pdf), 15 pages. | The order is not smaller, and the conditional `n log log n/log n` target remains unproved. Its `evidence/` bundled 15 byte-identical copies of files already here: the OpenAI sources and license, `eth.pdf`, six placed report sources, this README, `OMITTED.tsv` and `PROVENANCE.md`. They are omitted. |
| [`eth_balanced_packing/`](Research/eth_balanced_packing/README.txt) | `eth_balanced_packing_2026-10-26.zip` | `C = 94.74820225953…`, in polynomial space. It uses a deterministic two-stage whole-vertex labeling with nearly equal pair-class loads, an additive logarithmic precision guard instead of the double taper, and an integer capacity schedule. [`report.pdf`](Research/eth_balanced_packing/report.pdf), 16 pages. | It makes no numerical comparison with `eth.pdf`, whose constant is unspecified. The eventual size thresholds are not practical. |
| [`eth_high_moment/`](Research/eth_high_moment/README.md) | `eth_high_moment_2026-10-26.zip` | `C = (9π/(4 ln 2))·√(15·log₂ 54) = 94.74820225953414…`. This is the same coefficient as `eth_balanced_packing/`, reached independently by higher-moment deterministic labeling and an additive precision gap. A polynomial-time orbit-padding alternative gives 98.8967…. Degree-sensitive specializations give 42.3727 (revised dense-query grouping) and 31.2365 (bounded-degree networks). [`report.pdf`](Research/eth_high_moment/report.pdf), 18 pages; [`INTEGRATION.md`](Research/eth_high_moment/INTEGRATION.md). | The specializations are network-budget coefficients, not coefficients in SAT variables. |
| [`eth_matching_refinement/`](Research/eth_matching_refinement/README.txt) | `ETH_Matching_Packing_Thin_Gaps_2026-10-27.zip` (dated 27 October) | `C = 94.74820225953415`, again the same coefficient. An exact-rational matching-potential packing argument reduces the label-class condition from `D_arr²·Δ` to `D_arr·Δ` up to polylogarithmic slack. Thin additive precision gaps allow larger retained interpolation ranges. [`report.pdf`](Research/eth_matching_refinement/report.pdf), 12 pages; [`qa/code_audit.md`](Research/eth_matching_refinement/qa/code_audit.md). | It claims no superiority over `eth.pdf`, whose constants are unspecified, and its thresholds are enormous. It reviewed only the first round, at ProveIt `770edf7756`. Its `sources/` snapshots of files already here are omitted; `sources/manifest.json` is kept. |
| [`eth_packet_refinement/`](Research/eth_packet_refinement/README.txt) | `eth_packet_refinement_2026-10-26.zip` | `C = 9π√22/(2 ln 2) = 95.66394…`. A two-stage labeling (greedy row balancing, then an exact exponential conditional potential) replaces the source's `D²Δ` packing scale by `DΔ` times logarithmic factors. Padding becomes `1+o(1)`, so the mode-family coefficient is 2 instead of 6, and an additive squared-log guard replaces `2·Σu_j`. [`report.pdf`](Research/eth_packet_refinement/report.pdf), 16 pages. | The fixed-density order `n/√(log n)` is also unchanged. Its bundled upstream copies, including `formalization_scope.md` (upstream `lean/docs/378.md`), are omitted. |
| [`eth_recursive_refinement/`](Research/eth_recursive_refinement/README.md) | `eth_recursive_refinement_2026-10-26.zip` | `C = 133.20737…`. It keeps the sharp padding bound and an additive precision guard. It also uses the missing residue class modulo 8 of the actual crossing rows to get a finite Cauchy basis with weight slope 64/21, above the prior 3. A lower-degree sparse-query corollary gives 60.70696…. [`report.pdf`](Research/eth_recursive_refinement/report.pdf), 17 pages. | The gain is asymptotic only. All 21 small mode inventories it samples favour the older basis, and it describes a polynomial-time choice between the two. |
| [`eth_joint_cauchy/`](Research/eth_joint_cauchy/README.txt) | `eth_joint_cauchy_2026-10-26.zip` | Full crossing-block Cauchy modes, with weights `a+1−i+4q−2·popcount(q)` at every valuation level, give `C = 319.68576…` (eventual 320) in polynomial space. A second algorithm, with cached group functions, block tables and Strassen multiplication, has time coefficient 225.59706…, but its space coefficient is 196.19945…. [`report.pdf`](Research/eth_joint_cauchy/report.pdf), 18 pages. | The Strassen variant spends subexponential space, so it is not polynomial-space. The Cauchy identity and Strassen are classical, and no priority claim is made beyond the reviewed corpus. |

### Round 3: combined schedules and exact kernels

Arrivals `f42479bca2` (three packets), `f898a9fde4` and `fa6e904d10`. The
five packets reviewed the repository at ProveIt `474ddba696`/`6d3adc4506`,
after round 2 was placed. They use the round-2
interface and the scale `s/√(log₂ s)` (`s/√⌈log₂ s⌉` for
`subsat_contraction_tree/`). They state that the SAT order is unchanged,
that the coefficients are per wire, and that no full solver is included.

| Directory | Archive | Claim | Scope stated by the packet |
|---|---|---|---|
| [`sat_adaptive_contraction/`](Research/sat_adaptive_contraction/README.md) | `sat_adaptive_contraction_2026-10-26.zip` | **Polynomial-space `C = 55.70948…`** (eventual 56) from streamed balanced recursive separators, the smallest polynomial-space claim. This lowers the composed `r=16` reference 66.1927… by the factor `√(17/24)`. Adaptive nine-group cached aggregation gives time 36.7503… with space coefficient 34.0242…. At root degree at most `⌈s^{1/12}⌉`, the cached figures are 15.392… time and 14.250… space. An exact modular Cauchy feature kernel measured 6.22–58.62× faster than a strengthened rational recurrence at the same cutoff. [`adaptive_sat_review.pdf`](Research/sat_adaptive_contraction/adaptive_sat_review.pdf), 19 pages. | The cached and low-degree branches have their own resource limits and premises. The kernel supports `(Z/2^p)[U]/(U²+U+1)` only. `code/reference_joint_cauchy.py` is an unchanged copy of `eth_joint_cauchy/code/joint_cauchy.py`, kept as a benchmark baseline. |
| [`sat_frontier_improvements/`](Research/sat_frontier_improvements/README.txt) | `sat_frontier_improvements_2026-10-26.zip` | Polynomial-space `C = 63.85741…` (eventual 64). In polynomial space it also gives 31.9287… at root degree at most `s^{3/5}`, and 26.9023… at degree at most `s^{1/12}`. A cached variant has time 38.4845… and space 34.2748…. Full Cauchy feature tables are built with quadratic rather than cubic ring work and one unit inversion; timings are in `results/benchmark_results.json`. [`report.pdf`](Research/sat_frontier_improvements/report.pdf), 21 pages; [`PROOF_STATUS.json`](Research/sat_frontier_improvements/PROOF_STATUS.json). | It claims no dominance over `eth.pdf`. `vendor/joint_cauchy.py` and `vendor/LICENSE.ProveIt` are unchanged copies of `eth_joint_cauchy/code/joint_cauchy.py` and the root `LICENSE`, kept because its checks load them. |
| [`subexponential_sat_frontier/`](Research/subexponential_sat_frontier/README.md) | `subexponential_sat_frontier_2026-10-26.zip` | Polynomial-space `C = 63.85220…` (eventual 64). A cached variant has time 37.930… and space coefficient 33.623…. It also gives an exact drop-in replacement for the asymmetric packet labeling, with scoring work `O(NQ³)` → `O(NQ²)` and identical outputs; it measured 1.50–9.56× faster on five fixtures. Precision peeling computes mode contributions at `P−V` bits and measured up to 14.34× on a synthetic kernel. [`report.pdf`](Research/subexponential_sat_frontier/report.pdf), 23 pages; [`PROOF_STATUS.json`](Research/subexponential_sat_frontier/PROOF_STATUS.json). | The cached schedule changes the memory guarantee. No global schedule optimality is claimed. The timings are subroutine measurements, not SAT timings. `code/reference_balanced_packing.py` is a byte copy of `eth_asymmetric_packet_balancing/code/balanced_packing.py`, kept because its code imports it. |
| [`subsat_contraction_tree/`](Research/subsat_contraction_tree/README.txt) | `subsat_contraction_tree_2026-10-26.zip` | Cached time `C_T = π√24339/(20 ln 2) = 35.3546…`, with space `C_S = π√915/(4 ln 2) = 34.2748…`, the smallest time coefficient claimed. It builds cached subset tables by binary construction and adds an exact CRT bridge to a matrix-multiplication backend with exponent below 12/5. A prefix-reuse kernel cuts Cauchy feature work from `O(L+PB²)` to `O(L+PB)`; it measured 101.95× on a 512-mode, 128-bit fixture. [`report/report.pdf`](Research/subsat_contraction_tree/report/report.pdf), 18 pages; [`CLAIMS.json`](Research/subsat_contraction_tree/CLAIMS.json), [`INTEGRATION.txt`](Research/subsat_contraction_tree/INTEGRATION.txt). | It uses subexponential space, so it is not a polynomial-space result. The fast matrix backend is imported theory and is not implemented. Its `LICENSE` is MIT-0. |
| [`subexponential_sat_kernel_improvements/`](Research/subexponential_sat_kernel_improvements/README.md) | `subexponential_sat_kernel_improvements_2026-10-26.zip` | Exact compositions of existing ingredients: polynomial-space 66.6051 (asymmetric packing with full-block Cauchy modes), and 44.5376 time / 39.4959 space with more memory. New exact kernels are an adaptive Smith-form separator for the actual crossing matrices (one sparse block has 260 feasible tuples against 3,013), Gray-code and antipodal streamed coefficient extraction, and a roots-of-unity projective filter. Kernel speedups of 2.16–7.86× were measured. [`report.pdf`](Research/subexponential_sat_kernel_improvements/report.pdf), 17 pages. | The compositions are comparison examples, not optima. The timings are kernel measurements. It names the density bound as the strongest SAT order in the corpus. `code/baseline_packet_extraction.py` is a byte copy of `eth_contraction_improvements/code/packet_extraction.py`, kept because its code imports it. Its `LICENSE` is MIT-0. |

### Round 4: adaptive partitions and contraction trees

Arrival `b9941a7396` (nine archives committed together). Seven packets
reviewed the round-3 placement (ProveIt `fd0edd17e6`…`dde01c4a63`). The two
marked † reviewed only through round 2 (`d098ba436b`/`474ddba696`). The
interface is the same, with degree at most `⌈s^{9/10}⌉` unless stated. Scale:
`s/√(log₂ s)`, or `s/√⌈log₂ s⌉` where marked ⌈⌉. All keep the SAT order
`n log log n/√(log n)`, and the conditional `n/log n` targets stay unproved.

| Directory | Archive | Claim | Scope stated by the packet |
|---|---|---|---|
| [`sat_adaptive_bounds/`](Research/sat_adaptive_bounds/README.txt) | `sat_adaptive_bounds_2026-10-26.zip` | **Polynomial-space `C = 46.18485…`** (from 55.709), the smallest polynomial-space claim, using adaptive streamed separators from complete binary linear flags. Cached: 34.32528… time, 34.02418… space. Cached at degree ≤ `⌈s^{1/12}⌉`: 13.37965… time, 13.25302… space. [`report.pdf`](Research/sat_adaptive_bounds/report.pdf), 22 pages. | Relative to the imported contraction identities; no solver or speedup is claimed. |
| [`sat_adaptive_tree_certificate/`](Research/sat_adaptive_tree_certificate/README.txt) | `sat_adaptive_tree_certificate_2026-10-26.zip` | **Cached `C_T = (π/ln 2)(√(128000/5103) + √(134144/41067)) = 30.89102…`** with `C_S = 32π√295/(81 ln 2) = 30.75391…` ⌈⌉, the smallest cached claim. It picks one of three contraction trees per pair-weight allocation, with a support-averaging certificate and a strict 9 → 13 → 7 schedule. [`report.pdf`](Research/sat_adaptive_tree_certificate/report.pdf), 15 pages. | It uses subexponential space; averaging and tree methods are classical. |
| [`sat_adaptive_frontier/`](Research/sat_adaptive_frontier/README.txt) | `sat_adaptive_frontier_2026-10-26.zip` | Adaptive quartet conditioning gives polynomial-space 50.30469…. Joint adaptive cached contraction gives time = space = 31.25240…. [`report.pdf`](Research/sat_adaptive_frontier/report.pdf), 22 pages; [`PROOF_STATUS.json`](Research/sat_adaptive_frontier/PROOF_STATUS.json). | Its reference composition is 55.40467 (polynomial) and 35.355/34.275 (cached). |
| [`sat_adaptive_matrix_partition/`](Research/sat_adaptive_matrix_partition/README.txt) | `sat_adaptive_matrix_partition_2026-10-26.zip` | Polynomial-space 50.21043… from an optimal balanced sixteen-group separator tree (14,827 DP states). Cached 34.32528… / 34.02418…, the same pair as `sat_adaptive_bounds/`, found independently via a three-triple partition. [`report.pdf`](Research/sat_adaptive_matrix_partition/report.pdf), 18 pages. | No SAT speedup was measured; the fast matrix backend is theoretical. |
| [`subexponential_sat_adaptive_four/`](Research/subexponential_sat_adaptive_four/README.txt) | `subexponential_sat_adaptive_four_2026-10-26.zip` | Cached 32.91581… / 31.66171… (32.85635… / 31.46748… with a 19/8 matrix backend). Polynomial-space 50.39373…. It gives a sharp local three-matching inequality with constant `√(244/75)`. [`report.pdf`](Research/subexponential_sat_adaptive_four/report.pdf), 18 pages. | Upper-bound comparisons, not runtimes. |
| [`subsat_rectangular/`](Research/subsat_rectangular/README.md) | `subsat_rectangular_2026-10-26.zip` | Polynomial-space 53.97753… ⌈⌉ by multistage streamed conditioning. Rectangular cached contraction gives 33.99389… / 33.99372… ⌈⌉. It also proves precision barriers, for example that asymmetric Hermite multiplicities cannot help. [`report.pdf`](Research/subsat_rectangular/report.pdf), 26 pages. | No practical SAT speedup is claimed. |
| [`eth_adaptive_exact_kernels/`](Research/eth_adaptive_exact_kernels/README.txt) | `ETH_Adaptive_Exact_Kernels_2026-10-27.zip` (dated 27 October) | Polynomial-space 55.33162…, and 25.16377… at degree ≤ `⌈s^{0.51}⌉`. Cached CRT/contraction tree gives 35.07061… / 33.99950…, with a lower-memory 37.32461… / 33.62304…. Sparse-support scoring measured 1.53–2.73×, and fused Cauchy transitions 1.46–2.29× (`(5N²+N)/2` → `N²+N` products). [`report.pdf`](Research/eth_adaptive_exact_kernels/report.pdf), 26 pages. | Small cases regress, and sparse balancing is pseudo-polynomial for binary edge weights. Its 58 `sources/` snapshots of packets already filed here are omitted. |
| [`3sat_round3_frontier/`](Research/3sat_round3_frontier/README.md) † | `3sat_round3_frontier_20261027.zip` | Polynomial-space 63.75736… ⌈⌉, and **23.66617… at degree ≤ `⌈s^{1/12}⌉`**, the smallest low-degree polynomial-space claim. Cached 37.93011… / 33.62304…; low-degree cached 14.23919… / 12.36130…. Centered antipodal extraction measured 1.56–2.30× and the cube-root filter 2.71–3.00×. [`report/report.pdf`](Research/3sat_round3_frontier/report/report.pdf), 20 pages. | Its 26 `evidence/` copies of files already here are omitted. Prior code is kept as inert `.py.txt`. |
| [`eth_adaptive_schedules/`](Research/eth_adaptive_schedules/README.txt) † | `eth_adaptive_schedules_2026-10-26.zip` | Polynomial-space 63.78117…; cached 37.59170… / 33.62304…. An exact incremental matching-potential kernel goes from `O(VMQ³)` to `O(MQ² + VQ)` with an identical deterministic output. [`report.pdf`](Research/eth_adaptive_schedules/report.pdf), 22 pages. | Its benchmarks are synthetic graph-packing inputs. |

### Round 5: affine-plane geometry and pairwise certificates

Arrival `26bd83d4b3`. The five packets reviewed the round-4 placement
(ProveIt `73dfb5e5ab`…`7de9d09fec`), and several cite the
`anthropics/formal-math` Lean development. All five improve only the cached
(subexponential-space) branch, except one low-degree polynomial-space
schedule. Generic polynomial space stays at 46.185. Scale: `s/√⌈log₂ s⌉`
unless marked `√log₂`.

| Directory | Archive | Claim | Scope stated by the packet |
|---|---|---|---|
| [`sat_pairwise_certificates/`](Research/sat_pairwise_certificates/README.txt) | `sat_pairwise_certificates_2026-10-26.zip` | **Cached time = space `C = (π/ln 2)√(15952347164548384057/368725000000000000) = 29.81161…`**, the smallest cached time, from a weighted norm-coupled pair-support certificate. **Polynomial space at degree ≤ `⌈s^{1/12}⌉`: 16.81223…** (from 23.666) via a streamed 32 → 16 → 8 → 4 schedule. It proves two obstructions: the flag coefficient is optimal over binary separator trees in its entropy model, and a finite rank obstruction rules out thinner graded spaces. It includes a conservative bounded-density CNF translation. [`report.pdf`](Research/sat_pairwise_certificates/report.pdf), 21 pages. | The worst-case order is unchanged, and the coefficients are per wire. |
| [`sat_affine_contraction/`](Research/sat_affine_contraction/README.md) | `sat_affine_contraction_2026-10-26.zip` | Cached 30.25704… time / **25.98907… space**, the smallest cached space. Four affine-plane partitions give local time coefficient `1/√3`, and a joint selector gives storage coefficient `√(7/27)`; the schedule is 9 → 12 → 9 → 7 → 4. [`report.pdf`](Research/sat_affine_contraction/report.pdf), 16 pages. | Time and space both stay subexponential. |
| [`sat_affine_geometry/`](Research/sat_affine_geometry/README.txt) | `sat_affine_geometry_2026-10-26.zip` | Cached `C_T = (π/ln 2)(√(128000/5103) + √(21920/7857)) = 30.26987…`, with `C_S = (π/ln 2)√(8000/189) = 29.48754…` (`√log₂`). It uses a four-plan affine-plane menu, a twelve-group menu and punctured menus. The Toeplitz packet kernel has a mixed record: full-grid loses and parity-strided wins at the largest sizes, and the raw results are kept. [`report.pdf`](Research/sat_affine_geometry/report.pdf), 21 pages. | No Lean rebuild was done. Seven delivered LaTeX/Python build byproducts are not filed (see placement record). |
| [`sat_affine_cauchy/`](Research/sat_affine_cauchy/README.txt) | `sat_affine_cauchy_2026-10-26.zip` | Cached 30.41335… / 29.46603…, from the four parallel classes of `F₃²`, thirteen cyclic plans and a 9 → 13 → 9 → 6 → … recursion. Guarded fast Cauchy feature transforms reduce to one convolution for odd nodes; the product-tree prototype is slower at small sizes, and the odd-node path is faster on all five measurements. It also proves an obstruction to an immediate sparse-oscillator route. [`report.pdf`](Research/sat_affine_cauchy/report.pdf), 23 pages. | Its conditional growth-rate route claims no smaller-order algorithm. |
| [`sat_affine_plane/`](Research/sat_affine_plane/README.txt) | `sat_affine_plane_2026-10-26.zip` | Cached 30.69134… / 29.46603… (`√log₂`), using the `F₃²` parallel-line partitions (support coefficient exactly `1/√3`) and a four-plan certificate on 13 groups. [`report.pdf`](Research/sat_affine_plane/report.pdf), 23 pages. | It does not improve polynomial space. It records that the published `anthropics/formal-math` evidence was retrieved, not rebuilt. |

## Strongest claimed improvements over the OpenAI preprint

This summary comes from each packet's README and status files. ProveIt has
checked none of it. The baseline is the preprint's Appendix D:
`2^{O_k(n log log n/√(log n))}` in the worst case and `2^{O_{k,D}(n/√(log n))}`
at fixed clause density.

**Strongest proved claim: an improvement in one density regime, not in the
worst case.** Two packets claim it independently:

- [`sat_density_improvement/`](Research/sat_density_improvement/README.txt)
  claims `poly_k(n,m) · 2^{O_k((n/√(log n)) · min{log(2+m/n), log log n})}`.
- [`eth_density_refinement/`](Research/eth_density_refinement/README.txt)
  claims essentially the same bound, `2^{O(n log(2+B)/√(log n))}` for `m ⩽ Bn`
  with `B ⩽ (log n)^A`.

At `m = Θ(n log log n)` the exponent drops from `n log log n/√(log n)` to
`n log log log n/√(log n)`. The gain appears only when the density `B` tends to
infinity with `log B = o(log log n)`. Neither packet changes the worst-case
exponent or the fixed-density exponent.

**Proved improvements of constants only.** Each comparison below is between
upper bounds, not measured runtimes. The contraction coefficient `C` in
`2^{(C+o(1)) s/√(log₂ s)}` has been driven down over three rounds. The
figures are per normalized wire `s`, at the general degree bound
`⌈s^{9/10}⌉`. In polynomial space:

| Coefficient `C` | Packet | Note |
|---:|---|---|
| 18,535.75… | source schedule, as analysed by `eth_contraction_improvements/` | the baseline |
| 648.44… | [`eth_contraction_improvements/`](Research/eth_contraction_improvements/README.txt) | round 1, about 28.6× below the baseline |
| 374.38… | 648.44 schedule + [`cauchy_mode_improvement/`](Research/cauchy_mode_improvement/README.txt) modes | composition computed in round 2 |
| 319.69… | [`eth_joint_cauchy/`](Research/eth_joint_cauchy/README.txt) | |
| 133.21… | [`eth_recursive_refinement/`](Research/eth_recursive_refinement/README.md) | |
| 95.66… | [`eth_packet_refinement/`](Research/eth_packet_refinement/README.txt) | |
| 94.748… | [`eth_balanced_packing/`](Research/eth_balanced_packing/README.txt), [`eth_high_moment/`](Research/eth_high_moment/README.md), [`eth_matching_refinement/`](Research/eth_matching_refinement/README.txt) | the same value, found by three packets independently |
| 84.07… | [`3sat_round2_refinement/`](Research/3sat_round2_refinement/README.md) | on `s/√⌈log₂ s⌉` |
| 76.909… | [`eth_asymmetric_packet_balancing/`](Research/eth_asymmetric_packet_balancing/README.txt) | round 2's best, `π√(5/2)(9+√3)/ln 2` |
| 66.605… | [`subexponential_sat_kernel_improvements/`](Research/subexponential_sat_kernel_improvements/README.md) | asymmetric packing + full-block Cauchy modes, a composition |
| 66.193… | composed `r=16` reference computed by `sat_adaptive_contraction/` | a composition at its parameter boundary |
| 63.857… | [`sat_frontier_improvements/`](Research/sat_frontier_improvements/README.txt) | |
| 63.852… | [`subexponential_sat_frontier/`](Research/subexponential_sat_frontier/README.md) | |
| 63.781… / 63.757… | [`eth_adaptive_schedules/`](Research/eth_adaptive_schedules/README.txt), [`3sat_round3_frontier/`](Research/3sat_round3_frontier/README.md) | round 4, reviewed only through round 2 |
| 55.709… | [`sat_adaptive_contraction/`](Research/sat_adaptive_contraction/README.md) | round 3's best, `√(17/24)` × 66.193 |
| 55.405… | compatible composition computed by `sat_adaptive_frontier/`, `subsat_rectangular/` | |
| 55.332… | [`eth_adaptive_exact_kernels/`](Research/eth_adaptive_exact_kernels/README.txt) | |
| 53.978… | [`subsat_rectangular/`](Research/subsat_rectangular/README.md) | on `s/√⌈log₂ s⌉` |
| 50.394… / 50.305… / 50.210… | [`subexponential_sat_adaptive_four/`](Research/subexponential_sat_adaptive_four/README.txt), [`sat_adaptive_frontier/`](Research/sat_adaptive_frontier/README.txt), [`sat_adaptive_matrix_partition/`](Research/sat_adaptive_matrix_partition/README.txt) | |
| **46.185…** | [`sat_adaptive_bounds/`](Research/sat_adaptive_bounds/README.txt) | **the smallest polynomial-space claim**, about 401× below the baseline |

With subexponential space (`2^{(C_S+o(1)) s/√(log₂ s)}`), the time
coefficients are smaller:

| Time `C_T` | Space `C_S` | Packet |
|---:|---:|---|
| 225.60… | 196.20… | [`eth_joint_cauchy/`](Research/eth_joint_cauchy/README.txt) (Strassen variant) |
| 44.538… | 39.496… | [`subexponential_sat_kernel_improvements/`](Research/subexponential_sat_kernel_improvements/README.md) (composition) |
| 38.484… | 34.275… | [`sat_frontier_improvements/`](Research/sat_frontier_improvements/README.txt) |
| 37.930… | 33.623… | [`subexponential_sat_frontier/`](Research/subexponential_sat_frontier/README.md) |
| 37.592… | 33.623… | [`eth_adaptive_schedules/`](Research/eth_adaptive_schedules/README.txt) |
| 37.325… | 33.623… | [`eth_adaptive_exact_kernels/`](Research/eth_adaptive_exact_kernels/README.txt) (lower-memory variant) |
| 36.750… | 34.024… | [`sat_adaptive_contraction/`](Research/sat_adaptive_contraction/README.md) |
| 35.355… | 34.275… | [`subsat_contraction_tree/`](Research/subsat_contraction_tree/README.txt), round 3's best, on `s/√⌈log₂ s⌉`, with an imported fast-matrix backend |
| 35.071… | 34.000… | [`eth_adaptive_exact_kernels/`](Research/eth_adaptive_exact_kernels/README.txt) |
| 34.325… | 34.024… | [`sat_adaptive_bounds/`](Research/sat_adaptive_bounds/README.txt), [`sat_adaptive_matrix_partition/`](Research/sat_adaptive_matrix_partition/README.txt), the same pair found independently |
| 33.994… | 33.994… | [`subsat_rectangular/`](Research/subsat_rectangular/README.md), on `s/√⌈log₂ s⌉` |
| 32.916… | 31.662… | [`subexponential_sat_adaptive_four/`](Research/subexponential_sat_adaptive_four/README.txt) (32.856 / 31.467 with a 19/8 backend) |
| 31.252… | 31.252… | [`sat_adaptive_frontier/`](Research/sat_adaptive_frontier/README.txt) |
| 30.891… | 30.754… | [`sat_adaptive_tree_certificate/`](Research/sat_adaptive_tree_certificate/README.txt), round 4's best, on `s/√⌈log₂ s⌉` |
| 30.691… | 29.466… | [`sat_affine_plane/`](Research/sat_affine_plane/README.txt) |
| 30.413… | 29.466… | [`sat_affine_cauchy/`](Research/sat_affine_cauchy/README.txt), on `s/√⌈log₂ s⌉` |
| 30.270… | 29.488… | [`sat_affine_geometry/`](Research/sat_affine_geometry/README.txt) |
| 30.257… | **25.989…** | [`sat_affine_contraction/`](Research/sat_affine_contraction/README.md), **the smallest cached space**, on `s/√⌈log₂ s⌉` |
| **29.812…** | 29.812… | [`sat_pairwise_certificates/`](Research/sat_pairwise_certificates/README.txt), **the smallest cached time**, on `s/√⌈log₂ s⌉` |

Low-degree networks have smaller coefficients under stronger input
assumptions. In polynomial space, the smallest is `sat_pairwise_certificates/`'s
**16.812** at maximum degree `⌈s^{1/12}⌉`. The others are:
- `3sat_round3_frontier/`: 23.666 at `⌈s^{1/12}⌉`;
- `eth_adaptive_exact_kernels/`: 25.164 at `⌈s^{0.51}⌉`;
- `sat_frontier_improvements/`: 26.902 at `s^{1/12}` and 31.929 at `s^{3/5}`;
- `eth_asymmetric_packet_balancing/`: 31.064 at `⌈s^{1/12}⌉`;
- `eth_high_moment/`: 31.236 at bounded degree.

With subexponential space at `⌈s^{1/12}⌉`, `sat_adaptive_bounds/` gives
**13.380** time / 13.253 space and `3sat_round3_frontier/` gives 14.239 /
**12.361**. Before them, `sat_adaptive_contraction/` gave 15.392 / 14.250.

Other first-round constant gains: `eth_density_refinement/` divides its
leading mode-enumeration coefficient by 16;
[`3sat_precision_refinement/`](Research/3sat_precision_refinement/README.md)
takes the working precision from `24MD/u` to `6MD/u`;
`cauchy_mode_improvement/` gives the mode-count ratio `1/√3`.

None of these coefficients converts directly into a constant per SAT
variable. That needs the encoding's wire constant, which no packet supplies.

**Measured speedups (round 3, kernels only).** These are the corpus's first
timings. Each one compares a subroutine against the earlier code, not SAT
solve times:

- packet labeling, 1.50–9.56× (`subexponential_sat_frontier/`);
- precision peeling, up to 14.34× (`subexponential_sat_frontier/`);
- streamed and projective coefficient extraction, 2.16–7.86×
  (`subexponential_sat_kernel_improvements/`);
- prefix-reused Cauchy features, 101.95× at 512 modes (`subsat_contraction_tree/`);
- modular Cauchy feature tables, 6.22–58.62× against a strengthened rational
  recurrence (`sat_adaptive_contraction/`);
- round 4: centered antipodal extraction 1.56–2.30× and a cube-root filter
  2.71–3.00× (`3sat_round3_frontier/`); sparse-support scoring 1.53–2.73× and
  fused Cauchy transitions 1.46–2.29× (`eth_adaptive_exact_kernels/`). Some
  small cases regress.

**Strongest claim of all, conditional on an unproved step.**
[`3sat_precision_refinement/`](Research/3sat_precision_refinement/README.md)
claims that a structured-mode summation method would give
`2^{O(n log log n/log n)}` in general and `2^{O(n/log n)}` at fixed density,
replacing `√(log n)` in the denominator by `log n`. The method rests on a
missing algorithm, which the packet states as an unproved hypothesis. The
other conditional proposals are weaker:

- [`3sat_refinement/`](Research/3sat_refinement/README.md) proposes
  `n (log log n)^{3/2}/log n`. It needs a compact factorization that the packet
  does not supply.
- [`3sat_asymptotic_analysis/`](Research/3sat_asymptotic_analysis/README.md)
  derives `n √(log log n/log n)` and `n/√(log n)` from two interfaces that it
  calls missing. It concludes that no stronger unrestricted bound is
  established.

[`eth.pdf`](Research/claude-2o-n-3sat/eth.pdf) is a separate manuscript, not a
refinement of the OpenAI preprint. Its `n`-bound, `k² n log log n/√(log n)`,
has the same order as the preprint's Appendix D.

All the conditional routes target the `√(log n)` denominator. The barrier
results of `3sat_asymptotic_analysis/` say that retuning the existing
parameters (weighted budgets, taper, Newton modes) cannot remove it. A real
order improvement therefore needs new structure, not better constants. The
second to fifth rounds confirm this: their twenty-seven packets improve only `C`
and kernel costs, and none closes a missing interface of the conditional
proposals.

## Placement record

- Arrivals. The drop process staged the first five files (three packets,
  `eth.pdf`, `paper.pdf`) without committing them. They were committed
  unchanged in `a505bd768b`. It committed the other four packets itself in
  `64b3202ee8` and `8afdbbea48`. Every archive remains recoverable from its
  arrival commit after its removal from `docs/incoming/`.
- Each archive was extracted into its own empty scratch directory outside the
  repository. Its inner directory (for `3sat_asymptotic_analysis`, its root)
  is filed unchanged under `Research/`. The file counts, in table order, are
  17, 15, 16, 9, 15, 12 and 35.
- Every filed file matched its packet's own checksum manifest before filing.
  In `3sat_asymptotic_analysis/MANIFEST.sha256.json`, only the omitted
  `source/` entries have no file.
- Omitted: the eight `source/` copies of upstream files listed in
  [`Research/OMITTED.tsv`](Research/OMITTED.tsv), and five delivered
  `SHA256SUMS`/`SHA256SUMS.txt` ledgers. The root `.gitignore` excludes those
  ledgers by repository policy. They were checked before omission and remain
  in the arrival archives. The other checksum manifests (`CHECKSUMS.sha256`,
  `MANIFEST.sha256`, `MANIFEST.sha256.json`) are filed as delivered.
- Two delivered CSV files have CRLF line endings:
  `cauchy_mode_improvement/results/mode_counts.csv` and
  `3sat_precision_refinement/results/exponent_scales.csv`. The root
  `.gitattributes` marks them `-text`, so they stay byte for byte as
  delivered.
- `eth.pdf` is filed as `Research/claude-2o-n-3sat/eth.pdf`.
- Round 2. The drop process committed seven archives in `3e57705cf1` and an
  eighth in `d098ba436b`. Their inner directories are filed with the date
  suffix dropped from the directory name. The file counts, in table order, are
  28, 48, 22, 21, 24, 20, 24 and 26. 39 members are not filed:
  - three `SHA256SUMS` ledgers (repository policy);
  - 36 members byte-identical to files at ProveIt `ab2fbc9e03`/`d098ba436b`
    or upstream `7ef5c0cc5c`, listed in `OMITTED.tsv` with the commit they
    match. Among them are round 2's copies of this README and of
    `OMITTED.tsv`.
- Every delivered file of round 2 matched its packet's checksum manifest
  (`MANIFEST.sha256`, `MANIFEST.sha256.json`, `MANIFEST.json`, or the dropped
  `SHA256SUMS` ledgers). Every filed file is byte-identical to its archive
  member. Three more CRLF CSV files are marked `-text`:
  `eth_joint_cauchy/results/mode_count_comparison.csv` and
  `eth_recursive_refinement/results/{comparison_coefficients,mode_counts}.csv`.
  The four `eth_matching_refinement/qa/*.log` audit logs are force-added,
  because the root `.gitignore` ignores `*.log`.
- Correction made with round 3: the round-2 placement had omitted
  `3sat_round2_refinement/scripts/build_report.sh` and
  `negative_integrity_controls.py` as duplicates. That packet's
  `replay_archive.py` and README run them, so both are now restored from
  `3e57705cf1` and removed from `OMITTED.tsv`. Duplicated `.py`/`.sh` files are
  now always kept.
- Round 3. The drop process committed three archives in `f42479bca2` and one
  each in `f898a9fde4` and `fa6e904d10`. In table order they are filed with
  50, 37, 48, 37 and 58 files, nothing omitted. Every file matched its
  packet's manifest (`MANIFEST.sha256.json`, `MANIFEST.sha256`,
  `MANIFEST.json`, `provenance/artifact_manifest.json`) and is byte-identical
  to its archive member. Five CRLF CSV files are marked `-text`.
  `subsat_contraction_tree/results/report_build.log` is force-added past the
  `*.log` rule.
- Round 4. Nine archives were staged by the drop process and committed
  unchanged at Vladimir's request in `b9941a7396`. In table order they are
  filed with 30, 43, 39, 35, 35, 40, 93, 89 and 39 files. 85 members are not
  filed:
  - one `SHA256SUMS` ledger;
  - 84 byte-identical copies of files at ProveIt `73dfb5e5ab` or upstream,
    listed in `OMITTED.tsv`. They are 58 `sources/` snapshots of
    `eth_adaptive_exact_kernels/` and 26 `evidence/` copies of
    `3sat_round3_frontier/`.
- Duplicated `.py`/`.sh` files of round 4 are kept. Five CRLF tables are
  marked `-text`, and seven delivered `.log` files are force-added. At
  Vladimir's request, round 4 had no separate manifest or omission recheck
  beyond the blob-identity test that decides each omission.
- Round 5. The drop process committed five archives in `26bd83d4b3`. In table
  order they are filed with 32, 30, 57, 50 and 44 files. Not filed:
  - one `SHA256SUMS` ledger;
  - `sat_affine_geometry/provenance/closing-Computability_SubexponentialSAT_README.md`,
    a byte copy of this README at `d86bd7259c` (in `OMITTED.tsv`);
  - seven delivered build byproducts of `sat_affine_geometry/`: `report.aux`,
    `.fdb_latexmk`, `.fls`, `.log`, `.out`, `.toc` and
    `code/__pycache__/portfolios.cpython-312.pyc`. These are generated files
    that the repository keeps out of history, and they remain in the
    arrival archive.
  Six delivered `results/*.log` build records are force-added. Three CRLF
  CSV files are marked `-text`. As in round 4, no separate manifest, omission
  or link recheck was run.
- No supplied script, test, Makefile or LaTeX build was run.
