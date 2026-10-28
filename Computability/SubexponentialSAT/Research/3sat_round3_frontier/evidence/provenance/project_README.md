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
authors' own. The seven packets below assume the unchanged arguments of the
OpenAI preprint. None of them claims an end-to-end SAT solver or a measured
speedup, and none was formalized.

## Primary manuscripts

| Manuscript | Date | Where | Claim |
|---|---|---|---|
| OpenAI, *The Exponential Time Hypothesis is False* | 25 October 2026 | vendored copy [`lib/openai-math/preprints/…/paper.pdf`](../../lib/openai-math/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf), with LaTeX sources in [`build/`](../../lib/openai-math/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex) and [provenance](../../lib/openai-math/preprints/PROVENANCE.md); upstream [`openai/math` preprint directory](https://github.com/openai/math/tree/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026) (67 pages) | A deterministic exact counter for satisfying assignments of a k-CNF. For each fixed `k ⩾ 2` it uses `poly_k(n, m)` space and runs in time `(n+m)^{O_k(1)} · 2^{n/(log n)^{1/2+o(1)}}`. Its Appendix D gives `(n+m)^{O_k(1)} · 2^{O_k(n log log n/√(log n))}` in general and `2^{O_{k,D}(n/√(log n))}` when `m ⩽ Dn`. |
| *A 2^{o(n)} time algorithm for 3-SAT*, credited to Claude (Anthropic) | 26 October 2026, 3:13 PM PT | [`Research/claude-2o-n-3sat/eth.pdf`](Research/claude-2o-n-3sat/eth.pdf) (49 pages) | A deterministic #k-SAT algorithm with time `2^{O(min{km/√(log m), k²·n·log log n/√(log n)})}`. Appendix E states `ETHIsFalse` and `MainTheorem` as Lean 4 propositions over Mathlib's multi-stack Turing machines. It reports proofs in a 1,881-file Lean 4.33.1 development, checked by the kernel, `leanchecker` and nanoda, with no axioms beyond the standard three. The development has not been published: its link is "to be added when a public location exists". The listing's comments cite the paper under the earlier title *The Exponential Time Hypothesis is False*. |

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

## Analysis and refinement packets

Every packet was prepared for Vladimir on 26 October 2026. None redistributes
the preprint, except where noted. Each `source_manifest.json` records the
upstream paths and Git blob hashes the packet used. Five packets pin
`openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`; the two marked ‡ pin
`42907c9e999cc00d6abe7a50bfc1023250edd1b9`. The preprint directory is
blob-for-blob identical at the two commits, so all seven analyse the same
text. Proofs are in natural language, with exact finite checks in
standard-library Python.

### Proved refinements of the preprint's upper bounds

| Directory | Archive | Claim | Scope stated by the packet |
|---|---|---|---|
| [`cauchy_mode_improvement/`](Research/cauchy_mode_improvement/README.txt) | `cauchy_mode_improvement_2026-10-26.zip` | Replaces the contraction's geometric-series modes by a finite integral Cauchy separation, with certified mode weight `w_b = 1 + b + 2·v₂(b!) = 3b + 1 − 2·popcount(b)`. Leading logarithmic mode-enumeration counts drop by a factor of `1/√3`, with a correspondingly smaller explicit contraction upper-bound coefficient. [`report.pdf`](Research/cauchy_mode_improvement/report.pdf), 15 pages. | The order stays `poly(n,m) · 2^{O(n log log n/√(log n))}`. The comparison is between certified enumeration work and upper bounds, not SAT runtimes. `code/cauchy_modes.py` is a kernel prototype, not a solver. Novelty is not established. |
| [`eth_contraction_improvements/`](Research/eth_contraction_improvements/README.txt) | `eth_contraction_improvements.zip` | Three changes. (1) An exact count of tapered Hermite conditions takes `h` from about `3M/u` to `M/u`, and the precision allowance from `24MD/u` to `6MD/u`. (2) A revised schedule has base-2 coefficient 648.44… in the `s/√(log₂ s)` exponent, against 18,535.75… for the source schedule under the same analysis. (3) Streamed finite-difference packet extraction uses at most `2^L` grid evaluations instead of `exp(O(L log s))`, in polynomial space. [`report.pdf`](Research/eth_contraction_improvements/report.pdf), 15 pages; [`INTEGRATION.txt`](Research/eth_contraction_improvements/INTEGRATION.txt) maps each change to source labels. | The global orders do not improve: `2^{O_k(n log log n/√(log n))}` in general, and `2^{O_{k,D}(n/√(log n))}` at fixed clause density. The 648 against 18,535 comparison is between proved upper bounds, not measured times. This is not an independent proof of the ETH claim. |
| [`3sat_precision_refinement/`](Research/3sat_precision_refinement/README.md) ‡ | `3sat_precision_refinement_2026-10-26.zip` | Exact Hermite-condition counts and the exact two-adic recovery loss bring the dominant working precision from `(24+o(1))MD/u` to at most `(6+o(1))MD/u`. This halves the leading constant of the mode-enumeration bound. The real full-loss taper minimax problem is solved exactly. [`report.pdf`](Research/3sat_precision_refinement/report.pdf), 16 pages. | The logarithmic order is unchanged. A proposed structured-mode summation would give `2^{O(n log log n/log n)}` in general and `2^{O(n/log n)}` at fixed density, but it rests on a stated **unproved** algorithmic hypothesis. |
| [`sat_density_improvement/`](Research/sat_density_improvement/README.txt) | `sat_density_improvement.zip` | A density-aware exact counter in `poly_k(n,m) · 2^{O_k((n/√(log n)) · min{log(2+m/n), log log n})}`, with constants uniform in the density. At `m = Θ(n log log n)` the exponent improves from `O_k(n log log n/√(log n))` to `O_k(n log log log n/√(log n))`. It uses explicit Margulis–Gabber–Galil expanders, local codes and greedy elimination. [`density_aware_sat_improvement.pdf`](Research/sat_density_improvement/density_aware_sat_improvement.pdf), 13 pages; [`PROOF_STATUS.txt`](Research/sat_density_improvement/PROOF_STATUS.txt) lists imported and new results. | Neither the worst-case `n`-only exponent nor the fixed-density exponent improves. The constants are very large. The Margulis–Gabber–Galil spectral theorem is cited, not tested. The packet contains no tensor-contraction engine or full solver. |
| [`eth_density_refinement/`](Research/eth_density_refinement/README.txt) ‡ | `eth_density_refinement.zip` | For `m ⩽ Bn` with `1 ⩽ B ⩽ (log n)^A`, exact counting in `poly(n,m) · 2^{O(n log(2+B)/√(log n))}` time and polynomial space. At `B = Θ(log log n)` the exponent numerator improves from `n log log n` to `n log log log n`. Smaller Hermite precision budgets cut the matched leading mode-enumeration coefficient by a factor of 16. [`report.pdf`](Research/eth_density_refinement/report.pdf), 14 pages; [`integration_notes.txt`](Research/eth_density_refinement/integration_notes.txt) maps the changes to source lemmas. | The unrestricted worst-case exponent is unchanged, as is the `√(log n)` denominator. The factor 16 is between upper bounds, not a measured speedup. It overlaps `sat_density_improvement/` in result and method. Its `LICENSE-UPSTREAM.txt` is the upstream Apache 2.0 text. |

### Barriers and conditional proposals

| Directory | Archive | Claim | Scope stated by the packet |
|---|---|---|---|
| [`3sat_refinement/`](Research/3sat_refinement/README.md) | `3sat_refinement_package.zip` | For sparse degree-k parity tests, a scalar lift `E_i(z) = (1 + ∏(1 − 2m(z)))/2` is proved. Modulo `2^p` it leaves no incidence monomial of degree above `k(p+a−1)`; at `p = n+1` that is `k(n+a)`, against the source's `k(2n+a)`. A second contraction over compactly indexed mode tuples would give `2^{O_k(n (log log n)^{3/2}/log n)}`. [`3sat_refinement_report.pdf`](Research/3sat_refinement/3sat_refinement_report.pdf), 17 pages; [`data/research_status.json`](Research/3sat_refinement/data/research_status.json) separates proved, inherited and assumed results. | The leading bound stays `2^{O_k(n log log n/√(log n))}`. The stronger exponent needs a compact factorization that is **not supplied**; compacting index strings alone gives tensors with too many wires. |
| [`3sat_asymptotic_analysis/`](Research/3sat_asymptotic_analysis/README.md) | `3sat_asymptotic_analysis_20261027.zip` | **No stronger unrestricted bound is established.** It proves restricted barriers: weighted-budget tightening, taper retuning and Newton modes do not by themselves improve the exponent. Two **missing** interfaces are identified. A degree-preserving recursive interface would give `O(n √(log log n/log n))`; a uniform linear-wire compression interface would give `O(n/√(log n))`. [`report/report.pdf`](Research/3sat_asymptotic_analysis/report/report.pdf), 11 pages; [`research_decision/findings.md`](Research/3sat_asymptotic_analysis/research_decision/findings.md). | Neither interface is constructed. It includes three upstream Lean files in `audit/lean_selected/`, identified by `manifest.json`; they are not built. The bundled copy of the preprint and upstream README/license (`source/`) is omitted as byte-identical to upstream; `source/manifest.json` and the derived `source/paper.txt` are kept. |

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
upper bounds, not measured runtimes.

| Packet | Claimed gain |
|---|---|
| [`eth_contraction_improvements/`](Research/eth_contraction_improvements/README.txt) | Exponent coefficient 648.44… against 18,535.75… for the source schedule under the same analysis, about 28.6× |
| [`eth_density_refinement/`](Research/eth_density_refinement/README.txt) | Leading mode-enumeration coefficient divided by 16 |
| [`3sat_precision_refinement/`](Research/3sat_precision_refinement/README.md) | Working precision `24MD/u` → `6MD/u`, halving the leading constant |
| [`cauchy_mode_improvement/`](Research/cauchy_mode_improvement/README.txt) | Mode-count ratio `1/√3` |

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
order improvement therefore needs new structure, not better constants.

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
- No supplied script, test, Makefile or LaTeX build was run.

