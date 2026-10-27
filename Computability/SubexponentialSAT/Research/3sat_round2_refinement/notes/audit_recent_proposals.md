# Audit of the recent ProveIt ETH arrivals

## Frozen scope and acquisition

- Repository snapshot: `aa6933442eb936962de79ba6d321cd0391c450bd`, authored 2026-10-27 00:53:43 UTC; root tree `2afad33e3e22c1b307adcc082a5f76a04d8f4bbb`.
- The complete `docs` subtree has 13 entries and is not truncated. Its `incoming` subtree contains seven ZIP packets, two ETH-related PDFs, and its unrelated long README.
- Commit `a505bd768bce347c70e923586c5f72ad3085bf44` (00:42:51) added Cauchy, contraction, SAT-density, original paper, and alternate eth.pdf.
- Commit `64b3202ee84fc4d71fe69c34d2110c93b7da95cd` (00:44:39) added precision, parity-refinement, and ETH-density packets.
- Commit `8afdbbea48d67b8d252a99e8926f3eca9649eae3` (00:48:56) added our previously delivered asymptotic-analysis packet. These commit file lists contain only 5, 3, and 1 files respectively and fit the requested 100-file page.
- Every archive/PDF was independently hashed as a Git blob and matched the immutable tree. `download_checks.json` records SHA-256 and Git SHA-1. The last packet also matches the known local SHA-256 `02deac7de7de77550eafcee20cc251e7c6706fb3914e4e88946297ef74c5dd57`.
- Six ZIPs were safely unpacked after checking member paths. All 82 checksum-listed internal files match. No upstream/package code was executed, no dependencies installed, and no upstream state changed.
- The >1 MiB final ZIP returned empty content from GitHub Contents API and GitHub fetch rejected its binary blob. An immutable public raw download succeeded and was hash-verified; there is no unresolved acquisition blocker.

### Completeness qualification

A repository-wide **path inventory** was completed: 223,088 descendants, 29 recorded recursive subtree requests plus four nonrecursive split reads, no errors. Four truncated subtree responses were recursively split rather than accepted as complete. Matching ETH/3SAT/SubexponentialSAT paths occur only in `docs/incoming`; other “subexponential” matches concern unrelated transseries research. This is not a full-content search of every ambiguously named file, nor an independent proof that no hidden or externally hosted development exists. Four non-ETH submodules were recorded but their external repositories were not traversed. The incoming theorem artifacts have not been integrated into a separately named native ETH proof subtree at this snapshot.

Evidence: `path_inventory_summary.json`, `tree_queries.json`, `eth_path_matches.json`. The full TSV and its gzip are large and should **not** be bundled into the user ZIP; the compact summaries suffice for ordinary provenance.

## Comparison inventory

Let L = log n and l = log log n. Polynomial factors and fixed-width constants are suppressed. “Derived” below means a natural-language derivation relative to the imported OpenAI Appendix D contraction theorem and other stated inputs, not a fresh independent certification of the entire ETH claim.

| Arrival | Proved/derived contribution claimed | General / sparse exponent scale | Stronger target left conditional |
|---|---|---|---|
| `cauchy_mode_improvement_2026-10-26.zip` | Integral finite Cauchy separation with weights 1+b+2v2(b!)=3b+1−2popcount(b); leading abstract mode-entropy coefficient factor 1/√3, compatible recursion claimed | n l/√L; n/√L unchanged | No stronger log-power claimed |
| `eth_contraction_improvements.zip` | Exact Hermite condition count; precision 24MD/u→6MD/u; retuned schedule; streamed coefficient extraction ≤2^packet-size grid evaluations | Same orders; stated explicit contraction coefficient 18535.7538→648.4411 under its accounting | None advertised as achieved |
| `sat_density_improvement.zip` | Uniform density profile n·min(log(2+m/n),l)/√L using density-dependent expander-code checks and retained actual query sparsity | Unrestricted n l/√L; fixed density n/√L | No stronger unrestricted target proved |
| `3sat_precision_refinement_2026-10-26.zip` | Exact precision losses and full-loss taper minimax; dominant precision coefficient ≤6 instead of24 | Same orders; mode coefficient halved | Structured-mode summation hypothesis would give general n l/L and sparse n/L |
| `3sat_refinement_package.zip` | Scalar exact parity lift; incidence degree k(2n+a)→k(n+a) at precision n+1; removes truncated-V coefficient axis | Same general n l/√L | Compact-factorization hypothesis would give n l^(3/2)/L |
| `eth_density_refinement.zip` | Same density-sensitive profile; somewhat different expander parameters; precision retuning and η=1/2048 give 16-fold matched mode coefficient improvement vs original parameters; exact local Cauchy Smith profile | Same orders | Research directions only |
| `3sat_asymptotic_analysis_20261027.zip` | Our prior delivered audit and scoped obstruction results, not a stronger algorithm | Baseline unchanged | Degree-K kernel plus closure target n√(l/L); no kernel/closure supplied |
| `paper.pdf` | Byte-identical original OpenAI paper | Baseline n l/√L, sparse n/√L | Not an additional proposal |
| `eth.pdf` | Separate 49-page alternate manuscript; assigned to separate reviewer | Its claimed headline is same asymptotic, not faster | Formal proof availability requires separate review; no corresponding source subtree found |

The precision conditional target is asymptotically stronger than the parity conditional target, and both are stronger than the prior degree-K-kernel target. Therefore a synthesis of constant improvements cannot honestly be described as a better asymptotic rate than **every conditional proposal**.

## Source-pin compatibility

Four packets cite `openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`; precision and ETH-density cite `42907c9e999cc00d6abe7a50bfc1023250edd1b9`. The latter directory membership was freshly read through GitHub. Its four TeX Git blobs match independently hashed local copies at the former pin:

- main_full_version.tex: f7af85e623b58e0ca9f4b9416916d442defa963a
- quantitative-contraction.tex: 51ba54efc29f51bbc0426f848003030da484f354
- quantitative-reduction.tex: 80389ac39d987133b71b2ddc2593e6fcdd99871a
- quantitative-circuits.tex: e25def5eb03ee53feefd3fe480dd5a1293761fae

Thus the differing repository pins do not create a paper-source mismatch in these four files. Evidence: `openai_429_build_membership.json`, `source_equivalence.json`.

## Detailed density-proof audit

Both density reports were read through their complete construction and complexity proofs. No fatal gap was found in the following chain, **conditional on the explicitly imported upstream contraction and parity identities**:

1. Lazy MGG walk: degree16, nonconstant spectrum ≤(1+5√2/8)/2<19/20. Its eight port formulas and spectral claim match the official Isabelle AFP source, inspected 2026-10-27: https://isa-afp.org/browser_info/current/AFP/Expander_Graphs/Expander_Graphs_MGG.html . This external theorem is an input, not proved by the packet's tiny graph tests.
2. Power by t=O(log B), yielding degree poly(B) and spectral error at most δ/2 for δ=Θ(1/(B log B)).
3. Exhaustive local-code search with entropy bound produces relative distance δ with O(d/B) rows. Time 2^{O(d²)} is paid explicitly, not hidden as polynomial.
4. Bipartite edge-code distance ≥δ(δ−ε)E≥δ²E/2 survives shortening. Rounding E<4m is paid for in row count. Small-input handling differs but is valid: SAT-density uses direct occurring-variable enumeration; ETH-density uses one-vertex parallel edges.
5. Greedy exact-count minimization reduces surviving nonsolutions by3/4 per round. 3n rounds suffice because 2^n(3/4)^{3n}=(27/32)^n<1. Repeated clause indices do not invalidate parity uniformity because each sampled coefficient bit is independent.
6. At most O(n) parity equations have S=poly(B) monomials. High-incidence branching costs2^{O(n/√L)}. Degree-array compression yields O(n log(S+2)) Boolean wires, max degree O(n^(3/4)S√L), and entry time2^{O(S)}poly(n), satisfying Appendix D uniformly for S≤L^C. For B≤L^A, the initial-code and candidate-search exponents are fixed powers of L and hence o(n/√L). Sequential enumeration preserves polynomial space.

The two density packages are largely duplicate mathematics with different conservative constants, not separate asymptotic improvements to stack multiplicatively. Neither improves unrestricted l/√L to a better power of L. Their finite test records do not establish the full solver, and this audit did not rerun their scripts or rebuild Lean.

## Useful structural observation for further work

ETH-density §9.4 computes exact Smith invariant valuations e_j=2j+2v2(j!)≈4j for K_ij=1/(a+2i−2j), a an odd unit. The factorial Cauchy package obtains weights≈3b on the **larger** auxiliary-row domain K(z,j)=1/(1−zj), and explicitly warns that its determinant obstruction is not a lower bound on the narrower actual reciprocal packet rows. An actual-row feature construction exploiting slope4 might improve constants beyond the existing basis, but requires a correct uniform integral separation and creation-precision/recursive compatibility argument; it does not by itself change the √log denominator.

## Local source paths

All six new editable reports live under
`sources/proveit/extracted/<archive-stem>/<inner-package>/`.
The density reports are:
- `sat_density_improvement/sat_density_improvement/density_aware_sat_improvement.tex`
- `eth_density_refinement/eth_density_refinement/report.tex`

Immutable public references:
- https://github.com/VladimirReshetnikov/ProveIt/tree/aa6933442eb936962de79ba6d321cd0391c450bd/docs/incoming
- https://github.com/VladimirReshetnikov/ProveIt/commit/a505bd768bce347c70e923586c5f72ad3085bf44
- https://github.com/VladimirReshetnikov/ProveIt/commit/64b3202ee84fc4d71fe69c34d2110c93b7da95cd
- https://github.com/VladimirReshetnikov/ProveIt/commit/8afdbbea48d67b8d252a99e8926f3eca9649eae3

