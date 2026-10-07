# Sources and attribution

## Upstream source 55

Title: Sharp Second-Order Stability at the Polynomial-Phase Endpoint of Gowers Norms.
Research manuscript prepared with ChatGPT for Vladimir Reshetnikov, October 2026.

Archived original:
https://github.com/VladimirReshetnikov/ProveIt/blob/f8bc5e2ec281fcee02c0fc5ef717a775ee7e4442/docs/incoming/gowers_endpoint_stability.zip

- Archive Git blob SHA-1: 9a478ac4f39121017eacec0213d5059351cb6ab2
- Archive SHA-256: 022c17045d35e85e155048831e1bec7c2912e4e8aa007099aca9c19c5102d17d
- Original member: gowers_endpoint_stability/article.tex
- Preserved public snapshot: provenance/sources/source55_article.tex
- Article SHA-256: 6ec4106b68121b6d190dd2b37ab1a27a216981bf5442b68c3cbe00c0cde24128

The archive identity was fetched from the exact GitHub commit. Its local raw bytes were checked against that Git blob identity, and the included article was checked byte-for-byte against the named ZIP member. No text decoding/re-encoding or newline normalization was applied to the public snapshots.

The question labeled q:entry asks for explicit numerical entry and singly exponential dependence in d for entry and the local radius. Source 55 already proves the qualitative sharp second-order theorem. Report 285 imports and reproves its bounded-function identities, three-wise independence, four-vertex classification, quartic Fourier bound, Fourier mass pairing, fifth-order real-part cancellation, local absorption and inversion scheme, sharp coefficients, separation gap, and matching families. Those results are not new claims of Report 285.

The new quantitative refinements in this report are the explicit fidelity-preserving implementation of the small-cocycle proof and the interpolation remainder B'_d = 10 binom(2^d,5) + binom(2^d,6). Their combination supplies epsilon <= 10^(-d), local radius >= 2^(-5d/2), and cubic coefficient < 3*8^d. No publication-priority claim is made.

Historical upstream source audit:
https://github.com/VladimirReshetnikov/ProveIt/blob/e40138bd546c7445f12b7ceb59dafb7885848eaa/Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/55-endpoint-stability-SOURCE_AUDIT.md

- Git blob SHA-1: 60fd39f876da6e7692f1a656832757b518add802
- SHA-256: efe06b0abb6619a35cc9bfff3ffe3ba5fbbd07c472dd6a1a2eb2bbc7fcb31952
- Public snapshot: provenance/sources/source55_audit.md

This snapshot was retrieved as base64, decoded to raw bytes, and verified against its Git blob SHA-1. Its statements about the preparation and verification of source 55 are historical upstream statements, not claims of certification for Report 285.

## Published antecedent

T. Eisner and T. Tao, Large values of the Gowers–Host–Kra seminorms, Journal d'Analyse Mathematique 117 (2012), 133–186.
https://doi.org/10.1007/s11854-012-0018-2
https://arxiv.org/abs/1012.3509v2
https://arxiv.org/html/1012.3509v2

Theorem 1.1 supplies the qualitative all-compact-abelian-group near-extremizer antecedent, Section 2 the small-cocycle method, and Remark 1.6 the observation that effective polynomial rates can be extracted. The present finite-group proof displays conservative explicit constants and preserves a squared-correlation invariant. It does not claim a new qualitative inverse theorem.

## Framework

W. T. Gowers, A new proof of Szemeredi's theorem, Geometric and Functional Analysis 11 (2001), 465–588.
https://doi.org/10.1007/s00039-001-0332-9

This is the background uniformity and phase-extraction framework. Report 285 supplies no new global bound in Szemeredi's theorem.

## Package implementation lineage

The guarded builder and its regression structure are adapted from Report 284's frozen reproducible package. Its unrelated Lean-source snapshots are not carried over. The mathematics and source identifiers of the present report refer to source 55 and Eisner–Tao as described above. The public evidence is limited to the two pinned upstream snapshots.
