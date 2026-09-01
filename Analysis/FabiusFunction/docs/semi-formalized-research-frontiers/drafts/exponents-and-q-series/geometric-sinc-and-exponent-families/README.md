# Geometric sinc and exponent families

This subgroup centers the exponent-sequence and geometric sinc-product
synthesis together with its two closest exceptional-parameter companions.
The negative/reciprocal report overlaps the synthesis's signed q-Fabius
layer, while the cyclotomic report continues its root-of-unity and
natural-boundary program.

| Package | Role |
| --- | --- |
| [`Exponents_and_q_Series_Frontiers/`](Exponents_and_q_Series_Frontiers/) | Seven-part synthesis of exponent sequences, finite and geometric sinc products, q-binomial acceleration, transport geometry, atomic families, and signed/reciprocal q-Fabius theory. |
| [`Fabius_Rvachev_Frontier_Report/`](Fabius_Rvachev_Frontier_Report/) | Negative parameters, reciprocal-base digit reversal, multisection, shape transitions, and the Gaussian boundary. |
| [`Cyclotomic_q_Fabius_Rvachev_Frontier/`](Cyclotomic_q_Fabius_Rvachev_Frontier/) | Root-of-unity radial expansions, cyclotomic blow-ups, natural-boundary questions, Bell/moment condensation, and inverse branches. |

The current live Exponents synthesis source is
`Exponents_and_q_Series_Frontiers/Exponents_and_q_Series_Frontiers.tex`
(16,362 lines, 737,086 bytes, SHA-256
`11b459fdbe4cd44b4690d8ed91864b8864112a03bbff8f8bf980d197eb37dd55`).
It now includes the exact Lean crosswalk from integer-zero multiplicities to
the exponent sequence, constructive dyadic-order first differences, and full
generalized-product rigidity.  It also records the zero-definition,
three-theorem `GeometricPochhammerNormalConvergence.lean` API: the outer
nome-`q^2` Pochhammer product converges locally uniformly for every complex
strict contraction, including `q = 0`, with dyadic Rvachev-product and
bounded-Fabius Fourier specializations.  The compound centered/MGF and
outside-disk zero--pole statement remains Partial, as do zeta-quotient,
cumulant/analytic-sample, and probability-law identifiability.

The retained historical PDF has 238 A4 pages and 6,316,535 bytes, with SHA-256
`df7b9ad69e0310b17988dd42cc22559cf22ff26027395c005c374ad51f9e62aa`.
It was built from the earlier 16,270-line, 731,389-byte source SHA-256
`2adbe7b1e450a858bb02e80e6b4c4c6420060733f2ae1fe25eb61b6546f58e0f`,
with 41-input closure SHA-256
`98fc1f42ff94bf2e23b8fac0285fe43c637ee6d8326cb6a71530113991c7a7c0`.
Exactly three guarded serial passes produced 228, 238, and 238 pages, with no
input drift or TeX/Lean/Lake interleave. The final log had no blocking
diagnostics; all 238 pages were text-bearing; all 1,190 page boxes matched A4;
all 42 Type-1 font rows were embedded and subsetted, including 11 Libertinus
rows, with no Type-3 font. Fresh visual inspection of physical pages 1, 164,
220, 224--227, 236, and 238 was clean. A fresh source-pinned render is pending;
the PDF was intentionally not regenerated during this source-only update.

See the parent [topic index](../README.md) for detailed status and the
[draft manifest](../../MANIFEST.md) for consolidation provenance.
