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
(16,369 lines, 737,768 bytes, SHA-256
`4313bddb87a0f248a8bad4bd5e5a7cfbb25da51d1b994abc0c9d4c62525ca78c`).
It now includes the exact Lean crosswalk from integer-zero multiplicities to
the exponent sequence, constructive dyadic-order first differences, and full
generalized-product rigidity.  It also records the zero-definition,
three-theorem `GeometricPochhammerNormalConvergence.lean` API: the outer
nome-`q^2` Pochhammer product converges locally uniformly for every complex
strict contraction, including `q = 0`, with dyadic Rvachev-product and
bounded-Fabius Fourier specializations.  Its exact declarations are
`Fabius.hasProdLocallyUniformly_geometricSincProduct_complexQPochhammerInf`,
`Fabius.hasProdLocallyUniformly_rvachevFourierProduct_complexQPochhammerInf`,
and `Fabius.hasProdLocallyUniformly_rvachevFourier_complexQPochhammerInf`.
The compound centered/MGF and
outside-disk reciprocal formula, pole divisor, and zero--pole exchange remain
Partial, as do zeta-quotient,
cumulant/analytic-sample, and probability-law identifiability.

The retained historical PDF has 238 A4 pages and 6,953,898 bytes, with SHA-256
`fa719a8ea68d3c474928b9fae7449f827eb35a5452613f2b660d8e88ba27267e`.
It was built in exactly three serial passes from the preceding 16,274-line,
731,692-byte source SHA-256
`4be184dc95f7c9d7665e5edf56cd22dc66bdacbc2f113b03b700468836018f8b`,
producing 228, 238, and 238 pages. Basic A4, text-extraction, embedded-font, and
no-Type-3 checks passed. The larger PDF batch stopped before a fresh full log,
page-box, and visual publication audit, and the current TeX has since changed.
The child ledgers therefore record current TeX and historical PDF as distinct
payloads, not as a synchronized publication pair. A fresh final-source render
and full validation remain pending.

See the parent [topic index](../README.md) for detailed status and the
[draft manifest](../../MANIFEST.md) for consolidation provenance.
