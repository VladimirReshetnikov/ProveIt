# Draft manifest

Global inventory of every research draft under this directory, grouped by
theme. Each draft directory holds one LaTeX document with its compiled PDF
and any supporting data, scripts, or figures. Drafts are **temporary
inboxes** (see [`../README.md`](../README.md)): once a draft's content is
either integrated into the primary exposition or absorbed into the
canonical frontier volume, the draft is deleted; this manifest must be
updated when that happens.

New drafts arrive through `incoming/` (as archives or directories),
are unpacked into the matching group, and are recorded here.

Reorganized into thematic groups on 2026-08-28. Path strings inside the
documents themselves (corpus inventories, provenance banners,
`\nolinkurl{...}` pointers) predate the reorganization and refer to the
old flat layout; the **Previous path** column below is the map. Documents
were moved verbatim — no `.tex` content was changed by the reorganization,
so no PDF was rebuilt for it.

## fourier-decay — `rvachev_up_fourier_decay/`

The Fourier-decay corpus: eight independently written source documents on
the decay envelope of `Û = ∏ sinc(2πξ/2^k)`, two audits, and a
popularization. Kept in its historical directory (heavily
cross-referenced internally; unchanged by the reorganization).

| Directory | Document |
| --- | --- |
| `rvachev_up_fourier_decay-1/` | Source Document 1 (decay-rate analysis) |
| `Rvachev_Up_Fourier_Decay-2/` | Source Document 2 |
| `Rvachev_Up_Fourier_Decay-3/` | Source Document 3 (*Fourier decay of Rvachev up*) |
| `rvachev_up_fourier_decay-4/` | Source Document 4 (the most rigorous where they overlap; ρ₁ certificate appendix) |
| `rvachev_up_fourier_decay-5/` | Source Document 5 (*Final*) |
| `rvachev_up_fourier_decay-6/` | Source Document 6 (*Final Synthesis*) |
| `rvachev_up_fourier_decay-7/` | Source Document 7 (second wave; shell-adaptive gauge) |
| `rvachev_up_fourier_decay-8/` | Source Document 8 (second wave) |
| `Rvachev_Up_Fourier_Decay_Comparative_Audit/` | The comparative audit of Documents 1–4, κ-dictionary, feasibility list |
| `Rvachev_Up_Fourier_Decay_Second_Wave_Audit/` | Audit of Documents 7–8; the shell-adaptive gauge verdict |
| `Rvachev_Up_Fourier_Decay_Gentle_Guide/` | Popularization (corrected 2026-08-28: composite limit answer, per-octave constant, profile range) |
| `asymptotic-decay-rate-of-an-infinite-product-of-sinc-functions/` | The original Stack-Exchange-format question document |

## thue-morse — `thue-morse/`

| Directory | Document | Previous path |
| --- | --- | --- |
| `Thue_Morse_Formula_Atlas/` | *A Unified Formula Atlas for the Thue–Morse Sequence* | `drafts/Thue_Morse_Formula_Atlas/` |
| `Fabius_Rvachev_Thue_Morse_Frontier_Results/` | *A Finite-Block Calculus for the Fabius–Rvachev–Thue–Morse System* (block bridges, zeta–Lambert tail calculus, q-Richardson; heavily Lean-crosswalked) | `drafts/Fabius_Rvachev_Thue_Morse_Frontier_Results/` |

## exponents-and-q-series — `exponents-and-q-series/`

| Directory | Document | Previous path |
| --- | --- | --- |
| `Exponents_and_q_Series_Frontiers/` | *Exponent-Sequence and q-Series Frontiers* — consolidation (2026-08-28) of the former `Fabius_Newton_Rvachev_Frontier_Report/` (*Exponent-Sequence and Newton-Basis Frontiers*, Lean-crosswalked) and `fabius_frontier_results/` (*q-Binomial Richardson Acceleration of Geometric Sinc Products*); their assets live under `assets/`, provenance with SHA-256 in the document | absorbed drafts deleted; git history is the archive |

## spectra-and-arithmetic — `spectra-and-arithmetic/`

| Directory | Document | Previous path |
| --- | --- | --- |
| `Fabius_Half_Integer_Spectral_Frontier_Report/` | *Half-Integer Spectral Arithmetic* | `drafts/Fabius_Half_Integer_Spectral_Frontier_Report/` |
| `Fabius_Arithmetic_Rays_Frontier_Report/` | *Arithmetic Dyadic Rays of the Rvachev Fourier Product* | `drafts/Fabius_Arithmetic_Rays_Frontier_Report/` |
| `Spectral_Arithmetic_Pascal_Rvachev_Hierarchy/` | *Spectral Arithmetic and the Pascal–Rvachev Hierarchy* | `drafts/Spectral_Arithmetic_Pascal_Rvachev_Hierarchy/` |
| `Fabius_Derivative_Norm_Spectrum_bundle/` | *Derivative Norm Spectra and Dual Moment Geometries of the Fabius–Rvachev System* | `drafts/Fabius_Derivative_Norm_Spectrum_bundle/` |

## integration-and-transforms — `integration-and-transforms/`

| Directory | Document | Previous path |
| --- | --- | --- |
| `Fabius_Antiderivatives_Report/` | *Antiderivatives of Monomially Weighted* Fabius integrands | `drafts/Fabius_Antiderivatives_Report/` |
| `Fabius_Monomial_Antiderivatives_Report/` | *Fabius Monomial Antiderivatives and Inverse-Quantile Integrals* | `drafts/Fabius_Monomial_Antiderivatives_Report/` |
| `fabius_monomial_antiderivatives_report-2/` | *Dyadic Primitive Ladders and Mellin–Newton Antiderivatives* | `drafts/fabius_monomial_antiderivatives_report-2/` |
| `Fabius_Integral_Transforms_Report/` | *Integral Calculus and Transform Dualities* | `drafts/Fabius_Integral_Transforms_Report/` |
| `Fabius_Integral_and_Transform_Frontiers/` | *Integral and Transform Frontiers* | `drafts/Fabius_Integral_and_Transform_Frontiers/` |
| `Fabius_Rvachev_Integral_Frontiers/` | *Integral Transforms and Fractional Calculus for the Fabius and Rvachev Functions* | `drafts/Fabius_Rvachev_Integral_Frontiers/` |
| `fabius_integral_frontiers_bundle/` | *Integral and Transform Frontiers* (bundle variant) | `drafts/fabius_integral_frontiers_bundle/` |
| `Fabius_Integral_Transform_Fractional_Frontiers/` | *Integral, Transform, and Fractional Frontiers* | `drafts/Fabius_Integral_Transform_Fractional_Frontiers/` (arrived 2026-08-28) |
| `Fabius_Rvachev_Fractional_Integral_Report/` | *Fractional Integral Calculus and Complex-Order Transform Hierarchies for the Fabius–Rvachev System* | `drafts/Fabius_Rvachev_Fractional_Integral_Report/` (arrived 2026-08-28) |
| `Fabius_Fractional_Integral_Transform_Frontiers/` | *Integral, Transform, and Fractional-Order Frontiers for the Fabius–Rvachev System* | `drafts/incoming/…zip` (unpacked 2026-08-28) |
| `fabius_fractional_transform_frontiers_bundle/` | *Fabius Fractional Transform Frontiers* (nonlocal tails, difference hierarchy, quantile-fractional and Stieltjes figures) | `drafts/incoming/…zip` (unpacked 2026-08-28) |

## inverse-and-sampling — `inverse-and-sampling/`

| Directory | Document | Previous path |
| --- | --- | --- |
| `Fabius_Inverse_Frontier_Report_Source_and_PDF/` | *Inverse Frontiers for the Fabius–Rvachev System* | `drafts/Fabius_Inverse_Frontier_Report_Source_and_PDF/` |
| `fabius_frontier_dyadic_inverse_barnes_report/` | *Dyadic Inverse Germs and Barnes–Rvachev Deconvolution* | `drafts/fabius_frontier_dyadic_inverse_barnes_report/` |
| `Fabius_Dyadic_Self_Sampling_Frontier_Package/` | *Dyadic Self-Sampling, Alias Superconvergence, and Rvachev–Appell Deconvolution* | `drafts/Fabius_Dyadic_Self_Sampling_Frontier_Package/` |

## representations — `representations/`

Series and orthogonal-expansion representations of the up-function.

| Directory | Document | Previous path |
| --- | --- | --- |
| `Fabius_Rvachev_Representation_Frontiers/` | *Fabius–Rvachev Representation Frontiers* (Jacobi coefficients, exact even moments, resolvent and logarithmic-derivative identities) | `drafts/incoming/…zip` (unpacked 2026-08-28) |

## frontier-compilations — `frontier-compilations/`

Broad multi-topic "collected new results" reports, kept together as a
series even where a single title leans toward another group.

| Directory | Document | Previous path |
| --- | --- | --- |
| `Fabius_Rvachev_Frontier_Report/` | *Tail Quadrature, Exact Dyadic Error Laws, …* | `drafts/Fabius_Rvachev_Frontier_Report/` |
| `Fabius_Rvachev_Frontier_Report-2/` | *Arithmetic Spectra of the Rvachev Sinc Product* | `drafts/Fabius_Rvachev_Frontier_Report-2/` |
| `Fabius_Rvachev_Frontier_Report-3/` | *Zero-Divisor-Preserving q-Richardson Extrapolation for the Fabius–Rvachev Sinc Product* | `drafts/Fabius_Rvachev_Frontier_Report-3/` |
| `Fabius_Rvachev_Frontier_Report_2026-08-27/` | *Midpoint Transmutation, Dyadic Cardinal Reproduction, …* | `drafts/Fabius_Rvachev_Frontier_Report_2026-08-27/` |
| `Fabius_Rvachev_New_Frontiers/` | *Gamma Duality, Total Positivity, and …* | `drafts/Fabius_Rvachev_New_Frontiers/` |
| `fabius_frontier_report_bundle/` | *Confluent Digital Extrapolation and …* | `drafts/fabius_frontier_report_bundle/` |
| `fabius_frontier_results_bundle/` | *Dyadic Spectral Determinants for the Fabius–Rvachev System* | `drafts/fabius_frontier_results_bundle/` |
| `fabius_frontier_new_results/` | *Logarithmic q-Richardson Acceleration and Lambert Phase Locking in Fabius–Rvachev Analysis* | `drafts/fabius_frontier_new_results/` |
| `fabius_frontier_spectral_endpoint_report_bundle/` | *Binary Spectral–Endpoint Bridges for the Fabius and Rvachev Functions* | `drafts/fabius_frontier_spectral_endpoint_report_bundle/` |
| `beyond_dyadic_fabius_web_report/` | *Beyond the Dyadic Fabius Web* | `drafts/beyond_dyadic_fabius_web_report/` |
