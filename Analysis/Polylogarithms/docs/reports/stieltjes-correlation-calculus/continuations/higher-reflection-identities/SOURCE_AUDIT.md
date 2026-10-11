# Source audit and inherited-result map

This note accompanies **Higher Reflection Identities and Resonant Zeta Calculus**. The source baseline is ProveIt commit **`c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4`**.

- [Canonical manuscript at the pinned revision][manuscript]
- [Canonical manuscript README and status record][status]
- [Incoming directory at the pinned revision][incoming]
- [Incoming README and intake history][intake]

## Acquisition and review scope

The preparation corpus includes the relevant canonical manuscript sections, the two source-root READMEs, and **all nine ZIP archives present in the pinned incoming inventory**. All nine archives were acquired and extracted. The file `provenance.json` records the baseline and incoming archive names. All source links below use the full commit.

This was a **focused mathematical audit** of the integration, harmonic, reflection, Stieltjes finite-part/contact, and Tornheim material used by the new report. Acquiring an archive, reading its README, or preserving an earlier verification receipt does not establish that every proof in it has received a new audit. The report makes no claim of a complete review of the four-volume manuscript or a replay of every historical suite.

### The nine incoming archives

The archive names below are exact paths under `docs/incoming/`. Titles and entry points are taken from the extracted packages.

| Archive | Observed report title and principal source entry |
|---|---|
| [ProveIt_Bilinear_Mellin_Hurwitz_2026-10-10.zip][bilinear] | **Bilinear Mellin–Hurwitz Calculus: Double-zeta reductions, harmonic moments, and Stieltjes reciprocity**; `bilinear_mellin_hurwitz/article.tex`. |
| [ProveIt_Coincident_Stieltjes_Directional_Zeta_2026-10-10.zip][coincident] | **Coincident Stieltjes Products and Directional Zeta Identities**; `ProveIt_Coincident_Stieltjes_Directional_Zeta_2026-10-10/article.tex`, with standalone `Coincident_Stieltjes_and_Directional_Zeta.tex`. |
| [ProveIt_Cubic_Harmonic_Mixed_Orders_2026-10-11.zip][cubic] | **Cubic Tornheim Derivatives and Harmonic Stieltjes Constants**; `ProveIt_Cubic_Harmonic_Mixed_Orders_2026-10-11/article.tex`, with standalone `Cubic_Tornheim_Harmonic_Stieltjes.tex`. |
| [ProveIt_Exact_Resonant_Identities_2026-10-11.zip][exact] | **Exact Resonant Identities Beyond the Diagonal**; `ProveIt_Exact_Resonant_Identities_2026-10-11/article.tex`, with standalone `Exact_Resonant_Identities.tex`. |
| [ProveIt_Independent_Orders_2026-10-11.zip][independent] | **Independent Orders and Exact Reductions in Polylogarithm–Zeta Calculus**; `ProveIt_Independent_Orders_2026-10-11/article.tex`, with standalone `Independent_Orders_and_Exact_Reductions.tex`. |
| [ProveIt_Mixed_Spectral_Identities_2026-10-10.zip][mixed] | **Mixed Spectral Identities: Harmonic Newton Series, Dougall Jets, Unequal Twists, and Stieltjes Collisions**; `ProveIt_Mixed_Spectral_Identities_2026-10-10/article.tex`. |
| [ProveIt_Ordered_Hurwitz_Resonances_2026-10-10.zip][ordered] | **Ordered Hurwitz Resonances and Cubic Stieltjes Products**; `Ordered_Hurwitz_Resonances_2026-10-10/article.tex`, with standalone `Ordered_Hurwitz_Resonances.tex`. |
| [ProveIt_Periodic_Collision_Contacts_2026-10-10.zip][periodic] | **Periodic Stieltjes Collisions: Exact Contact Terms, Finite-Part Fubini Laws, and Gamma–Polylogarithm Primitives**; `ProveIt_Periodic_Collision_2026-10-10/Periodic_Stieltjes_Collisions.tex`. |
| [ProveIt_Periodic_Stieltjes_Contact_2026-10-10.zip][contact] | **Periodic Stieltjes Contact Calculus: All-Index Collision Corrections, Harmonic Derivative Anomalies, and Exact Zeta-Jet Integrals**; `ProveIt_Periodic_Stieltjes_Contact/article.tex`. |

Dates and older commit counts inside these READMEs describe their own preparation snapshots. For example, references there to six or eleven incoming archives do not change the nine-archive inventory at the revision used here.

## Mapping inherited results and explicit research questions

Paths beginning with `chapters/` in this table are relative to the canonical manuscript. Other section paths are relative to the extracted report named in the first column.

| Source and exact location | Inherited result or stated question | Use and extension in this report |
|---|---|---|
| Canonical [`chapters/07-integration.tex`][integration], especially “The common Hurwitz-jet calculus,” “Reflection formulas,” and “Moments” | Hurwitz/Stieltjes conventions, argument primitives, reflection, and moment calculus. | Section 2, `sections/02_beta.tex`, uses these conventions in the complex-power sine transform and its normalized antiderivatives. These foundational identities are inherited. |
| Canonical [`chapters/07-harmonic-gamma-coefficients.tex`][harmonic] | The normally convergent Gauss–Gamma generator for elementary-symmetric harmonic numerators and its corrected all-order consequences. | Background for Section 3. Elementary-symmetric numerators, raw powers of `H_n`, and general polynomials in `H_n^(r)` remain distinct families. The new criterion concerns the last family. |
| Canonical [`chapters/07-stieltjes-convolution-foundation.tex`][foundation], `chapters/07-shifted-stieltjes-correlations.tex`, [`chapters/08-stieltjes-contact-products.tex`][products], and `chapters/08-stieltjes-dilation-contacts.tex`; both periodic-contact archives | Fixed-coordinate finite parts, Hurwitz Fourier normalization, shifted closure, derivative/contact corrections, and primitive normalization. The two periodic reports already supply the all-index two-factor distributional comparison. | Sections 2 and 4 retain the complete local numerator and the coordinate convention. Section 4 does not claim a new proof of the already established two-factor contact law. |
| **Exact Resonant Identities**, `sections/03_reflected.tex` and `sections/07_research.tex`, **Q8: “A reflected generating function beyond polynomials”** | Coincident polynomial reflected Stieltjes/polygamma closure is already proved. Q8 requests a nonpolynomial family with its full changing-exponent subtraction. | Section 2, “A completed complex-power sine transform,” supplies the complex-power family, Gamma Fourier coefficients, polylogarithmic integral, and completed crossing germ. |
| **Exact Resonant Identities**, `sections/04_harmonic.tex` and `sections/07_research.tex`, **Q11: “Generalized harmonic products and their regular shifts”** | Raw powers `H_n^p` already have centered regularity at every nonpositive even integer. Q11 explicitly warns that this proof does not automatically apply to higher harmonic orders. | Section 3, `sections/03_harmonic.tex`, gives the necessary and sufficient polynomial-involution criterion and the invariant algebra. |
| **Mixed Spectral Identities**, `sections/05_collisions.tex`, Theorems labeled `cl:collision` and `cl:allfactor`; `sections/06_audit_research.tex`, “A complete geometric collision calculus” and “Hierarchical collisions and composition” | The fixed-rate zero-index triple formula and its finite anomaly are already proved. The all-factor theorem is a spectral completion for a prescribed configuration. Moving geometric clusters and the hierarchical path `(0,ε,ε+ε²)` are explicitly proposed. | Section 4, `sections/04_collision.tex`, supplies an exact local geometric subtraction with an analytic remainder for arbitrary factor counts and argument-derivative orders at Stieltjes index zero. It includes the hierarchical and equally spaced quartic constants. Higher Stieltjes indices and associativity of successive mergers remain separate. |
| **Cubic Tornheim Derivatives and Harmonic Stieltjes Constants**, `sections/02_cubic_harmonic.tex`, `sections/03_diagonal_bridge.tex`, and `sections/04_ray_calculus.tex` | The digamma-cube/harmonic-Stieltjes bridge and the complete asymmetric cubic directional formula are inherited, including the retained ordinary-constant reduction questions. | Section 2 uses the inherited cube bridge to interpret its new logarithmic sine-moment identity. Section 5 starts at the next directional order; neither the cube bridge nor the cubic spanning formula is relabeled as new. |
| **Independent Orders and Exact Reductions**, `sections/03_tornheim.tex` and `sections/07_research.tex`, “The quartic and higher directional layers” and “Systematic cancellation of directional coordinates”; **Cubic** report, `sections/07_audit_research.tex`, **Question 4: “Construct the complete quartic directional layer”** | The holomorphic Tornheim remainder, exact axis, Euler boundary relation, cubic coordinates, and the explicit request for a quartic reconstruction and a formal quotient dimension. | Section 5, `sections/05_tornheim.tex`, gives the fourth directional derivative, convergent representatives of its three coordinates, cancellation formulas, and the all-order residual/cyclic dimension calculation. Dimensions refer to the specified formal relations. |

The bilinear and ordered-Hurwitz reports also supply broader Mellin, harmonic, and resonant-normalization context. Their finite mixed-order closure, ordered Laurent completion, and cubic completion results are not claimed as new contributions here.

## Corrections already present or already reported

No new false source theorem was identified among the claims used by this report. In particular:

1. The real arctanh formula labeled `cleo:eq:lintanh` in canonical [`chapters/03-algebraic.tex`][algebraic] **already contains** the absolute value in its logarithm and a proof on both sides of zero. The earlier unsupported non-elementarity assertion has already been replaced by a qualification that minimality and non-elementarity are unproved. The older mixed-spectral correction proposal should not be reapplied as though these changes were missing at the present pin.
2. The Choi harmonic factor-two normalization and the `n=0` term are already handled in `chapters/07-harmonic-gamma-coefficients.tex`. Its all-order pure and mixed families are inherited proved results.
3. The previously rejected `S8` vector is distinguished from the revised candidate in canonical [`chapters/04-S8-candidate.tex`][s8]. Rejection of the former is not a new finding and does not refute the latter.
4. The correction to Lo Ho Tin’s arXiv:2507.03058v1 equation (22) is already documented in **Exact Resonant Identities**, `sections/06b_tin_sign.tex`. The Borwein–Dilcher author-PDF conventions `H_0=0`, the integer logarithm coefficient, and the local-series splitting radius were already documented in the coincident/directional and cubic packages. These are inherited, version-specific correction records; this audit does not claim a fresh review of every external publication version.

## Extrapolations excluded by the new results

The new report proves limits on possible extensions without attributing those extensions to source theorems.

- **Centered harmonic regularity is not universal for generalized harmonic polynomials.** The numerator `(H_n^(2))²` has residue `−2ζ(2)` at `s=0`. Section 3 gives the exact invariant criterion; the source’s theorem for raw powers of `H_n` remains valid.
- **One diagonal Tornheim coordinate does not determine every higher cyclic layer from the recorded relations alone.** Section 5 exhibits the fifth-degree polynomial `ABC((A+B+C)²−3(AB+BC+CA))`. It satisfies the homogeneous boundary restrictions and vanishes on the diagonal, while its cyclic sum is nonzero. This is a formal underdetermination result, not a proof of arithmetic independence or a refutation of an unknown additional functional identity.
- **A scalar collision constant depends on the path unless the full local counterterm is removed.** This phenomenon was already established for fixed-rate triples by the mixed-spectral report. The new hierarchical value `Q3+γ−11/6` and quartic formula extend its precise calculation. They do not correct a source theorem asserting path independence. The derivative-pair identity in Section 4 likewise illustrates the already recognized need for boundary/contact corrections in finite-part integration by parts.

## Claim boundaries retained for integration

The current Gaussian **S6** (`cycloquot:conj:S6`) and **revised S8** (`s8new:conj:S8`) remain open. Existing rigorous proximity estimates and formal separating certificates do not decide their period equalities. The arithmetic reduction or independence of the retained harmonic and Tornheim coordinates also remains open. The report’s new proofs address the stated analytic and finite formal-algebraic questions; no worldwide-priority claim, external referee validation, or proof-assistant formalization is asserted.

[manuscript]: https://github.com/VladimirReshetnikov/ProveIt/tree/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/Analysis/Polylogarithms/docs/manuscript
[status]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/Analysis/Polylogarithms/docs/manuscript/README.md
[incoming]: https://github.com/VladimirReshetnikov/ProveIt/tree/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/docs/incoming
[intake]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/docs/incoming/README.md
[bilinear]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/docs/incoming/ProveIt_Bilinear_Mellin_Hurwitz_2026-10-10.zip
[coincident]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/docs/incoming/ProveIt_Coincident_Stieltjes_Directional_Zeta_2026-10-10.zip
[cubic]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/docs/incoming/ProveIt_Cubic_Harmonic_Mixed_Orders_2026-10-11.zip
[exact]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/docs/incoming/ProveIt_Exact_Resonant_Identities_2026-10-11.zip
[independent]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/docs/incoming/ProveIt_Independent_Orders_2026-10-11.zip
[mixed]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/docs/incoming/ProveIt_Mixed_Spectral_Identities_2026-10-10.zip
[ordered]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/docs/incoming/ProveIt_Ordered_Hurwitz_Resonances_2026-10-10.zip
[periodic]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/docs/incoming/ProveIt_Periodic_Collision_Contacts_2026-10-10.zip
[contact]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/docs/incoming/ProveIt_Periodic_Stieltjes_Contact_2026-10-10.zip
[integration]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/Analysis/Polylogarithms/docs/manuscript/chapters/07-integration.tex
[harmonic]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/Analysis/Polylogarithms/docs/manuscript/chapters/07-harmonic-gamma-coefficients.tex
[foundation]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/Analysis/Polylogarithms/docs/manuscript/chapters/07-stieltjes-convolution-foundation.tex
[products]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/Analysis/Polylogarithms/docs/manuscript/chapters/08-stieltjes-contact-products.tex
[algebraic]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/Analysis/Polylogarithms/docs/manuscript/chapters/03-algebraic.tex
[s8]: https://github.com/VladimirReshetnikov/ProveIt/blob/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4/Analysis/Polylogarithms/docs/manuscript/chapters/04-S8-candidate.tex
