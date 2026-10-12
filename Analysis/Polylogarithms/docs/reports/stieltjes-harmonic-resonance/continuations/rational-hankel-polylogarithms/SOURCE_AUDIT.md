# Source audit and research-status decisions

## Comparison point

Repository: `VladimirReshetnikov/ProveIt`.

The final explicit `main` observation was commit `505c62fddea6b4a9eb61fee0c76e6c021e9c7128`, whose commit timestamp is 2026-10-12T00:50:17Z. This is 11 October in the user's Pacific-time setting. During retrieval, main changed and six older incoming archives were moved into report placements. Source paths below refer to the recorded observation or to the separately recorded earlier file blob, rather than an assumption that main is immutable.

Repository content was read through the GitHub connector. Binary incoming archives were inspected through Wolfram's ZIP import because the available GitHub reader did not expose their members as text. External mathematical references were checked through their primary publication pages, arXiv records, and NIST DLMF. No repository write was performed.

## Inspected source material and its actual role

| Source | Exact identifier or path | Inspection / use |
|---|---|---|
| Canonical manuscript README | Blob `dc0fa26d0e5c2ede56df37c5640c7319681dfd25` | Selected research-status and integration descriptions; navigation, not proof dependency. |
| Canonical IBP normal forms | `Analysis/Polylogarithms/docs/manuscript/chapters/07-ibp-normal-forms.tex`, blob `11297bc8b987f7d4abc3dfbfc2cb9aa76cd92dfe` | Normal-form definitions and early Gamma examples; used to exclude already developed directions. |
| Harmonic moving-pole report | `Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/stieltjes-harmonic-identities/sections/harmonic.tex`, blob `51108e8519d46af87dc3682956511fc525cecec3` | Harmonic Gamma ratio, moving-pole boundary, and mixed coefficient context. The new article supplies its own beta normalization check. |
| Gap-six archive | `docs/incoming/ProveIt_Gap_Six_Harmonic_Determinants_2026-10-12.zip`, blob `d7695b94c3117d7bdcb5e75fcf930c410e9c31b6` | README; leading portions of `sections/02_complex_rank.tex` and `sections/03_hahn_and_polylogs.tex`; complete returned `sections/05_audit_and_questions.tex`. Primary local frontier and adjacent-pole comparison. |
| Universal Gamma normal forms | `docs/incoming/ProveIt_Universal_Gamma_Normal_Forms_2026-10-11.zip`, blob `b2a5e51a1b340683721bb803c20410fc3124d9de` | README and stated scope. It already claims the all-coefficient normal-form result. No independent full proof audit of that archive was performed. |
| Gamma normalizations | `docs/incoming/ProveIt_Gamma_Normalizations_and_Colored_Moments_2026-10-12.zip`, blob `a7d997b5d80ab90623ca58864871eb3829089628` | Gamma determinant / normalization section statements and derivation excerpts. It supplies the source-status update for the older K_m question. Its verification programs were not replayed here. |
| Ordered boundary and order-ten archives | Incoming README material; beginning of the ordered Gamma-basis section | Exclusion of earlier solved prefix and normalization questions; not a dependency of the new theorems. |

This is a targeted source audit, not an exhaustive review of all manuscript pages, all incoming packages, or all historical literature. Some long tool returns contained truncated middle sections; those were not treated as fully inspected proofs. All new proofs in the delivered article are written out independently of such omitted sections.

## What is already established in the local predecessors

The gap-six report's Section 2 already establishes ordinary formal harmonic degree equals generic harmonic-pencil rank for complex rational weights. Its Section 3 already gives a fixed-size Hahn formula and an all-particle dilogarithm generator for two adjacent simple poles. Neither statement is relabeled new.

The older mixed Gamma normal-form sector is superseded by the universal Gamma archive. The normalization constants asked for in gap-six Q4 are evaluated in the newer Gamma-normalization archive. These are source-status corrections, not new results of the delivered paper.

## What this continuation adds relative to the inspected frontier

The confluent weighted-minor allocation, its positive marginal-sequence form, its explicit formally sharp single-pole Gamma coefficient, and the cost-preserving exact compiler are developed and proved in the new article. In particular, the dilogarithm family now covers every integral quadratic denominator, including arbitrarily separated simple poles and a double pole, with any polynomial part.

For several simple poles, the exact compression and its normalization, all bordered endpoint jets, and the positive-matrix residue slice are specified. The general Christoffel and determinant-stability methods themselves are classical. The spectral identities provide ordinary all-order Stieltjes–zeta derivative consequences with explicit convergence domains.

The height-one Gamma identity, finite quasi-shuffle algebra, Hahn norms, rational hyperlogarithm integration, and weight-five Euler reductions retain classical attribution. Global historical priority for the new combination and coefficient invariant has not been established.

## Corrections proposed, and corrections not claimed

1. Update the older K_m question to reference the already available normalization archive, after the repository's own intake review.
2. Do not reopen the universal Gamma coefficient problem from older sector-specific files.
3. Update the several-pole research question with the exact advances in this package, but retain minimal classical-polylogarithm depth and intrinsic cutoff-cancellation classification as open.
4. Preserve ordinary transpose, formal-coordinate qualification, collectively removable endpoint terms, and anchored inverse-Euler operators.
5. Do not differentiate an isolated zeta special-value evaluation as though it were a spectral parameter identity.

No false inherited mathematical theorem was identified in the specific dependencies inspected. The three-pole double endpoint pole is a counterexample to a possible naive extrapolation, not to an assertion made by the adjacent-pole report.
