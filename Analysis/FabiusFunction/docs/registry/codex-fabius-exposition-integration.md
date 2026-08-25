# Workstream registry: `codex/fabius-exposition-integration`

This file implements the per-branch registry protocol in
[`../COLLABORATION.md`](../COLLABORATION.md). It is a status and provenance
record, not a mathematical exposition.

```text
SYNC Fabius
branch / worktree / machine: codex/fabius-exposition-integration /
  C:\Users\vresh\.codex\worktrees\8f3f\ProveIt / EVO
fetched main SHA: bc92ae3a36b7a844dbf4a9685d917e21b3ed0aab
HEAD and dirty paths: parent of this registry-only status commit is the
  fast-forwarded main SHA bc92ae3a3; no merge is in progress; apart from this
  registry update, the only dirty paths are two untracked, byte-identical PDF
  build copies named Fabius_Function_and_Rvachev_Up_build.pdf and
  non-formalized-research-frontiers_build.pdf
writing (exact paths):
  Analysis/FabiusFunction/docs/registry/codex-fabius-exposition-integration.md
expected declarations or document claims: none outstanding relative to
  current main; historical branch-only content is inventoried below
completed commits: 150bdcd01 (proof-backed rewrite), bd55f04fe,
  e97e14f14, c2fa48111, 0157e504f, and 5e0505bf2 (successive semantic
  integrations); ccf81cf83 merged the feature tip into main
validated (exact command, SHA/state, exit code): git merge --ff-only
  bc92ae3a36b7a844dbf4a9685d917e21b3ed0aab at the feature tip, exit 0;
  git diff --check and git diff --cached --check at bc92ae3a3, exit 0;
  pdfinfo reports the committed primary as 57 A4 pages / 1,007,180 bytes and
  the committed frontier as 203 A4 pages / 2,169,265 bytes; SHA-256 confirms
  each untracked build copy is identical to its committed PDF. Documentation
  validation recorded at 5e0505bf2 is detailed below.
not yet validated: no fresh exact-SHA aggregate Lean build at bc92ae3a3; no
  post-generalizations rerun of the primary declaration/module citation audit;
  no build was started after the coordinator froze documentation and withheld
  this machine's build token
requested integration or lease: none; the documentation tranche is already
  on main and this workstream should be treated as closed
conflicts / dependencies: no unresolved Git or semantic-document conflict;
  current main contains the feature tip through ccf81cf83. The two redundant
  untracked build copies remain untouched under the preservation freeze.
next bounded step: push this registry-only status commit to the feature branch,
  then wait for the coordinator; do not edit, rebuild, replay, cherry-pick, or
  remerge the exposition tranche
```

Source-only reviewers remained read-only. They did not edit, stage, build,
commit, merge, or push.

## Current disposition

There is no remaining extraction set:

- Feature checkpoint `5e0505bf23ac0e348dea8238af51567fa648e045` is an
  ancestor of current main `bc92ae3a36b7a844dbf4a9685d917e21b3ed0aab`.
- Main merge `ccf81cf8399630b64492460d2b39ccaacc8b191a` has
  `5e0505bf2` as its second parent.
- The primary TeX/PDF, canonical frontier TeX/PDF, and frontier README are
  byte-identical between `5e0505bf2` and `bc92ae3a3`.
- The requested
  `docs/Fabius_Function_and_Rvachev_Up/drafts/` directory is absent.
- Current main preserves the strict placement rules and the live coordinator
  preamble. No stale branch-local coordination wording should be resurrected.

Canonical artifact blob IDs, identical at the feature checkpoint and current
main, are:

| Artifact | Git blob |
| --- | --- |
| Primary TeX | `e3a0df24ef2697d6ad12300ce2e57f22f5fddde8` |
| Primary PDF | `93af1982d22666570eee76314f14251468567381` |
| Frontier TeX | `3108624f90ac806fa3aa3edcc1159afccb8cd64f` |
| Frontier PDF | `0cd676c1d8d1f590acadd813ad42669c8faa5aba` |
| Frontier README | `c3d9bb52c75a04627968d65aa978585a522e1cf3` |

## Historical primary claim inventory

The following is the claim-level delta that the coordinator originally asked
for, comparing feature checkpoint `5e0505bf2` with the then-pinned main
`22d63a9f74a9dd022b243fc3836930ae94354ff9`. Every item is now on current
main. This section is retained only to make the semantic merge auditable.

### Exact Lean-backed statements added or made explicit

- **Probability measure and characteristic function.** The primary records
  absolute continuity and null-set transfer through
  `rvachevMeasure_absolutelyContinuous` and
  `rvachevMeasure_eq_zero_of_volume_eq_zero`, and the positive-frequency
  normalization at `eq:rvachev-charfun` through
  `rvachevMeasure_charFun_pos`.
- **Fourier structure.** It records `rvachevFourier_scaling`,
  `rvachevFourier_analyticOnNhd`, and the exact conjugation, evenness, and
  real-axis identities at `eq:fourier-symmetries` through
  `rvachevFourier_conj`, `rvachevFourier_neg`, and
  `rvachevFourier_ofReal_im_eq_zero`.
- **Totalized inverse endpoints.** It adds the explicit one-sided quotient
  limits at `eq:fabius-inverse-infinite-slopes`, including
  `tendsto_one_sub_fabiusInv_div_one_sub_atTop`, and cites
  `fabiusInv_not_differentiableAt_zero` and
  `fabiusInv_not_differentiableAt_one` rather than inferring endpoint
  nondifferentiability from nearby asymptotics.
- **Elementary/inverse closure.** The rpow interfaces
  `IsElementary.rpow_of_ne_zero`, `IsElementary.rpow_of_pos`, and
  `eqOn_rpow_of_pos` accompany the global exclusions at
  `eq:not-elementary-or-inverse`, backed by
  `fabius_not_isElementaryOrInverse` and
  `fabiusInv_not_isElementaryOrInverse`.
- **Moment and Laplace bridge.** Exact integral and entire-function routing
  uses `integral_even_pow_mul_rvachev_eq_moment`,
  `moment_eq_integral_formula`, `halfMoment_eq_integral_formula_all`, and
  `differentiable_complexGeneratingFunction`. The identities at
  `eq:G-derivative-laplace`, `eq:laplace-reflection`,
  `eq:laplace-midpoint`, and `eq:laplace-shift` are tied to
  `iteratedDeriv_generatingFunction`, `iteratedDeriv_generatingFunction_zero`,
  `fabiusLaplaceMoment_zero_reflection`,
  `fabiusLaplaceMoment_zero_centered_even`,
  `fabiusLaplaceMoment_midpoint_sq_le_all`, and
  `fabiusLaplaceMoment_le_shift`.
- **Reciprocal powers and compositions.** The inverse evaluations at
  `eq:inverse-power-inversion` and `eq:composition-inversion`, including the
  zero index, use `fabiusInv_fabiusAtInverseTwoPow` and
  `fabiusInv_two_pow_choose_mul_fabiusCompositionSum`.
- **Dyadic representation independence.** The statements at
  `eq:dyadic-refine-pow` and `eq:dyadic-rat-invariance` cite
  `fabiusDyadic_refine_pow` and `fabiusDyadic_eq_of_rat_eq`; the route from
  rational evaluation to the analytic function is exposed through
  `fabiusDyadic_cast` and `fabiusDyadic_cast_extended_nat`.
- **Dyadic evaluator certification.** The leading-bit recurrence and evaluator
  are routed through `fabiusTaylorHorner_eq_sum`,
  `fabiusInversePowTwoTable_hasBlockTaylor`,
  `blockTaylor_implies_bitRecurrence`,
  `fabiusInversePowTwoTable_hasBitRecurrence`,
  `fabiusDyadicUnit_eq_fabiusDyadic`, `fabiusDyadicValue`,
  `fabiusDyadicValue_cast`, and
  `fabiusDyadicUnitAux_eq_of_bitRecurrence`. Denominator assertions are routed
  through `rvachevDyadic_mul_denominatorBound_isNatural_all`,
  `moment_mul_common_denominator`,
  `fabiusDyadic_mul_denominatorBound_isInteger`, `proposition_fifteen`, and
  `dyadicDenominator_eq_fabiusDyadicDenominator`.
- **Half-base q-binomial strengthening.** The all-node piecewise evaluation
  and exact vanishing characterization use
  `qBinomial_half_two_pow_sum_eq_ite` and
  `qBinomial_half_two_pow_sum_eq_zero_iff`. Representation/refinement
  invariance uses
  `qBinomialThueMorseDyadicTranslatedFormula_eq_of_rat_eq` and
  `qBinomialThueMorseDyadicTranslatedFormula_refine`.
- **All-real binary reduction.** The finite telescope, infinite sum, and
  parity-power identity use
  `extendedFabius_eq_globalBinaryReductionSum_add_remainder_all`,
  `extendedFabius_eq_tsum_globalBinaryReductionSummand_all`, and
  `globalFabius_eq_tsum_fabiusParityPower_literal_all`. Uniform error and
  convergence are recorded through
  `norm_globalBinaryReductionSum_sub_extendedFabius_le` and
  `globalBinaryReductionSum_tendstoUniformly_extendedFabius`.
- **Complex-q boundary correction.** The primary states only the proved plain
  exponential estimate
  `norm_fabiusComplexShiftSpline_sub_center_le_half_pow_mul_exp`, records
  `fabiusComplexShiftSpline_tendsto_globalFabius_all`, and leaves the sharper
  exp-minus-one estimate on the frontier.
- **Prefix convergence and endpoint failure.** The literal endpoint failure
  subsection `tm:sub-literal-endpoint` cites
  `paperPrefixGridValue_endpoint_not_tendsto_one`. The corrected samples are
  extended to every input at most one, with the exact nonpositive tail at
  `eq:tm-left-tail-exact`, using
  `correctedPrefixGridSample_eq_at_zero_of_nonpos`,
  `correctedPrefixGridSample_zero`,
  `correctedPrefixGridSample_tendsto_of_nonpos`, and
  `correctedPrefixGridSample_tendsto_rvachevUp_of_le_one`.
- **Prefix and Thue--Morse overlays.** Exact theorem bridges cover sign/weight
  recurrences, odd-index first-prefix vanishing, exact-order centered power
  series, finite-product coefficient stabilization, and denominator-cleared
  prefix series through `thueMorseSign_two_mul`,
  `thueMorseSign_two_mul_add_one`, `binaryWeight_two_mul`,
  `binaryWeight_two_mul_add_one`, `iteratedPrefix_one_two_mul_add_one`,
  `order_thueMorseCenteredPowerSeries`,
  `coeff_finite_thueMorse_product`, `iteratedPrefixSeries_eq`,
  `one_sub_X_pow_mul_iteratedPrefixSeries`, and `coeff_eq6_finite`.
- **Lower Lambert calculus.** The derivative statement at
  `eq:lower-lambert-derivative` and its surrounding range/monotonicity facts
  use `lowerLambertW_continuousOn`, `lowerLambertW_strictAntiOn`,
  `lowerLambertW_image`, `lowerLambertW_hasDerivAt`, `deriv_lowerLambertW`,
  and `deriv_lowerLambertW_neg`. The primitive-recursive Thue--Morse evaluator
  uses `tmBitPR`, `tmBitPR_of_pos`, and `tmBitPR_eq_thueMorseBit`.
- **Negative-Laplace derivative.** The full-ray first-derivative expansion at
  `eq:negative-Laplace-first-derivative` is backed by
  `negativeLaplaceLogFirst_sub_periodic_main_isBigO_inv_sq_real` and
  `negativeLaplaceLog_hasDerivAt`.
- **Certified effective dyadic asymptotic.** The explicit threshold and
  rational error in `eq:dyadic-effective-main` and
  `eq:dyadic-effective-bound` use
  `abs_log_fabius_dyadic_sub_explicitCumulantMain_le`,
  `dyadicEndpointSecondOrder_sq_le`, `dyadicHigherLaplaceMoments_le`, and
  `abs_dyadicEndpointLaplaceLogError_add_secondOrder_le_unconditional`.
- **Lambert phase calculus.** The exact image, monotonicity, derivative, and
  sign at `eq:lambert-phase-derivative` cite
  `fabiusLambertPhase_continuousOn`,
  `fabiusLambertPhase_strictAntiOn`, `fabiusLambertPhase_image`,
  `fabiusLambertPhase_hasDerivAt`, `deriv_fabiusLambertPhase`, and
  `deriv_fabiusLambertPhase_neg`. Exact saddle and Bromwich routing uses
  `log_fabius_sub_sharpLambertMain_eq_log_ratio_add_tail`,
  `fabius_bromwich`, and `fabius_bromwich_scaled`.
- **First two saddle corrections and all orders.** The primary records exact
  continuity, periodicity, boundedness, low-order expansion, closed-jet, and
  recursive all-order APIs. The normalization at
  `eq:saddle-coefficient-normalization` uses
  `expCoeff_logCoeff_eq_ite`, `logCoeff_expCoeff_eq_ite`,
  `expSeries_logCoeff_eq_massSeries_normalize_zero`, and
  `logSeries_expCoeff_eq_exponentSeries_normalize_zero`. Exact asymptotic
  endpoints include `fabiusSharpLambertExpansion_two`,
  `fabiusSharpLambertExpansion_three`,
  `log_fabius_sub_twoSaddleCorrections_isBigO`,
  `log_fabius_sub_twoSaddleCorrections_isBigO_negLog`,
  `log_fabius_sub_sharpLambertMain_hasAsymptoticExpansion`, and
  `fabiusLambertPhase_sub_logarithmicApproximation_isBigO`.
- **Signed Poisson identities.** The absolute-scale statements at
  `eq:poisson-support-abs-unscaled` and `eq:poisson-support-abs` preserve the
  oriented frequency and cite
  `rvachev_poisson_support_specialization_unscaled_of_one_half_le_abs` and
  `rvachev_poisson_support_specialization_of_one_half_le_abs`.
- **Signed-global effective continuity.** The modulus at
  `eq:global-effective-modulus` uses
  `extendedFabius_effectivelyUniformContinuous`,
  `fabiusEffectiveUniformModulus`, and
  `globalFabius_effectively_uniformly_continuous`.

### Fail-closed rewrites of material already present on pinned main

The branch also made important placement corrections where the underlying
mathematics, but not the exact proof boundary, already appeared on `22d63a9f`:

- long hand derivations of the negative-Laplace, Mellin, saddle, and all-order
  material were compressed into the literal public Lean API;
- uncertified numerical specializations were withheld even when a generic
  evaluator could compute them;
- the complex-shift exp-minus-one sharpening was moved to the gap register;
- the right-endpoint asymptotic-transfer narrative was not inferred merely
  from symmetry;
- stronger higher-phase, ordered-composition, uniqueness, numerical,
  logarithmic-leading-derivative, and limit-set claims remained frontier-side;
  and
- duplicate exposition was synthesized rather than retained merely because it
  came from a separate draft.

## Historical canonical-frontier inventory

This is the branch-only frontier delta relative to `22d63a9f`. It is now
present verbatim on current main.

- **New provenance object.** The only added source snapshot was
  `Primary_Exposition_Gap_Register/Primary_Exposition_Gap_Register.tex`, SHA-256
  `06c7b888d9601b67ad7a5c0aee3f087d44d9ecaaa9abfb3bf3edfda4bd29c0d1`,
  under `\part{Primary Exposition Gap Register}`. The other eleven source
  snapshots and hashes already existed on pinned main.
- **Repeated-integration coupling warning.** The branch preserves the warning
  that reordering yields an almost-sure coupling of laws, whereas the original
  forward recursion continually inserts new noise and need not converge
  pathwise.
- **Summatory Thue--Morse prefix lemma.** The exact adjacent-pair cancellation
  and prefix bound are retained at `repeated2:lem:TM-prefix` and
  `repeated2:eq:TM-prefix`.
- **Restored figures.** Unique embedded plots survive at
  `repeated2:fig:iterates-comparison`,
  `repeated2:fig:scaled-errors-supplement`, and
  `tmrates:fig:three-scales-supplement`.
- **Generic q-leading extractor.** The arbitrary-base residue/divided-
  difference extension is preserved at
  `dyadicq:eq:q-leading-extractor-general`,
  `dyadicq:eq:barycentric-denominator`, and `dyadicq:eq:q-survivor`.
- **Thue--Morse differential operator.** The operator, factorization,
  annihilation, first surviving moment, leading coefficient, and symmetric
  `sinhc` form are retained at `dyadicq:eq:TM-operator`,
  `dyadicq:eq:TM-factorization`, `dyadicq:eq:first-TM-moment`,
  `dyadicq:eq:TM-degree-n`, `dyadicq:eq:TM-leading-coeff`, and
  `dyadicq:eq:TM-sinhc`.
- **Appell extensions.** The addition law, arbitrary-scale row identity, and
  explicit low rows are preserved around `dyadicq:eq:Appell-addition` and
  `dyadicq:eq:R-Appell-general`.
- **Direct q-Appell and digit-q forms.** Both centered and raw versions,
  common-translation gauge, finite-row warning, digit-sparse substitution, and
  dyadic termination are retained at
  `dyadicq:thm:centered-q-Appell`, `dyadicq:eq:centered-q-Appell`,
  `dyadicq:thm:raw-q-Appell`, `dyadicq:eq:raw-q-Appell`,
  `dyadicq:eq:centered-digit-q`, and `dyadicq:eq:raw-digit-q`.
- **Finite row weights and contour form.** Higher factorial moments, the
  symmetric row-weight formula `dyadicq:eq:weights-symmetric`, and the
  arbitrary-argument contour representation `dyadicq:eq:LX` /
  `dyadicq:eq:Bromwich` remain explicitly frontier material.
- **Computational guidance.** The sparse-bit evaluator is described only as an
  arithmetic-operation count, not a bit-complexity theorem, and carries a
  conditioning/common-translation warning.
- **Complex-shift status correction.** The actually proved plain-exponential
  estimate `dyadicweb:eq:shifted-spline-bound-formal` is separated from the
  unformalized exp-minus-one sharpening and downstream constants. The warning
  records the two top exponent maximizers at the smallest relevant scale.
- **Formal-status overlays.** Existing formulas receive exact source pointers
  for translated-polynomial invariance, recurrence/product identities, phase
  locking, and the relevant module map, without promoting adjacent deductions.

### Primary Gap Register obligations

The consolidated register records claim-level promotion obligations for:

- shifted-weight Fourier decay on the whole real line;
- named exact rational evaluator specializations;
- a precise popcount-based evaluator-cost theorem, including endpoint rules;
- Taylor-integral/block-substitution analytic derivations;
- the all-real exp-minus-one complex-shift spline estimate;
- stars-and-bars and convolution interpretations of prefix kernels;
- literal iterated derivatives of the Thue--Morse block polynomial at one;
- construction of an actual infinite formal product, rather than finite
  coefficient stabilization alone; and
- the formal-background crosswalk explaining why nearby declarations do not
  yet discharge those obligations.

The register's promotion rule requires exact hypotheses, normalization,
domain, conclusion, declaration, and module. Discharging one obligation does
not erase adjacent exploratory material.

## Draft disposition and provenance

The requested primary-exposition inbox was dispositioned before the final
synthesis:

- `69ba1e6bd4c9107fd6416d79f42c19ed132717c1` moved the two “missing parts”
  drafts into the stable Integration and Inverse/Saddle frontier dossiers and
  moved Small-Argument Asymptotics under the frontier tree. It then removed
  the empty target `drafts/` directory.
- `53c187fb0806299bb186d0e43258d5a106a856ad` replaced “missing parts” branding
  with research-frontier notices and explicit outstanding obligations.
- `e97e14f14d31df1c6cdb784b2b53cc32b2ecca03` absorbed those dossiers and the
  other frontier notebooks into the single canonical volume and deleted the
  obsolete standalone copies.

The canonical frontier README records SHA-256 provenance for twelve absorbed
sources: eleven notebooks and the later gap register. In particular:

- Small-Argument Asymptotics:
  `85f51a20fc7b6bdf3b1d049ec4506f508aee3c4cd70554e6a68cbcc30977cb0b`;
- Fabius Integration Research Frontiers:
  `21222ae5a8c64cf556dac562fd66943ae0b6ed881408e23e37edfa9113bdecbd`;
- Fabius Inverse and Saddle Research Frontiers:
  `f9d8605761aaaa1b2c2af83e3c5c55dcd6acfc847402163458b03b68c7b35ff8`;
  and
- Primary Exposition Gap Register:
  `06c7b888d9601b67ad7a5c0aee3f087d44d9ecaaa9abfb3bf3edfda4bd29c0d1`.

A separate repository path `Analysis/FabiusFunction/docs/drafts/` contains two
Wikipedia-draft bookkeeping files. It is not the processed primary-exposition
inbox named in this workstream and was outside this task.

## Placement rules now on main

The requested policy is preserved in all three authoritative locations:

- `Analysis/FabiusFunction/AGENTS.md` requires an actual proved Lean
  counterpart for every mathematical assertion in the primary, sends every
  nonliteral or merely plausible consequence to the frontier, and treats the
  primary draft directory as a temporary claim-by-claim inbox.
- `Analysis/FabiusFunction/README.md` repeats the exact-counterpart,
  frontier-placement, provenance, and draft-deletion rules for contributors.
- `Analysis/FabiusFunction/docs/non-formalized-research-frontiers/README.md`
  defines claim-by-claim promotion, requires current-source inspection and
  organic nonduplicative integration, and requires paired PDF rebuild and
  inspection when a source changes.

## Validation ledger and epistemic limits

The immutable feature checkpoints record progressively broader documentation
validation. The strongest pre-curvature static audit is at `0157e504f`:

- primary: 57 A4 pages;
- frontier: 202 A4 pages;
- exactly three `pdflatex` passes for each;
- rendered inspection of all new clusters, restored plots, q-Appell and
  complex-shift material, and the gap register;
- 427 Lean citations, 401 unique first-token declarations;
- 189 module mentions, 96 unique;
- no missing public declaration, module, label, reference, bibliography key,
  control character, or conflict marker; and
- no source occurrence of a declared `axiom`, `opaque`, `sorry`, or `admit`.

At final feature checkpoint `5e0505bf2`, the curvature reconciliation records:

- exactly three `pdflatex` passes per document;
- a 57-page primary and 203-page frontier;
- rendered contact-sheet inspection;
- no unresolved references, rerun requests, overfull boxes, multiply-defined
  labels, or duplicate destinations; and
- clean `git diff --cached --check`.

The curvature additions were independently source-audited against exact public
declarations in `Convexity.lean` and `FabiusInverse.lean`, but the final
checkpoint did not record a fresh numbered declaration/module citation audit
after that merge. No feature commit records a fresh aggregate
`lake build +FabiusFunction` at its immutable tip. The later generalizations
merge also lacks a fresh aggregate build at current main.

The documentation baseline at `0157e504f` reported one inherited upstream
regression: `SaddleExpansionAlgebra.lean` had 13 undocumented declarations
against a baseline of 12. No Lean source was edited to hide that result.

Current untracked build copies are redundant, not divergent:

- primary build-copy SHA-256:
  `59B8B06825F89B81A33F6352196CEBE7C0CAF4C436170FEB15FFDD9336E72908`;
- frontier build-copy SHA-256:
  `CD91C680DFA7D96F110106F7A6ADCACC5CBA10E188DF1BD0A4484218FA8FA39C`.

Each hash exactly matches the corresponding committed canonical PDF. The
copies are deliberately neither staged nor removed under the freeze.
