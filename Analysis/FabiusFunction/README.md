# Fabius function

> [!CAUTION]
> **Never start Lean or Lake builds in parallel, and never start a second
> build while one is already running.** Run exactly one
> `lake build +FabiusFunction.Module` at a time, with one target. Do not
> launch background build loops, pass a batch of targets, or use parallel
> runners such as `xargs -P`.
>
> One invocation is not by itself one process: Lake sizes its worker pool to
> hardware concurrency and starts one `lean.exe` **per core** whenever the
> target has a stale dependency set. On this machine several agent sessions
> share 13 GB, so that fan-out starves all of them. Set both limits on every
> build:
>
> ```bash
> LAKE_JOBS=1 LEAN_NUM_THREADS=0 lake build <one target>
> ```
>
> `LAKE_JOBS` bounds the number of `lean.exe` processes and
> `LEAN_NUM_THREADS` bounds the threads inside each one; they are
> independent, so set both. Lake `5.0.0` accepts neither `-j` nor `--jobs`,
> so these environment variables are the only control. Measured 2026-08-27:
> a facade build over a stale dependency set spawned **11 concurrent
> `lean.exe`**, and **exactly one** under `LAKE_JOBS=1`.
>
> Starvation does not look like starvation. It surfaces as errors that read
> like corruption:
>
> ```
> failed to read file '...\Mathlib\...\Basic.olean'
> libc++abi: terminating due to uncaught exception of type std::bad_alloc
> ```
>
> These are out-of-memory symptoms, **not** broken proofs -- the same module
> built by itself succeeds. Never "fix" them by editing Lean sources.
>
> Before starting, check that nothing else -- including another agent session
> in a sibling worktree -- is already building; after interrupting a build,
> check for survivors, because stopping a task does not reliably kill the
> processes it spawned:
>
> ```powershell
> Get-Process lean,lake -ErrorAction SilentlyContinue
> ```
>
> If a build is running, wait for it rather than racing it.

> **Multi-agent coordination: OFF.**  A single switch file,
> [`AGENTS/STATUS.md`](AGENTS/STATUS.md), states
> whether the coordination framework is in effect; flipping it — plus
> creating or deleting the off-`main` board branch it names — is the entire
> enable/disable procedure.  The lightweight protocol it switches is
> [`AGENTS/PROTOCOL.md`](AGENTS/PROTOCOL.md).  The
> engineering policies in [`AGENTS.md`](AGENTS.md) (documentation, Lean
> builds, invariants) apply at all times.

This project formalizes the Fabius function and the results in both papers by
Juan Arias de Reyna:

- [*An infinitely differentiable function with compact support: Definition
  and Properties*](https://arxiv.org/abs/1702.05442); repository copies of
  the [TeX source](docs/papers/arXiv-1702.05442v1/09-Function.tex) and
  [published PDF](docs/papers/arXiv-1702.05442v1/1702.05442v1.pdf) are
  available locally;
- [*Arithmetic of the Fabius function*](https://arxiv.org/abs/1702.06487),
  version 3; repository copies of the
  [TeX source](docs/papers/arXiv-1702.06487v3/157-Arithmetic-v3.tex) and
  [published PDF](docs/papers/arXiv-1702.06487v3/1702.06487v3.pdf) are
  available locally.

A self-contained human-readable synthesis of the formal development is also
available as [LaTeX source](docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex)
and as a [rendered PDF](docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.pdf).
That primary exposition is deliberately proof-backed: every mathematical claim
in it must have a proved counterpart in the Lean development.

The formally proved small-argument hierarchy—including the corrected sharp
asymptotic, the general coefficient algebra for the recursive all-orders
expansion, and the first two explicit periodic saddle corrections—is integrated
into the primary exposition. Exploratory derivations, the small-argument
notebook, and the primary-exposition gap register are preserved in the canonical
[research-frontier LaTeX volume](docs/non-formalized-research-frontiers/non-formalized-research-frontiers.tex)
([PDF](docs/non-formalized-research-frontiers/non-formalized-research-frontiers.pdf)).
That volume labels claims still awaiting literal Lean counterparts and records
their exact outstanding proof obligations.

Non-elementarity is treated in
[*The Fabius Function and Its Inverse are Not Elementary*](docs/Non_Elementarity_of_the_Fabius_Function/Non_Elementarity_of_the_Fabius_Function.tex)
([PDF](docs/Non_Elementarity_of_the_Fabius_Function/Non_Elementarity_of_the_Fabius_Function.pdf)):
the class of elementary functions of one real variable is formalized, every
member of it is proved real analytic on a dense open subset of the line, and
this is combined with nowhere analyticity to show that no elementary function
agrees with the Fabius function on any subset of `[0,1]` with nonempty
interior.  The
same conclusion is proved for a class the inductive definition does not
reach — any continuous branch of a polynomial equation whose coefficients are
elementary and whose leading coefficient vanishes nowhere — which covers the
algebraic functions that are not expressible by radicals.  The inverse Fabius
function is treated too: it is real analytic at no point of `[0,1]` either,
hence not elementary, and neither it nor the Fabius function is reachable once
the class is closed under continuous inverse branches at any depth — a class
containing the Lambert `W` function.

The development contains executable exact arithmetic.  The evaluator and its
analytic correctness at every dyadic, the canonical function's existence and
uniqueness, the moment and denominator arithmetic, the global differential
identities, Taylor reduction, the Fourier and entire-series identities,
probability and weak-convergence constructions, polynomial step
approximants, Poisson summation, and every theorem, lemma, corollary, and
prose proposition in both papers are checked without `sorry`.  The asymptotic
layer additionally proves the corrected sharp small-argument expansion with
its nonconstant Gamma--zeta periodic term, together with its complete
all-orders saddle expansion.

Several agents sometimes develop this directory concurrently in separate
worktrees.  If you are one of them, read [`AGENTS.md`](AGENTS.md) first;
whether the multi-agent coordination framework is currently in effect is
stated by the single switch file [`AGENTS/STATUS.md`](AGENTS/STATUS.md).

## Design

The formalization separates two functions that the sources both call `F`:

- `BoundedFabius = ℝ → Set.Icc 0 1` is the CDF-style function requested for
  this project.  `IsFabius F` says that it is zero on `(-∞,0]`, one on
  `[1,∞)`, smooth, symmetric on `[0,1]`, and satisfies the differential
  equation on `[0,1/2]`.  The existence/uniqueness theorem selects the
  canonical `fabius`, constructed as the fixed point of an integral
  contraction on continuous symmetric unit-interval-valued functions.
- `extendedFabius F : ℝ → ℝ` is the signed global extension used in the
  paper.  It is defined by the locally finite Thue--Morse translate sum in
  equation (1).  It agrees with the bounded function on `[0,1]` but can be
  negative outside it.

Rvachev's compactly supported `up` function is represented by `rvachevUp F`,
which folds the bounded candidate about zero.  Its evenness is structural:
`rvachevUp_even` holds for every `BoundedFabius`, without the Fabius equations.
Support does use `IsFabius`: `Basic.lean` gives the lightweight inclusion
`support_rvachev_subset_Ioo`, `Monotonicity.lean` strengthens it to the exact
pointwise identity `support_rvachevUp`, and `tsupport_rvachev` identifies the
topological support with the closed interval `[-1,1]`.

The arithmetic layer is independent of real analysis:

- `moment`, `halfMoment : ℕ → ℚ` are the rational sequences `c_n`, `d_n`.
- `momentNumerator`, `halfMomentNumerator : ℕ → ℕ` are `F_n`, `G_n`, defined
  by division-free recurrences.
- `fabiusDyadicValue n a : ℚ` computes the bounded Fabius function exactly at
  the signed dyadic argument `a / 2^n`; `extendedFabiusDyadicValue` computes
  the paper's signed global extension.
- `evalFabiusDyadic : ℚ → Option ℚ` is the convenient rational-input wrapper.
  It returns `none` exactly when the reduced denominator is not a power of two.
- `fabiusDyadic` remains the independent closed formula from equation (32),
  while `rvachevDyadic` evaluates exact dyadic values of `up`.
- `reshetnikov : ℕ → ℚ` remains rational until its integrality is proved.
- `dyadicDenominator : ℕ → ℕ` is the finite LCM `D_n`.

This makes denominator, divisibility, parity, and valuation proofs live in
`ℚ` and `ℕ`; named bridge theorems connect them to the analytic functions.
The Fourier transform, sinc product, inversion integral, moment series, and
complex exponential generating function are also represented explicitly.

## Using the Lean library

From the repository root, the complete public surface is checked with

```sh
LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake build +FabiusFunction
```

Use `import FabiusFunction` when downstream code needs the entire development.
For a smaller dependency footprint, the following imports are useful entry
points:

| Purpose | Focused import | Good starting declarations |
| --- | --- | --- |
| Definitions, the bounded characterization, folded `up`, and the global first-jet reflection law | `FabiusFunction.Basic`, `FabiusFunction.Differential` | `BoundedFabius`, `IsFabius`, `rvachevUp`, `rvachevUp_even`, `rvachevUp_eq_zero_of_not_mem_Ioo`, `support_rvachev_subset_Ioo`, `rvachev_hasDerivAt`, `fabius_hasDerivAt`, `deriv_fabiusReal`, `deriv_fabiusReal_one_sub` |
| Sharp bounded derivatives and the exact zero-interleaved Thue--Morse pattern on every matched dyadic grid | `FabiusFunction.BoundedDerivatives` | `iteratedDeriv_fabiusReal_of_lt_one`, `iteratedDeriv_fabiusReal_dyadicGrid_eq_ite`, `iteratedDeriv_fabiusReal_dyadicGrid_eq_zero_iff`, `abs_iteratedDeriv_fabiusReal_dyadicGrid_of_odd`, `abs_iteratedDeriv_fabiusReal_le`, `isGreatest_abs_iteratedDeriv_fabiusReal` |
| Existence, uniqueness, and the canonical functions | `FabiusFunction.PaperStatements` | `existsUnique_fabius`, `fabius`, `fabius_spec`, `globalFabius` |
| Original compact-support characterization and bounded/original bridge | `FabiusFunction.OriginalUniqueness` | `IsOriginalFabius`, `IsOriginalFabius.mk_of_derivative_law`, `IsFabius.isOriginalFabius_rvachevUp`, `rvachevUp_eq_iff_eqOn_Iic_one`, `isFabius_iff_isOriginalFabius_rvachevUp_and_rightTail`, `isOriginalFabius_iff_existsUnique_isFabius` |
| Product-probability and CDF representations | `FabiusFunction.ProbabilityRepresentation` | `weightedSumCDF_eq_fabiusReal`, `fabiusReal_eq_weightedSum_probability`, `rvachevUp_eq_weightedSumCDF`, `rvachevUp_eq_weightedSum_probability_global` |
| Exact midpoint--endpoint value and first-jet transfer, complete higher midpoint jet, centered mass, and weighted primitive kernels | `FabiusFunction.MidpointEndpointTransfer` | `fabiusReal_midpoint_add_eq`, `fabiusReal_midpoint_sub_eq`, `deriv_fabiusReal_midpoint_add_eq`, `deriv_fabiusReal_midpoint_sub_eq`, `iteratedDeriv_fabiusReal_half_eq_zero_of_two_le`, `intervalIntegral_fabiusReal_centered`, `intervalIntegral_mul_fabiusReal_midpoint_add_defect_eq_neg`, `intervalIntegral_mul_fabiusReal_midpoint_sub_defect_eq`, `intervalIntegral_fabiusReal_midpoint_add_defect_eq_neg`, `intervalIntegral_repeatedPrimitiveKernel_fabiusReal_midpoint_add_defect_eq_neg` |
| Exact inverse-midpoint offset and defect fixed points, endpoint normalizations, positive-cell enclosures, and global oddness | `FabiusFunction.InverseMidpointDefect` | `fabiusInvMidpointOffset`, `fabiusInvMidpointDefect`, `fabiusInvMidpointOffset_zero`, `fabiusInvMidpointDefect_zero`, `fabiusInvMidpointOffset_half`, `fabiusInvMidpointDefect_half`, `fabiusInvMidpointOffset_mem_Icc`, `fabiusInvMidpointOffset_equation`, `fabiusInvMidpointOffset_fixedPoint`, `fabiusInvMidpointDefect_eq_half_fabiusReal`, `fabiusInvMidpointDefect_fixedPoint`, `fabiusInvMidpointDefect_mem_Icc`, `fabiusInvMidpointOffset_neg`, `fabiusInvMidpointDefect_neg` |
| Exact finite-spline cell around `1/4`, with two-sided reflection, curvature, and conditional inverse identities | `FabiusFunction.QuarterSplineLocalPolynomial`, `FabiusFunction.QuarterSplineTwoSided` | `reportFiniteFabiusApproximant_quarter_twoSided`, `reportFiniteFabiusApproximant_quarter_reflection`, `reportFiniteFabiusApproximant_quarter_centralSecondDifference`, `strictMonoOn_reportFiniteFabiusApproximant_quarter_twoSided`, `reportFiniteFabiusApproximant_quarterPrefix_value`, `reportFiniteFabiusApproximant_quarterPrefix_quantile` |
| Weighted-partition exponential coefficients over commutative `ℚ`-algebras | `FabiusFunction.ExponentialPartition`, `FabiusFunction.ExponentialBell` | `partitionExpSum_recurrence`, `partitionExpSum_succ`, `partitionExpSum_eq_sum_div`, `partitionExpSum_eq_expCoeff` |
| Complete Bell and moment--cumulant transforms over commutative `ℚ`-algebras | `FabiusFunction.MomentCumulantAlgebra` | `factorialNormalize`, `completeBellPolynomial`, `momentCumulant`, `completeBellPolynomial_succ`, `completeBellPolynomial_momentCumulant`, `momentCumulant_completeBellPolynomial` |
| Full-order centered Rvachev moment, logarithmic-coefficient, and cumulant parity, with positive even-order Bernoulli--Mersenne cumulants | `FabiusFunction.CenteredMomentParity`, `FabiusFunction.SinhDivBernoulliLog` | `centeredRvachevFullMoment_even`, `centeredRvachevFullMoment_odd`, `centeredRvachevFullLogCoefficient_even`, `centeredRvachevFullLogCoefficient_odd`, `centeredRvachevFullCumulant_even`, `centeredRvachevFullCumulant_odd`, `centeredRvachevEvenCumulant_eq_bernoulliMersenne` |
| Finite polynomial integrals from raw moments and formal cumulants | `FabiusFunction.PolynomialExpectationCumulant` | `integral_eval₂_eq_sum_moment`, `integral_eval₂_eq_sum_completeBell_momentCumulant_with_mass_correction`, `integral_eval₂_eq_sum_completeBell_momentCumulant_of_moment_zero_eq_one`, `integral_eval₂_eq_sum_completeBell_momentCumulant` |
| Universal endpoint-transfer polynomials and their formal exponential series | `FabiusFunction.EndpointTransferPolynomials` | `endpointTransferPolynomial_succ`, `endpointTransferPolynomial_eq_partitionExpSum`, `endpointTransferSeries_eq_exp_subst`, `aeval_endpointTransferPolynomial`, `map_endpointTransferSeries` |
| Complete homogeneous evaluations, denominator-free geometric principal specialization, and Gaussian symmetry | `FabiusFunction.CompleteHomogeneous`, `FabiusFunction.GeometricCompleteHomogeneous` | `completeHomogeneousEval_eq_eval_hsymm`, `completeHomogeneousEval_smul`, `completeHomogeneousEval_option_zero`, `completeHomogeneousEval_fin_succ`, `completeHomogeneousEval_geometric`, `completeHomogeneousEval_scaled_geometric`, `completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial`, `completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial_degree`, `gaussianBinomial_add_symm`, `gaussianBinomial_symm` |
| Every residual moment of finite interpolation and geometric Richardson rows | `FabiusFunction.LagrangeResidualMoments`, `FabiusFunction.GeometricResidualMoments` | `sum_weight_mul_pow_card_add`, `sum_lagrangeEvalWeight_mul_pow_card_add`, `sum_weight_mul_geometric_pow_of_pos`, `sum_weight_mul_scaled_geometric_pow_succ_add`, `sum_weight_mul_scaled_geometric_pow_of_pos`, `sum_geometricLagrangeWeight_mul_pow_of_pos`, `sum_geometricLagrangeWeight_mul_shifted_pow_of_pos` |
| Geometric Richardson filters, Gaussian coefficients, all residual moments, and finite conditioning | `FabiusFunction.GeometricQBinomialLagrange`, `FabiusFunction.GeometricRichardson`, `FabiusFunction.GeometricLagrangeWeights`, `FabiusFunction.GeometricLagrangeQBinomial`, `FabiusFunction.GeometricLagrangeQMoments` | `reversed_finite_qBinomial_theorem`, `sum_geometricLagrangeWeight_mul_pow_eq_gaussianBinomial`, `geometricLagrangeWeightPolynomial_eq_forwardGeometricRichardsonPolynomial`, `geometricLagrangeQMoment_eq_residual_qBinomial`, `sum_abs_geometricLagrangeWeight_eq_prod`; the rational closed forms use their stated nonzero-base and nonvanishing finite-denominator hypotheses, while sign and variation assume `0 < q < 1` |
| Report-facing geometric complete-homogeneous bridges | `FabiusFunction.GeometricLagrangeCompleteHomogeneous` | `completeHomogeneousEvalOn_geometric_range`, `sum_geometricLagrangeWeight_mul_pow_succ_add_eq_gaussianBinomial`, `geometricLagrangeQMoment_eq_residual_qBinomial_via_completeHomogeneous` |
| Formal geometric Richardson filters and the quarter Catalan--Gaussian specialization | `FabiusFunction.QuarterCatalanRichardson` | `finiteRescaleFilter_coeff`, `geometricRichardsonPowerSeriesFilter_coeff_eq_qBinomial`, `quarterCatalanRichardsonFilter_coeff_eq_zero_of_le`, `quarterCatalanRichardsonFilter_coeff_eq_qBinomial`, `quarterCatalanRichardsonFilter_firstUncancelled_coeff` |
| Exact lower-Lambert phase locking and reciprocal-grid Richardson moments | `FabiusFunction.LambertPhaseLockedRichardson` | `fabiusLambertPhase_phaseLockedNode`, `Periodic.apply_fabiusLambertPhase_phaseLockedNode`, `shiftedReciprocalLagrangeWeight_eq_choose`, `sum_shiftedReciprocalLagrangeWeight_mul_periodicPhaseLocked`, `sum_shiftedReciprocalLagrangeWeight_mul_invPow_card_add`, `sum_shiftedReciprocalLagrangeWeight_mul_invPow_eq_completeHomogeneous`, `sum_shiftedReciprocalLagrangeWeight_residual` |
| Generic unit-interval Laplace-moment bounds | `FabiusFunction.UnitLaplaceMomentBounds` | `unitLaplaceMoment_midpoint_sq_le_all`, `unitLaplaceMoment_le_of_tilt_sub`, `pow_mul_exp_neg_le_factorial`, `fabiusLaplaceMoment_midpoint_sq_le_all`, `fabiusLaplaceMoment_le_of_tilt_sub` |
| Exact dyadic computation and analytic correctness | `FabiusFunction.DyadicAnalytic`, `FabiusFunction.GlobalDyadic` | `fabiusDyadicValue`, `evalFabiusDyadic`, `fabiusDyadicUnit_cast`, `extendedFabiusDyadicValue_cast` |
| First and second published papers | `FabiusFunction.Paper05442`, `FabiusFunction.Paper06487` | the theorem maps in the module docstrings and [`docs/PAPER_COVERAGE.md`](docs/PAPER_COVERAGE.md) |
| Corrected sharp and all-orders asymptotics | `FabiusFunction.PaperFabiusAsymptotic` | `abs_log_fabius_dyadic_sub_explicitCumulantMain_le`, `log_fabius_sub_sharpLambertMain_hasAsymptoticExpansion`, `fabiusSharpLambertExpansion_two` |
| Fourier--Legendre expansions | `FabiusFunction.FabiusTranslatedLegendreSeries`, `FabiusFunction.FabiusLegendreLeastSquares` | `hasSum_canonical_rvachevLegendreSeries_formula`, `rvachevLegendrePartialSum_pythagorean` |
| Denominator-cleared centered sinc shells and their Thue--Morse zero classification | `FabiusFunction.CenteredRvachevThueMorseFourier` | `centeredSincPartialProduct_dyadic_eq_thueMorse`, `rvachevFourierProduct_dyadic_eq_thueMorse`, `rvachevFourierProduct_dyadic_eq_zero_iff_thueMorse`, `rvachevFourierProduct_dyadic_eq_zero_iff_exists` |
| Finite odd-coset DFT traces and odd-coset-filtered convolution (Ramanujan at power-of-two moduli) | `FabiusFunction.HalfIntegerOddDFT` | `sum_odd_powers_eq_root_filter`, `oddDFT_add_period`, `oddDFTPowerTrace_eq_ramanujanConvolution`, `normalizedOddDFTPowerTrace_eq_two_mul_half` |
| Inverse construction, exact smoothness locus, interior calculus, curvature, and endpoint steepness | `FabiusFunction.FabiusInverse` | `fabiusInv`, `fabiusReal_fabiusInv`, `fabiusInv_hasDerivAt`, `deriv_fabiusInv_eq_inv_two_mul_rvachevUp`, `deriv_fabiusInv_pos`, `fabiusInv_contDiffOn_Ioo`, `fabiusInv_contDiffAt_infty_iff`, `fabiusInv_differentiableAt_iff`, `deriv_deriv_fabiusInv`, `deriv_fabiusInv_half`, `deriv_deriv_fabiusInv_half`, `deriv_deriv_fabiusInv_neg_iff`, `deriv_deriv_fabiusInv_pos_iff`, `deriv_deriv_fabiusInv_eq_zero_iff`, `strictConcaveOn_fabiusInv_firstHalf`, `strictConvexOn_fabiusInv_secondHalf`, `id_isLittleO_fabiusInv_pow_at_zero_right`, `one_sub_isLittleO_one_sub_fabiusInv_pow_at_one_left`, `tendsto_deriv_fabiusInv_atTop_at_zero_right`, `tendsto_deriv_fabiusInv_atTop_at_one_left` |
| Elementary functions and non-elementarity | `FabiusFunction.ElementaryFunction`, `FabiusFunction.AlgebraicBranch`, `FabiusFunction.InverseBranch`, `FabiusFunction.NotElementary`, `FabiusFunction.InverseNotElementary` | `IsElementary`, `IsElementary.comp`, `IsElementary.rpow_of_ne_zero`, `IsElementary.dense_analyticLocus`, `analyticDenseOn_of_algebraic`, `canonical_fabius_not_isElementary_on_Ioo`, `canonical_fabius_not_isElementary`, `canonical_fabius_not_algebraicBranch_on_Ioo`, `IsElementaryOrInverse`, `fabiusInv_not_analyticAt`, `canonical_fabiusInv_not_isElementary_on_Ioo`, `canonical_fabiusInv_not_isElementaryOrInverse_on_Ioo` |
| Computable-real-function theorems | `FabiusFunction.FabiusComputableSpline` | `fabiusSplineApproxPR_computable`, `extendedFabiusSplineApproxPR_computable`, `fabius_isComputableRealFunction`, `globalFabius_isComputableRealFunction` |

The frontier-facing focused imports above expose exact finite or formal
algebra, and their names should not be read as stronger analytic conclusions.
The quarter-cell theorems concern the finite spline `reportFiniteFabiusApproximant`,
not a constructed finite inverse `G_n`; the Catalan--Gaussian filter is an
identity in `ℚ[[Q]]`, without convergence or an error bound.  The centered
Thue--Morse shell concerns the standalone sinc-product model, while the odd
DFT module is finite character algebra and does not prove a half-integer
aliasing formula or alias-error estimate.  Likewise, the geometric principal
specialization proves finite residual moments, not spectral-tail convergence,
and the Lambert module proves exact phase locking and interpolation identities,
not extraction of a periodic saddle coefficient or a weighted asymptotic
remainder.  The full-order centered parity API is coefficientwise formal
algebra; its even-index bridges identify it with the already established
compressed moment and cumulant families.

Most analytic theorems first appear in a reusable form with arguments
`(F : BoundedFabius) (hF : IsFabius F)`.  Canonical corollaries specialize
these results to `fabius` and `fabius_spec`; `globalFabius` denotes the signed
extension and is intentionally different from the bounded, clamped function
outside `[0,1]`.  Range facts such as `rvachevUp_nonneg`,
`rvachevUp_le_one`, and `norm_coe_rvachevUp_le_one` need no `IsFabius`
hypothesis because they follow directly from the codomain.

The probability API uses “global” in a deliberately different sense from
`globalFabius`: it means that a formula holds for every real argument.  If `X`
is the weighted sum of independent uniform coordinates, then
`fabiusReal F x = P[X ≤ x]` and
`rvachevUp F x = P[X ≤ 1 - |x|]` for every `x : ℝ`.  These identities describe
the bounded CDF and its folded bump, not the signed extension
`extendedFabius F`; real-valued and native `ℝ≥0∞` measure forms are both
available.

The naming scheme distinguishes convergence objects and numeric identities:
`*_hasSum` retains the summability witness, while `*_eq_tsum` gives the
corresponding equality; `*_cast` bridges exact rational formulas to analysis;
and `*_zpow` uses integer exponents so inverse powers remain visible without
division side conditions.  The module docstrings state endpoint conventions
and any corrections to the printed sources.

## Computability as a real function

`FabiusComputability.lean` formalizes the two clauses in the
Grzegorczyk definition of a computable real function.  A computable real
sequence is presented by one recursive fast dyadic name, uniform in the
sequence index and precision: at precision `p`, a signed-natural pair
`(a,b)` denotes `(a-b)/2^p` with error at most `2^-p`.
`SequentiallyComputable` says that every such sequence is mapped to another
such sequence.  `EffectivelyUniformContinuous` uses a recursive positive
modulus and the source's reciprocal convention for positive precision
indices.

The algorithms in `FabiusComputableSpline.lean` are entirely natural-number
and primitive-recursive.  Both compute the Thue--Morse bit, evaluate the
finite centered uniform spline on the dyadic grid of order `p+3`, and round
to the nearest dyadic of order `p`.  The bounded evaluator clamps its input
to `[0,1]`; the signed-global evaluator instead rounds an unrestricted signed
rational spline code, with negative input names collapsing to the exact zero
tail.  Each has proved evaluator error `5 * 2^(-(p+3))`.  Propagating the
input-name error through the global `2`-Lipschitz bound costs another
`2 * 2^(-(p+3))`, so the output error is within `2^-p`.  This proves both
`fabius_sequentiallyComputable` and `globalFabius_sequentiallyComputable`.
The primitive-recursive modulus `d(n)=2n` proves effective uniform continuity;
`fabius_isComputableRealFunction` and
`globalFabius_isComputableRealFunction` package both clauses for the canonical
bounded and signed-global functions.  These are computability certificates,
not practical running-time claims: the unrestricted positive grid numerator
controls the length of a finite primitive-recursive fold.  The underlying
analytic approximation is stronger than the computability application needs:
`Fabius.abs_fabiusUniformSpline_sub_extendedFabius_le` gives the global error
`2^-p`, and `Fabius.fabiusUniformSpline_tendstoUniformly_globalFabius`
packages uniform convergence on all of `ℝ`; the diagonal theorem
`Fabius.fabiusUniformSpline_tendsto_extendedFabius_of_tendsto` also allows the
evaluation point to vary with the spline order.

## Exact dyadic evaluation

The executable evaluator follows
[a well-known algorithm](https://mathematica.stackexchange.com/a/137749),
which is Proposition 10 of the paper in computational form.  It precomputes
the values `F(2^-k)`, removes one highest set bit from the numerator at each
step, and evaluates the resulting Taylor polynomial in Horner form.  Thus it
uses roughly `O(n^2 + n * binaryWeight(a))` rational operations for `a / 2^n`,
rather than work proportional to the numerator itself.  The rational-input
wrapper is the preferred front door because Lean's `ℚ` representation first
reduces inputs such as `10/32` to `5/16`.

`DyadicCorrectness.lean` proves termination, clamping, table-prefix stability,
refinement invariance, and representation independence.  The inverse-power
table is connected axiom-cleanly to the executable moment recurrences in
`MomentPowerSeries.lean`; `DyadicClosedForm.lean` proves the highest-bit Taylor
identity, and `DyadicAnalytic.lean` proves equality with every bounded analytic
Fabius function.  `GlobalDyadic.lean` supplies the corresponding proofs for
the signed global extension and for equation (32) at every nonnegative dyadic
argument `m / 2^n`, with no restriction that the representation be reduced or
that `m ≤ 2^n`.

```lean
#eval Fabius.fabiusDyadicValue 4 5
-- 305857 / 2073600

#eval Fabius.evalFabiusDyadic (5 / 16 : ℚ)
-- some (305857 / 2073600)

#eval Fabius.evalFabiusDyadic (2 / 3 : ℚ)
-- none
```

Under the bounded convention, nonpositive inputs evaluate to `0` and inputs
at least `1` evaluate to `1`.  The separate global evaluator retains the
paper's oscillating continuation, for example `F(3) = -1`.

## Fourier--Legendre expansion of `up`

The ordinary Legendre polynomials are constructed from Rodrigues' formula in
`LegendrePolynomial.lean`.  The development proves their parity, degree,
Sturm--Liouville equation, endpoint values, sharp bound `|P_n(x)| ≤ 1` on
`[-1,1]`, orthogonality, and exact squared norm `2 / (2n+1)`.

`FabiusLegendreCoefficients.lean` evaluates the even Fourier--Legendre
coefficients of Rvachev's up function in terms of dyadic Fabius values.  The
result is the exact finite sum

```text
u_n = 4^(-n) (4n+1) sum (k = 0..n),
  (-1)^(n+k) * choose(2n,n+k) * choose(2n+2k,2n)
  * (2k)! * 2^choose(2k+1,2) * F(2^(-2k-1)).
```

Finally, `FabiusLegendreSeries.lean` proves
`up(x) = ∑' n, u_n P_(2n)(x)` for every `x ∈ [-1,1]`.  The convergence
is absolute and uniform on that closed interval, so the equality includes
both endpoints.  The primary public results are
`Fabius.canonical_rvachevLegendreCoefficient_eq_fabius_sum`,
`Fabius.hasSum_canonical_rvachevLegendreSeries_formula`, and
`Fabius.hasSum_canonical_rvachevLegendreSeries_formula_uniform`, with `tsum`
forms available for both.  No corresponding equality is asserted outside
the natural Legendre interval.

`FabiusLegendreLeastSquares.lean` proves the finite orthogonal-projection
property behind this expansion.  If

```text
S_N(x) = sum (n = 0..N), u_n * P_(2n)(x),
E(q) = integral (-1..1), (up(x) - q(x))^2 dx,
```

then for every real polynomial `q` of degree at most `2N+1`,

```text
E(q) = E(S_N) + integral (-1..1), (S_N(x) - q(x))^2 dx.
```

Consequently `S_N` is the unique least-squares minimizer.  This is stronger
than optimality among polynomials of its visible degree at most `2N`: the
extra degree is available because the coefficient of `P_(2N+1)` vanishes.
The primary public results are
`Fabius.rvachevLegendrePartialSum_pythagorean`,
`Fabius.rvachevLegendrePartialSum_least_squares`,
`Fabius.rvachevLegendrePartialSum_error_eq_iff`, and
`Fabius.canonical_rvachevLegendrePartialSum_mem_and_isMinOn`.

`FabiusTranslatedLegendreSeries.lean` translates this expansion to the
signed global Fabius function on `[0,2]`.  It proves

```text
P_(2n)(x-1) = sum (j = 0..2n),
  (-1)^j * 2^(-j) * choose(2n,j) * choose(j+2n,j) * x^j,
```

and substitutes this finite polynomial into the coefficient formula above.
The resulting public `HasSum` and `tsum` theorems display the complete nested
`k`- and `j`-sums, including the integer exponent
`k - j + 2*k^2 - 2*n`.  They use `globalFabius` both for the value at `x`
and for every dyadic value inside the coefficient.  This signed/global
interpretation is essential on `1 < x ≤ 2`; the bounded CDF-style function is
clamped to one there.  At `x = 0`, natural powers use the convention
`0^0 = 1`.  The primary endpoints are
`Fabius.hasSum_globalFabius_translatedLegendre_formula` and
`Fabius.globalFabius_eq_tsum_translatedLegendre_formula`.

## Sharp global regularity

The order-theoretic and metric shape of the two functions is developed in six
modules that sit directly on top of `Differential.lean` and are independent of
the paper-index files.

`Differential.lean` proves the *single* differential equation

```text
F'(x) = 2 up(2x - 1)      for every real x,
```

`Fabius.fabius_hasDerivAt`.  It specializes to the defining equation
`F'(x) = 2 F(2x)` on `[0, 1/2]`, to its reflection `F'(x) = 2 F(2 - 2x)` on
`[1/2, 1]`, and to `0` outside `[0, 1]`, so no later derivative computation
needs the case analysis.

`Monotonicity.lean` collects everything order-theoretic.  Besides the
monotonicity, positivity, and support statements that used to live inside the
arXiv:1702.06487v3 index file, it proves the strict theory: `F` is strictly
increasing on `[0,1]` (`Fabius.strictMonoOn_fabiusReal`), hence injective
there, and the intermediate value theorem promotes this to a bijection of
`[0,1]` onto itself (`Fabius.bijOn_fabiusReal`).  The support of `up` is
*exactly* the open interval, `Fabius.support_rvachevUp`, and `up` is strictly
increasing on `[-1,0]`, strictly decreasing on `[0,1]`, and equal to one only
at the origin (`Fabius.rvachevUp_eq_one_iff`).  The positivity statements are
also given in `iff` form.

`Regularity.lean` proves that both `F` and `up` are `2`-Lipschitz and that the
constant cannot be improved: `F'(1/2) = 2 up(0) = 2`, so
`Fabius.isLeast_lipschitzWith_fabiusReal` and
`Fabius.isLeast_lipschitzWith_rvachevUp` identify `2` as the least Lipschitz
constant of each.  The linear majorant `F(x) ≤ 2x` holds on all of `[0, ∞)`.

`Convexity.lean` shows that `F` is convex on `(-∞, 1/2]` and concave on
`[1/2, ∞)`, strictly so on the two halves of the unit interval, so the
midpoint is the unique inflection point.  It also gives the exact pointwise
formula

```text
F''(x) = 8 * (up(4x - 1) - up(4x - 3)),
```

and proves that `F''` is positive exactly on `(0, 1/2)`, negative exactly on
`(1/2, 1)`, and zero outside `(0,1)` and at the midpoint.  The entry points
are `Fabius.deriv_deriv_fabiusReal`,
`Fabius.deriv_deriv_fabiusReal_pos_iff`,
`Fabius.deriv_deriv_fabiusReal_neg_iff`, and
`Fabius.deriv_deriv_fabiusReal_eq_zero_iff`.

`EffectiveFlatness.lean` replaces the qualitative `o(x^n)` flatness statement
by the effective bound

```text
F(x) ≤ 2^C(n+1,2) * x^n      whenever 0 ≤ x and 2^n x ≤ 1,
```

obtained by iterating the mean value estimate `F(x) ≤ 2x F(2x)`.  Rvachev's
function inherits it at both ends of its support through `up(x) = F(1 - |x|)`.
`SharpFlatness.lean` runs the same induction through the fundamental theorem
of calculus instead of the mean value theorem, which recovers the factorial
the pointwise estimate throws away:

```text
F(x) ≤ 2^C(n+1,2) / n! * x^n .
```

At `x = 2^(-n)` the exact value is `2^(-C(n,2)) d_n / n!` with `d_n` the half
moment, so the remaining overshoot is exactly `1 / d_n`.

`GlobalBounds.lean` proves that the signed global extension is bounded by one
in absolute value, `Fabius.abs_extendedFabius_le_one` — the missing ingredient
that turns equation (3) into the sharp uniform derivative bounds

```text
|F^(k)(x)| ≤ 2^C(k+1,2)      and      |up^(n)(x)| ≤ 2^C(n+1,2),
```

both attained, at `2^(-k)` and `2^(-n) - 1` respectively, so
`Fabius.isGreatest_abs_iteratedDeriv_extendedFabius` and
`Fabius.isGreatest_abs_iteratedDeriv_rvachevUp` are exact suprema.

`BoundedDerivatives.lean` carries all of that back to the bounded, CDF-style
function.  The two functions have the same germ at every argument below one,
so equation (3) holds verbatim for `fabiusReal` there; above one the bounded
function is locally constant, and the single remaining point `x = 1` is caught
by continuity.  The consequences are flatness at the origin
(`Fabius.iteratedDeriv_fabiusReal_zero`), the global bound
`Fabius.abs_iteratedDeriv_fabiusReal_le`, and the exact attained supremum
`Fabius.isGreatest_abs_iteratedDeriv_fabiusReal`.  More sharply, on the
matched mesh `m / 2^k` with `m < 2^k`, the `k`th derivative vanishes exactly
at even numerators; at odd numerators it is the sharp amplitude
`2^C(k+1,2)` times `thueMorseSign (m / 2)`.  Hence every odd grid point is an
extremizer, not only the familiar point `2^-k`.

`MidpointEndpointTransfer.lean` identifies the entire midpoint defect with
the endpoint profile on the closed half-cell:

```text
F(1/2 + h) = 1/2 + 2h - F(h),
F(1/2 - h) = 1/2 - 2h + F(h)       for 0 ≤ h ≤ 1/2.
```

Both translated first derivatives equal `2 - F'(h)`, and every iterated
derivative of order at least two vanishes at `1/2`.  The same pointwise
identity gives the all-real oriented centered-mass formula
`∫_[1/2-a,1/2+a] F = a`, arbitrary-weight right and left defect-transfer
identities, and every Cauchy kernel `(a-h)^n/n!` for anchored repeated
primitives.  These are exact pointwise and finite-integral theorems, not an
analytic-germ assertion or a finite-spline quarter-cell statement.

`InverseMidpointDefect.lean` then converts that transmutation into an exact
implicit equation for the totalized inverse.  With

```text
h(δ) = F⁻¹(1/2 + δ) - 1/2,
E(δ) = h(δ) - δ/2,
```

one has, throughout `0 ≤ δ ≤ 1/2`,

```text
δ = 2h(δ) - F(h(δ)),
h(δ) = δ/2 + F(h(δ))/2,
E(δ) = F(h(δ))/2 = F(δ/2 + E(δ))/2,
0 ≤ h(δ) ≤ 1/2,        0 ≤ E(δ) ≤ 1/4.
```

The endpoints are exact: `h(0)=E(0)=0`, while
`h(1/2)=1/2` and `E(1/2)=1/4`, so both displayed upper bounds are attained.
The offset enclosure actually holds for every `δ ≥ 0`, and both `h` and `E`
are globally odd, including the clamped inverse tails.  The fixed point is an
exact algebraic identity; no all-orders defect bound, asymptotic equivalence,
logarithmic expansion, or Lambert-W transfer is inferred without the
additional quantitative estimates those conclusions require.

`NowhereAnalytic.lean` transfers the unnumbered non-analyticity corollary from
`up` to `F` and determines the analytic locus exactly:

```text
AnalyticAt ℝ (fabiusReal F) x  ↔  x ∉ [0, 1].
```

The signed extension is likewise analytic at no point of the first block
`[0, 2)`.

## Paper coverage

`Paper05442.lean` is the public import for the first paper.  It includes all
seven theorems, Lemma 1, the unnumbered non-analyticity corollary, and the
prose probability proposition.  In particular, it proves the original
existence-and-uniqueness characterization with the initially unknown scale.
Although positivity of that scale remains a source-faithful field of
`IsOriginalFabius`, `IsOriginalFabius.mk_of_derivative_law` derives it from
the remaining smoothness, support, positivity, normalization, and derivative
hypotheses.
Every bounded Fabius solution folds to an original compact-support solution,
and conversely every original solution has scale two and is the fold of a
unique bounded Fabius solution.  More sharply, equality of two folds is
equivalent to equality of their bounded candidates on `(-∞, 1]`; restoring
the omitted strict right tail gives an exact fixed-candidate iff.  The paper
aggregate also proves
weak-* convergence of the finite convolution measures, pointwise convergence
of the polynomial step approximants, the infinite-product probability model,
the differential identities, Poisson summation, moment formulas, and global
rationality at dyadic points.  Its Schwartz construction also exposes rapid
decay of every real-axis derivative of the entire Fourier transform through
`rvachevFourier_real_iteratedDeriv_rapidDecay`, with the transform-only form
`rvachevFourier_real_rapidDecay` as a direct corollary.

`Paper06487.lean` is the public import for the arithmetic paper.
`PaperStatements.lean` contains all 18 proved numbered results in the v3 PDF:
Propositions 1, 2, 3, 4, 6, 8, 10, 15, 18, 19, and 22; Theorems 7, 9, 13,
17, 20, and 21; and Lemma 1.  It also formalizes Question 5, Definition 12,
and Conjecture 16.  `Paper06487Supplement.lean` proves assertions made in the
surrounding prose and inside proofs.

`PaperFabiusAsymptotic.lean` is the public aggregate for the first local
draft.  It proves the exact logarithmic delay equation, the elementary log
expansions, explicit dyadic bounds, the full-real quadratic leading term, and
the coarse `O(t * log t)` error.  It also proves that the draft's proposed
sharp main term has a nonzero `(log t / t)^2` equation residual and therefore
is not `O(t^-2)`.  The draft's unsupported periodic-in-`t` argument is not
used.  Independently, a negative-Laplace product, Mellin finite-part analysis,
and quantitative Bromwich saddle proof establish a corrected sharp formula
with error `O(1 / (-log x))`.  Its centered periodic correction is reconstructed
as an absolutely summable Gamma--zeta Fourier series and proved nonconstant.
At dyadic arguments the cumulant approximation is fully effective from index
`224043` onward.  The component normalized-moment estimates, the
endpoint/Laplace comparison, and the final evaluated-constant bound are all
public Lean theorems, headed by
`abs_log_fabius_dyadic_sub_explicitCumulantMain_le`.
More strongly, if `lambda = fabiusLambertPhase x`, then for every `N`

```text
log F(x) = fabiusSharpLambertMain x
  + sum (j < N), lambda^(-j) * fabiusSaddleLogCoefficient j lambda
  + O(lambda^(-N)).
```

The zeroth coefficient is zero, and the first explicit correction is
`fabiusFirstSaddleCorrection lambda / lambda`.  A separate theorem expands
`lambda` itself to arbitrary order in `-log x` and `log (-log x)`.  The full
formula keeps the oscillatory coefficient functions at the exact Lambert
phase; it does not silently replace them by a lower-order phase approximation.

The asymptotic aggregate also audits four linked Stack Exchange discussions.
The recurrence sequence is exposed directly as
`fabiusRecurrenceSequence n = halfMoment n / n!`, with its displayed
recurrence, Bernoulli recurrence, inverse-dyadic bridge, generating series,
and product all proved.  Substituting the inverse-dyadic bridge back into the
sequence recurrence gives the direct formula

```text
F(2^(-n)) = 2^(-choose(n,2)) / (2^n - 1) *
  sum (k < n), 2^(choose(k,2)) / (n-k+1)! * F(2^(-k))
```

for every `n ≥ 1`; exact rational, generic bounded, generic signed-global,
and canonical signed-global forms are exposed by
`fabiusAtInverseTwoPow_recurrence_zpow`,
`fabiusFunction_inverse_two_pow_recurrence_zpow`,
`extendedFabius_inverse_two_pow_recurrence`, and
`globalFabius_inverse_two_pow_recurrence`, respectively.  The restriction is
necessary: at `n = 0` the displayed denominator vanishes.

`FabiusInverseDyadicClosedForm.lean` solves this recurrence completely.  If
`(r₁,…,rₘ)` ranges over the ordered compositions of `n` and
`sⱼ = r₁+⋯+rⱼ`, then

```text
F(2^(-n)) = 2^(-choose(n,2)) *
  sum (r₁,…,rₘ) ⊧ n,
    product (j = 1,…,m), 1 / ((2^sⱼ - 1) * (rⱼ + 1)!).
```

For `n = 0`, the unique empty composition and empty product give the initial
value `F(1)=1`, so unlike the recurrence this formula holds for every natural
`n`.  The proof is a finite weighted-path expansion with a formal last-edge
decomposition.  Public endpoints include
`Fabius.fabiusAtInverseTwoPow_eq_composition_formula`, the explicitly nested
`Fabius.fabiusAtInverseTwoPow_eq_composition_formula_by_length`, and generic,
canonical, and signed-global real corollaries.  The self-contained derivation
is integrated into the primary exposition, available as
[LaTeX source](docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex)
and as a
[rendered PDF](docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.pdf).
The consolidated frontier volume retains longer alternative derivations and
their provenance without weakening this exact, primary-document integration.

The
[conjectured finite q-binomial formula](https://math.stackexchange.com/questions/3283519/conjectured-formula-for-the-fabius-function)
is proved exactly in its full stated scope: for all natural `m,n`, its
half-shifted Thue--Morse sum is the signed global Fabius value at `m / 2^n`.
No condition `m ≤ 2^n` or irreducibility of the dyadic representation is
needed.  When `m ≤ 2^n`, the same formula is a corollary for every bounded
function satisfying `IsFabius`.  The rational expression is independent of
the representation of `m / 2^n` (in particular, it is unchanged by
`(m,n) ↦ (2m,n+1)`) and is invariant under any common translation of its
inner powers.  The finite translated expressions are constant polynomials
over `ℚ`, so they can be evaluated in every field over `ℚ`.  In particular,
for every real or complex `q` the fully displayed sum with inner power
`(j - m * 2^k + q)^(n+k)` has that same value; generic, real, complex, and
Gaussian-rational endpoints are public.  Thus the source's `+1/2` formula and
the centered form agree, while its `QPochhammer`/`QBinomial` factors retain
notation-faithful definitions at the fixed q-special-function base `1/2`.
For the inverse-power specialization, dyadic reflection additionally proves
for every real or complex `q` the raw-coordinate formula with inner power
`(r+q)^(n+k)` and denominator `(-2)^(n^2)`.  Its fully literal theorem uses
the zero-one `thueMorseBit`; at `n = q = 0`, the sole inner power is `0^0`
and evaluates to one.  The centered and raw scalar APIs are
`Fabius.qBinomialThueMorseTranslatedFormulaIn` and
`Fabius.qBinomialThueMorseRawTranslatedFormulaIn`; the arbitrary-numerator
version is `Fabius.qBinomialThueMorseDyadicTranslatedFormulaIn`.

The global binary-reduction series is also formalized.  Its correct outer
index starts at `m = 0`, where `Floor[2^(m-1)x]` is genuinely `Floor[x/2]`.
For every real `x ≥ 0`, the series converges absolutely to the signed global
Fabius extension.  This specializes to the bounded Fabius function on
`0 ≤ x ≤ 1`.  More strongly, for `N ≥ 1` the finite telescope through scale `N` has
all-real error at most `2 * 2^-N`: it is the uniformly bounded residual for
`x ≥ 0`, while both the partial sum and signed extension vanish for `x ≤ 0`.
Thus `Fabius.globalBinaryReductionSum_tendstoUniformly_extendedFabius`
proves uniform convergence on `ℝ`.  The complete finite inner expression is
a constant polynomial in its common translation, so the theorem holds not
only for rational `q`, but for every real or complex `q`.  The missing
`m = 0` term is zero on
`0 ≤ x < 1` and equals one at `x = 1`; this explains both why the former
one-indexed formula worked on the half-open interval and why it failed at the
right endpoint.  The primary public endpoints are
`Fabius.hasSum_qBinomialFabiusGlobalSummand`,
`Fabius.globalFabius_eq_tsum_qBinomialFabiusGlobalSummand_real`, and
`Fabius.globalFabius_eq_tsum_qBinomialFabiusGlobalSummand_complex`.

The parity-power form of the binary-reduction series is proved as well, with
one necessary correction: the all-`x` sum begins at `m = 0`.  For every real
`x ≥ 0`, `Fabius.globalFabius_eq_tsum_fabiusParityPower_literal` is the fully
expanded source-style identity and targets the signed global extension.  Its
exponent is interpreted in `ℤ`, so the `n = 0` exponent is genuinely `-1`:
`Fabius.fabiusParityPowerExponent_eq_choose_sub_one` records the exact
normalization.  On `[0,1]`,
`Fabius.fabiusReal_eq_tsum_fabiusParityPowerSummand` gives the bounded Fabius
function.  The original sum starting at `m = 1` is retained, with its correct
domain `0 ≤ x < 1`, as
`Fabius.globalFabius_eq_tsum_fabiusParityPowerSummand_succ`.

The generalized Wolfram `DiscreteLimit` formula is proved as well.  For every
real `x ≥ 0` and every `q : ℂ`, its finite q-binomial/Thue--Morse
approximants converge to the signed global Fabius value; on `[0,1]` the limit
is the ordinary bounded Fabius function.  Separate public specializations
cover rational shifts, Gaussian-rational shifts, and arbitrary real shifts,
including irrational ones.  Lean encodes the inner sum safely with length
`⌊2^(n+k) x + 1/2⌋₊`; `Fabius.fabiusDiscreteLimitRangeLength_eq_floor_add_one`
proves that this is exactly the successor of the inclusive Wolfram upper
bound `Floor[2^(n+k) x - 1/2]`, including its empty case.  A finite row can
genuinely depend on `q` at a nondyadic `x`; it is the limit that is independent
of every fixed complex `q`.  The proof reindexes each row as a uniformly
bounded Toeplitz average of centered finite Thue--Morse splines, proves their
global convergence through finite uniform-distribution CDFs, and controls a
complex shift by a decaying Taylor bound.  Finally, exact telescope and
`tsum` theorems identify the same limit with the binary-reduction series; they
do not assert a termwise equality between the two finite approximations.  The
primary endpoints are
`Fabius.fabiusDiscreteLimit_literal_complex_tendsto_globalFabius`,
`Fabius.fabiusDiscreteLimitApproximationComplex_tendsto_fabiusReal`, and
`Fabius.fabiusDiscreteLimitApproximationComplex_tendsto_literal_tsum`.
The exact finite-remainder telescope is exposed both generically as
`Fabius.extendedFabius_eq_qBinomial_telescope_add_remainder` and with every
nested sum displayed as
`Fabius.globalFabius_eq_qBinomialThueMorse_telescope_add_remainder_complex`.

The recurrence sequence's fixed-constant heuristic
omits the nonconstant periodic correction.  The elementary small-`x`
expression from
[Math Stack Exchange](https://math.stackexchange.com/a/3925650/19661) is
formalized verbatim and corrected by adding that term at the exact
lower-Lambert phase.  The uncorrected claimed error is formally disproved.
Exponentiating the corrected formula gives a proved asymptotic equivalent for
the Fabius function itself.
Finally, the proposed
[quotient-of-exponentials fit](https://mathematica.stackexchange.com/questions/285919/approximation-of-the-fabius-function-with-a-quotient-of-exponentials)
is little-o of the true displaced Fabius bump at the endpoint, so it cannot be
an asymptotic equivalent despite its good compact-interval plot.

`PaperKFoldThueMorse.lean` is the public aggregate for the second local
draft.  It contains the exact prefix-sum, zero-run, convolution, and
generating-series identities; the intended real polygonal interpolation; and a
proved corrected pointwise approximation scheme.  It also exposes the
zero-one sequence `thueMorseBit` and proves the exact identity expressing it
through `Log2` of the signed binomial-parity sum.  The Stirling estimate used
by the draft is proved in its precise `O(log n)` form.  The aggregate also
exposes formal counterexamples to the literal normalization, the claimed local
and global error estimates, the unbounded “maximum” proxy, and the omitted
linear term in the subsequent Stirling calculation.  Both qualitative decay
comparisons are proved: the Fabius function is smaller than every power at
zero, while `exp (-c/x)` is little-o of it for every `c > 0`.  No Lambert-W
theorem is used to justify the false proxy chain; instead, the repaired lower
branch, its equation-(9) solution, and its standard two-term expansion are
proved separately.

The exact source-to-Lean map is in
[`docs/PAPER_COVERAGE.md`](docs/PAPER_COVERAGE.md).
The requirement-by-requirement asymptotic evidence is recorded in
[`docs/ASYMPTOTIC_COMPLETION_AUDIT.md`](docs/ASYMPTOTIC_COMPLETION_AUDIT.md).

The two arXiv sources contain a few statements that are not literally correct.  The
formalization records the mathematically valid versions next to their proofs.
Among them:

1. In the first paper, equation (12) must be a finite convolution; the printed
   infinite upper index is incompatible with its dependence on `m`.
2. The closed interval indicators in Theorem 2 double-count shared endpoints.
   `halfEndpointIntervalIndicator` gives endpoints weight `1/2`, preserving
   the asserted normalization `φ_n(0) = 1` and the pointwise limit.
3. Equation (25) omits `t` from its exponential, equation (26) needs `n > 0`,
   and equation (32) has inconsistent scaling.  The Poisson-summation module
   proves the corrected identities.  Its
   `rvachev_poisson_support_specialization_unscaled_of_one_half_le` and
   `rvachev_poisson_support_specialization_of_one_half_le` declarations also
   show that the paper's upper bound `a ≤ 1` is unnecessary: both formulas
   hold on the sharp support-controlled ray `a ≥ 1/2`.
4. In the arithmetic paper, Lemma 1 is false for a negative scale and an
   arbitrary derivative order.  Its proof requires
   `0 ≤ scale + order`; the Lean statement includes that hypothesis.
5. Proposition 2's quotient `(exp x - 1) / x` has a removable singularity;
   `expm1Div 0` is defined to be `1`.
6. The exponent in `R_n` is positive in equation (27), its proof, and its
   displayed values.  The development uses that consistent positive exponent.

## Documentation policy

Every mathematical document in this directory is a LaTeX document, and its
compiled PDF is committed alongside its source.

- **Format.** Mathematics is written in `*.tex`, never in Markdown. Markdown is
  reserved for repository bookkeeping that contains no displayed mathematics:
  this README, [`AGENTS.md`](AGENTS.md),
  [`docs/PAPER_COVERAGE.md`](docs/PAPER_COVERAGE.md), and the coordination
  files in `AGENTS/`.
- **Style.** New documents reuse the preamble of
  [`Fabius_Function_and_Rvachev_Up.tex`](docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex)
  verbatim — the same geometry, fonts, colours, `hyperref` setup, running
  heads, section formatting, theorem environments, macros, and listing style.
  Only the title block and the PDF metadata change.
- **Layout.** One directory per document, named after it, containing the `.tex`
  and the `.pdf` of the same name.
- **The PDF is committed** in the same commit as the `.tex`, built with three
  `pdflatex` passes so that the cross-references and the table of contents
  settle; the `.aux`, `.log`, `.out` and `.toc` files are not committed. A
  `.tex` change without a rebuilt `.pdf` is an incomplete commit.
- **Prose is Libertinus.** The preamble falls back to Latin Modern silently
  when the font package is missing, so builders verify the committed PDF with
  `pdffonts`, install Libertinus first when it is absent, and — only when
  installation fails — commit a fallback build together with a `README.md`
  beside the PDF requesting a rebuild on a Libertinus-equipped machine. Math
  stays Computer Modern by decision. `AGENTS.md` states the full rule.
- **Check the rendered PDF.** Never write LaTeX through a shell heredoc or a
  script that round-trips through `unicode_escape`: both silently destroy
  backslashes, and LaTeX will not complain — it renders something plausible and
  wrong.
- **Keep the primary exposition formalization-backed.** Every mathematical
  assertion in
  [`Fabius_Function_and_Rvachev_Up.tex`](docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex)
  must match one or more actual proved Lean declarations. This rule covers not
  only theorem environments, but also displayed formulas, prose deductions,
  exact numerical values, inequalities, asymptotics, convergence statements,
  and claims about algorithms. The exposition records exact declaration names
  and modules so the correspondence can be audited; similarity to a theorem or
  an informal consequence is not sufficient.
- **Put unformalized work on the research frontier.** Any mathematical material
  without an exact proved Lean counterpart — however obvious, standard, or
  plausible — belongs in a LaTeX/PDF document under
  [`docs/non-formalized-research-frontiers/`](docs/non-formalized-research-frontiers/),
  not in the primary exposition. Frontier documents label conjectures,
  heuristics, partial formalizations, refutations, and the precise outstanding
  Lean obligations rather than presenting them as established results.
- **Treat drafts as a temporary inbox.** Content under
  `docs/Fabius_Function_and_Rvachev_Up/drafts/` is reviewed claim-by-claim.
  Lean-backed material is integrated organically into the primary exposition
  without duplication; everything else is relocated to the research-frontier
  tree with its provenance. Once a draft is fully dispositioned, it is removed,
  and an empty `drafts/` directory is deleted rather than retained as an
  archive.

[`AGENTS.md`](AGENTS.md) states the same policy with the exact build commands.

## Contributing and coordination

The operational entry point is [`AGENTS.md`](AGENTS.md): its documentation
policy, Lean build guidance, and invariants apply to all work in this
directory.  Multi-agent coordination is switched by the single file
[`AGENTS/STATUS.md`](AGENTS/STATUS.md) (currently OFF)
and specified by
[`AGENTS/PROTOCOL.md`](AGENTS/PROTOCOL.md): claim-free
optimistic Lean work with first-landed-wins integration, one standing owner
per canonical document with a fast path for small fixes, a lock-file build
mutex, a 2-hour integration-latency cap, bookkeeping on a dedicated orphan
branch off `main`, and a built-in overhead assessment with explicit authority
to delete rules that stop paying for themselves.  The heavier v1 protocol of
the 2026-08 campaign and its rationale survive only in git history (the
deleted `docs/COLLABORATION.md` and
`docs/MULTI_AGENT_COORDINATION_PROPOSAL.md`).

## Checking

From the repository root:

```sh
lake build +FabiusFunction
```
