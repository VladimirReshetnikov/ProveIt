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
> share 13 GB, so that fan-out starves all of them. Bound Lake's worker pool
> on every build:
>
> ```bash
> LAKE_JOBS=1 lake build <one target>
> ```
>
> `LAKE_JOBS` bounds the number of `lean.exe` processes.  Do not set
> `LEAN_NUM_THREADS=0`: it serializes elaboration inside the single worker
> and was measured to make focused builds about thirty times slower. Lake
> `5.0.0` accepts neither `-j` nor `--jobs`, so the environment variable is
> the process-control mechanism. Measured 2026-08-27:
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
[research-frontier LaTeX volume](docs/semi-formalized-research-frontiers/semi-formalized-research-frontiers.tex)
([PDF](docs/semi-formalized-research-frontiers/semi-formalized-research-frontiers.pdf)).
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
identities, normalized integer-order and positive-real fractional Volterra
calculus, exact integer primitive ladders and first fractional Fabius--Rvachev
shifts, unconditionally summable analytic finite-series filters, Taylor
reduction, the Fourier and entire-series identities,
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
At formal source checkpoint `71ab6f6728fceb753c88d8b0573077a59acf2682`,
summable-scale products additionally give the entire geometric
reciprocal-Gamma family, its Mahler/zero/reflection laws, the exact dyadic
Rvachev bridge, and the dyadic zero and meromorphic pole orders.
The post-checkpoint jet/tower tranche at `0ba35abd4` adds all five public
declarations of `ReciprocalGammaJets.lean` and the first eight public
declarations of `ThueMorseGammaTower.lean`; the current integrated tree adds that
module's ninth declaration, the master-product/tower-ratio bridge.  Thus the
entire reciprocal Gamma function now has exact first jets, simple analytic
orders, and punctured local coefficients at every nonpositive integer, and the
Thue--Morse continuation has exact first jets, Mellin/integral GammaLog levels,
and dyadic log/tower laws at every natural level.  The GammaLog is a chosen
coordinate, not a proved `Complex.log` identity.  Its and the tower's definitions
are total in the real parameter `a`, while their analytic identification laws
assume `0 < a`; no derivative value is assigned to raw Gamma at a pole.  Only
the parameter-`a` differential and iterated ladder remains open within this
tower tranche.

## Using the Lean library

From the repository root, the complete public surface is checked with

```sh
LAKE_JOBS=1 lake build +FabiusFunction
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
| Generic affine-difference iterates and derivative orbits | `FabiusFunction.AffineDifferenceOrbit` | `affineDifference_iterate_apply`, `iteratedDeriv_eq_affineDifference_iterate_on`, `affineDifference_iterate_two_one_apply`; the module assumes a one-step derivative identity and does not prove the up-law resolvent equation |
| Central-binomial valuation and the Thue--Morse sign | `FabiusFunction.CentralBinomialValuation` | Exhaustive public surface: `padicValNat_two_centralBinom`, `thueMorseSign_eq_neg_one_pow_centralBinom`, `padicValNat_two_centralBinom_eq_zero_iff`; for every natural `n`, the valuation is `binaryWeight n`, the sign is its `(-1)`-power, and valuation zero is equivalent to binary weight zero (hence occurs only at `n = 0`, not at positive powers of two) |
| Binary digits as differences of dyadic floors | `FabiusFunction.BinaryDigitFloor` | Exhaustive public surface: `div_two_pow_succ_eq_div_div`, `sub_two_mul_div_two`, `div_two_pow_sub_two_mul_div_two_pow_succ`, `testBit_toNat_eq_div_sub_two_mul_div`; the identities are total in their natural-number inputs and give the atlas's exact floor-difference digit formula, without an analytic or real-floor generalization |
| Total complex finite Thue--Morse sinc and negative-Laplace bridges | `FabiusFunction.ThueMorseComplexProductBridge` | `shiftedComplexSincPrefix`, `complexLaplacePrefix`, `sum_thueMorseSign_cexp_eq_sin_prod`, `thueMorseBlock_cexp_eq_sincPrefix`, `thueMorseBlock_cexp_eq_sincPrefix_of_pos`, `thueMorseBlock_exp_neg_eq_laplacePrefix`, `shiftedComplexSincPrefix_eq_thueMorseBlock_cexp_of_pos`, `complexLaplacePrefix_eq_thueMorseBlock_exp_neg`, `complexExpm1Div_neg_eq_exp_mul_complexSinc`, `complexLaplacePrefix_eq_exp_mul_shiftedComplexSincPrefix`, `shiftedComplexSincPrefix_apply_zero`, `complexLaplacePrefix_apply_zero`; the primary equalities and the finite Fourier--Laplace rotation hold at every level and at the removable origin, while the quotient forms assume a nonzero free variable |
| Finite uniform-digit characteristic functions as Thue--Morse blocks | `FabiusFunction.UniformDigitThueMorseBridge` | `charFun_uniformDigitPrefix_eq_shiftedComplexSincPrefix`, `thueMorseBlock_cexp_eq_charFun_uniformDigitPrefix`, `charFun_uniformDigitPrefix_eq_thueMorseBlock_cexp`; the first two identities hold at every natural level and real frequency, including the empty prefix and frequency zero, while solving for the characteristic function assumes the real frequency is nonzero; these are finite-prefix identities and assert no infinite-product or random-tail limit |
| Exact first jets and simple zeros of reciprocal Gamma | `FabiusFunction.ReciprocalGammaJets` | `deriv_Gamma_inv_neg_nat`, `hasDerivAt_Gamma_inv_neg_nat`, `hasDerivAt_Gamma_inv_zero`, `analyticOrderAt_Gamma_inv_neg_nat`, `tendsto_Gamma_inv_div_add_nat`; all five statements hold for every natural zero index, concern the entire reciprocal function, and assign no derivative to raw Gamma at a pole |
| Thue--Morse continuation jets and Gamma tower | `FabiusFunction.ThueMorseGammaTower` | `hasDerivAt_dirichletMellinContinuation_neg_nat`, `deriv_dirichletMellinContinuation_neg_nat`, `thueMorseGammaLog`, `thueMorseGammaTower`, `thueMorseGammaLog_eq_mellin`, `thueMorseGammaLog_eq_integral`, `thueMorseGammaLog_dyadic`, `thueMorseGammaTower_dyadic`, `ofReal_exp_mpLimit_eq_gammaTower_div`; the two definitions are total in `a`, all analytic laws assume `0 < a` (and the ratio bridge also `0 < b`), GammaLog is a chosen coordinate rather than a proved `Complex.log` identity, and only the parameter differential/iterated ladder remains open |
| Generic normalized Volterra calculus over real normed spaces (Banach only for the FTC/Taylor layer) | `FabiusFunction.NormalizedVolterra` | `volterraPrimitive`, `iteratedPrimitive`, `normalizedVolterra`, `normalizedVolterra_affine`, `normalizedVolterra_comp_affine`, `normalizedVolterra_basepoint_shift`, `normalizedVolterra_succ_eq_taylor_of_eq_zero`, `iteratedPrimitive_add`, `iteratedPrimitive_succ_hasStrictDerivAt`, `iteratedPrimitive_eq_normalizedVolterra`, `normalizedVolterra_succ_hasStrictDerivAt`, `iteratedDeriv_normalizedVolterra_add`, `contDiff_normalizedVolterra`, `normalizedVolterra_add`, `normalizedVolterra_succ_iteratedDeriv_eq_sub_taylor`, `intervalIntegrable_normalizedVolterraKernel_add`, `normalizedVolterra_succ_polynomial_of_taylor_support_kernel_intervalIntegrable`, `normalizedVolterra_succ_polynomial_of_kernel_intervalIntegrable`, `normalizedVolterra_polynomial`, `normalizedVolterra_monomial` |
| Positive-real fractional Volterra calculus over real normed spaces | `FabiusFunction.FractionalVolterra`, `FabiusFunction.FractionalVolterraSemigroup` | `fractionalVolterra`, `fractionalVolterra_self`, `fractionalVolterra_congr`, `fractionalVolterra_smul`, `intervalIntegrable_fractionalVolterra_kernel`, `intervalIntegral_eq_integral_min_of_eq_zero`, `fractionalVolterra_eq_intervalIntegral_min_of_eq_zero`, `fractionalVolterra_add_input`, `fractionalVolterra_one`, `fractionalVolterra_nat_succ`, `intervalIntegral_fractionalVolterra_betaKernel`, `intervalIntegrable_fractionalVolterra_betaKernel`, `intervalIntegral_fractionalVolterra_normalizedBetaKernel`, `fractionalVolterra_normalized_rpow_smul`, `fractionalVolterra_rpow_smul`, `fractionalVolterra_const`, `fractionalVolterra_add`; the definition and algebraic endpoint/integer rules use oriented interval integrals, while kernel integrability and input additivity assume `0 < α`, `a ≤ x`, and continuity on `[a,x]`; if `a ≤ b`, `a ≤ x`, and an interval-integrable kernel vanishes on `Ioo b x`, its integral cuts off at `min x b`, and for `0 < α` the same support truncation holds for a continuous fractional input vanishing on that open tail; for `0 < α`, `0 < β`, the raw shifted beta kernel is interval-integrable when `s ≤ x`, and its raw and Gamma-normalized values are evaluated when `s < x`; on a complete target, normalized shifted powers (`α, β > 0`, `a < x`), general shifted powers (`α > 0`, `ρ > -1`, `a < x`), and constants (`α > 0`, `a ≤ x`) have their exact Gamma-quotient values, and `fractionalVolterra_add` proves additive composition of two positive orders when `a ≤ x` and the input is continuous on `[a,x]`; no order-zero law, reversed-endpoint fractional interpretation, semigroup theorem for merely interval-integrable inputs or noncomplete targets, fractional derivative or Caputo theorem, or complex order is claimed |
| Increasing-affine covariance, ordinary-derivative order raising, causal Rvachev fractional primitives, and one-step Fabius--Rvachev shifts | `FabiusFunction.FractionalVolterraCalculus`, `FabiusFunction.FabiusFractionalVolterra` | `fractionalVolterra_affine`, `fractionalVolterra_comp_affine`, `fractionalVolterra_add_one_deriv`, `fractionalVolterra_add_one_deriv_of_eq_zero`, `rvachevFractionalPrimitive`, `rvachevFractionalPrimitive_eq_intervalIntegral_min`, `rvachevFractionalPrimitive_nat_succ`, `rvachevFractionalPrimitive_add`, `fractionalVolterra_add_one_extendedFabius_of_nonneg`, `fractionalVolterra_add_one_fabiusReal`, `fractionalVolterra_add_one_rvachevUp`; affine covariance holds for every real order, positive scale, and ordered endpoints without regularity, integrability, or completeness assumptions; on a complete target, order raising assumes `0 < α`, `a ≤ x`, continuity of the primitive on `[a,x]`, an interval-integrable displayed derivative, and its right derivative on the open interval, records the exact Gamma-normalized left-boundary term, and includes the degenerate interval; `rvachevFractionalPrimitive` is total, its classical support-truncated formula assumes `0 < β` and `-1 ≤ x`, its positive-natural-order bridge is total in the endpoint, and its additive semigroup assumes `α, β > 0` and `-1 ≤ x`; the three shift specializations give `I₀^(α+1) 𝓕(x) = 2^α I₀^α 𝓕(x/2)` for `α > 0`, `x ≥ 0`, its bounded form for `x ∈ [0,1]`, and `I₋₁^(α+1) up(x) = 2^α I₀^α F((x+1)/2)` for `x ≥ -1`; no nonpositive-scale or reversed-endpoint covariance, negative- or complex-order fractional-calculus extension, fractional derivative or Caputo theorem, shifted dyadic-lattice or endpoint-moment wrapper, transform/tail-series theorem, or inverse-function specialization is claimed |
| Exact signed-global and bounded Fabius primitive ladders with finite polynomial weights | `FabiusFunction.FabiusAntiderivatives` | `normalizedVolterra_extendedFabius`, `normalizedVolterra_fabiusReal_of_le_one`, `normalizedVolterra_polynomial_mul_extendedFabius`, `normalizedVolterra_pow_mul_extendedFabius`, `normalizedVolterra_polynomial_mul_fabiusReal_of_le_one`, `normalizedVolterra_pow_mul_fabiusReal_of_le_one`, `integral_cube_mul_fabiusReal_eq`; signed formulas are global, while bounded formulas assume `x ≤ 1` |
| Absolutely summable uniform-coordinate series and their canonical pushforward laws | `FabiusFunction.WeightedUniformSeries` | `weightedUniformSeries`, `weightedUniformSeries_smul_weights`, `weightedUniformSeries_split`, `weightedUniformDistribution`, `isProbabilityMeasure_weightedUniformDistribution`, `weightedUniformDistribution_split`, `weightedUniformDistribution_reflection`, `ae_weightedUniformDistribution_mem_Icc`, `weightedUniformDistribution_restrict_Icc`, `weightedUniformDistribution_Icc` |
| Compatibility names, scalar/unit-mass refinements, and absolute continuity for weighted real laws | `FabiusFunction.WeightedUniformDistribution` | `uniformProduct_map_head_tail_function`, `weightedUniformDistribution_isProbabilityMeasure`, `weightedUniformDistribution_smul_weights`, `uniformProduct_map_head_tail_weightedUniformSeries`, `weightedUniformDistribution_unitInterval`, `weightedUniformDistribution_compl_unitInterval`, `uniformScaledAdd_absolutelyContinuous`, `weightedUniformDistribution_absolutelyContinuous_of_head_ne_zero`, `weightedUniformDistribution_absolutelyContinuous`, `weightedUniformDistribution_nullSingletonClass` |
| Banach-valued L1 survival-kernel calculus for finite measures, clipped endpoints, and scalar probability integration by parts | `FabiusFunction.ProbabilityLaplaceMoments` | `integral_Icc_intervalIntegral_eq_intervalIntegral_smul_survival`, `integral_Icc_intervalIntegral_min_eq_intervalIntegral_smul_survival`, `integral_Icc_intervalIntegral_eq_intervalIntegral_smul_rvachevUp`, `integral_Icc_intervalIntegral_min_eq_intervalIntegral_smul_rvachevUp`, `intervalIntegral_mul_rvachevUp_eq_integral_Icc_intervalIntegral`, `intervalIntegral_mul_rvachevUp_eq_integral_Icc_intervalIntegral_min`, `integral_Icc_eq_left_add_intervalIntegral_deriv_mul_survival`, `integral_unit_eq_zero_add_integral_deriv_mul_rvachevUp` |
| Exact midpoint--endpoint value and first-jet transfer, complete higher midpoint jet, centered integral, and weighted primitive kernels | `FabiusFunction.MidpointEndpointTransfer` | `fabiusReal_midpoint_add_eq`, `fabiusReal_midpoint_sub_eq`, `deriv_fabiusReal_midpoint_add_eq`, `deriv_fabiusReal_midpoint_sub_eq`, `iteratedDeriv_fabiusReal_half_eq_zero_of_two_le`, `intervalIntegral_fabiusReal_centered`, `intervalIntegral_mul_fabiusReal_midpoint_add_defect_eq_neg`, `intervalIntegral_mul_fabiusReal_midpoint_sub_defect_eq`, `intervalIntegral_fabiusReal_midpoint_add_defect_eq_neg`, `intervalIntegral_repeatedPrimitiveKernel_fabiusReal_midpoint_add_defect_eq_neg` |
| Exact inverse-midpoint offset and defect fixed points, endpoint normalizations, positive-cell enclosures, and global oddness | `FabiusFunction.InverseMidpointDefect` | `fabiusInvMidpointOffset`, `fabiusInvMidpointDefect`, `fabiusInvMidpointOffset_zero`, `fabiusInvMidpointDefect_zero`, `fabiusInvMidpointOffset_half`, `fabiusInvMidpointDefect_half`, `fabiusInvMidpointOffset_mem_Icc`, `fabiusInvMidpointOffset_equation`, `fabiusInvMidpointOffset_fixedPoint`, `fabiusInvMidpointDefect_eq_half_fabiusReal`, `fabiusInvMidpointDefect_fixedPoint`, `fabiusInvMidpointDefect_mem_Icc`, `fabiusInvMidpointOffset_neg`, `fabiusInvMidpointDefect_neg` |
| Exact finite-spline cell around `1/4`, with two-sided reflection, curvature, and conditional inverse identities | `FabiusFunction.QuarterSplineLocalPolynomial`, `FabiusFunction.QuarterSplineTwoSided` | `reportFiniteFabiusApproximant_quarter_twoSided`, `reportFiniteFabiusApproximant_quarter_reflection`, `reportFiniteFabiusApproximant_quarter_centralSecondDifference`, `strictMonoOn_reportFiniteFabiusApproximant_quarter_twoSided`, `reportFiniteFabiusApproximant_quarterPrefix_value`, `reportFiniteFabiusApproximant_quarterPrefix_quantile` |
| Full-order centered Rvachev moment, logarithmic-coefficient, and cumulant parity, with Bernoulli--Mersenne formulas at every positive even order | `FabiusFunction.CenteredMomentParity`, `FabiusFunction.SinhDivBernoulliLog` | `centeredRvachevFullMoment_even`, `centeredRvachevFullMoment_odd`, `centeredRvachevFullLogCoefficient_even`, `centeredRvachevFullLogCoefficient_odd`, `centeredRvachevFullCumulant_even`, `centeredRvachevFullCumulant_odd`, `centeredRvachevEvenCumulant_eq_bernoulliMersenne` |
| Exact topological support of weighted-uniform laws | `FabiusFunction.WeightedUniformSupport` | `isOpenPosMeasure_infinitePi`, `uniformProduct_isOpenPosMeasure`, `support_map_eq_closure_range_of_continuous`, `weightedUniformSeries_constCoordinates`, `weightedUniformDistribution_support_eq_range`, `range_weightedUniformSeries_eq_Icc_min_max`, `weightedUniformDistribution_support_eq_Icc_min_max`, `range_weightedUniformSeries_eq_Icc`, `weightedUniformDistribution_support_eq_Icc`, `weightedUniformDistribution_support_eq_unitInterval` |
| Continuous CDF calculus for atomless real probability laws | `FabiusFunction.ContinuousCDF` | `continuous_cdf_of_nullSingleton`, `cdf_reflection_sub`, `measure_eq_withDensity_of_cdf_hasDerivAt`; the last theorem turns an everywhere pointwise CDF derivative into the exact Lebesgue `withDensity` representation without assuming derivative continuity or prior absolute continuity, because CDF monotonicity supplies nonnegativity and local integrability |
| Contractive affine independent-copy probability laws | `FabiusFunction.AffineIndependentCopy` | At compiled checkpoint `d312c0603`: `affineIndependentCopyLaw`, `affineIndependentCopyLaw_isProbabilityMeasure`, `affineIndependentCopyLaw_eq_map_prod`, `charFun_affineIndependentCopyLaw`, `charFun_eq_mul_charFun_of_affineIndependentCopy_fixedPoint`, `charFun_iterate_of_affineIndependentCopy_fixedPoint`, `eq_of_charFun_affine_recurrence`, `affineIndependentCopyLaw_fixedPoint_unique`, `affineIndependentCopy_map_fixedPoint_unique`; the digit space is an arbitrary measurable space and the target is a second-countable Borel real inner-product space; a measurable digit map and probability digit/candidate laws suffice for the operator-level fixed-point API, while completeness is assumed only by the characteristic-recurrence and two fixed-point uniqueness theorems; uniqueness requires `|q| < 1`, includes `q = 0` and negative `q`, and uses no support, density, or moment hypothesis |
| Geometrically weighted uniform laws and their characterization | `FabiusFunction.GeometricUniformLaw`, `FabiusFunction.GeometricUniformUniqueness` | `geometricUniformWeight`, `hasSum_geometricUniformWeight`, `geometricUniformSeries`, `geometricUniformSeries_split`, `geometricUniformDistribution_selfSimilar`, `geometricUniformDistribution_absolutelyContinuous`, `geometricUniformDistribution_nullSingletonClass`, `geometricUniformDistribution_reflection`, `geometricUniformDistribution_Icc`, `eq_geometricUniformDistribution_of_selfSimilar`; the last theorem characterizes the law among all probability measures satisfying the affine product-map equation whenever `|q| < 1`, including `q = 0` and negative `q`, without support, density, or moment assumptions |
| Geometric tail dictionary and sinc-prefix factorization | `FabiusFunction.GeometricUniformDictionary`, `FabiusFunction.GeometricSincFactorization` | `charFun_geometricUniformDigit`, `charFun_geometricUniformDistribution_prefix`, `charFun_geometricUniformDistribution_prefix_sinc`, `tendsto_prefix_sinc_charFun`, `charFun_weightedSumDistribution_prefix_sinc`, `tendsto_prefix_sinc_charFun_weightedSumDistribution`; the digit formula is unconditional, while for every real `q` with `|q| < 1`, depth `m`, and frequency `t`, the law has the exact residual factorization `φ_q(t) = exp(i(1-q^m)t/2) · ∏_{k<m} sinc((1-q)q^k t/2) · φ_q(q^m t)`, and the phase-bearing prefix without the residual converges pointwise to `φ_q(t)`; this includes `q = 0` and negative `q`, and the final two declarations are the `q = 1/2` weighted-sum wrappers.  `geometric_tail_dictionary_geometricUniform` already supplies finite characteristic-function, MGF, and CGF tail factorizations, while `geometricSincProduct` already packages the rescaled sinc factors as a `tprod`.  A named characteristic-function-to-`geometricSincProduct` bridge (or explicit `HasProd` theorem), compact-uniform prefix convergence, rapid-decay bounds and Fourier inversion, explicit Bernoulli-cumulant/Bell-moment formulas and asymptotics, further transform formulas, centered packaging, and shape theory remain frontier targets.  The separate fixed-dyadic Pochhammer factorization below does not supply any of these general-`q` characteristic-function or uniformity statements |
| CDF and explicit density of the geometric uniform law | `FabiusFunction.GeometricUniformCDF` | `geometricUniformCDF`, `monotone_geometricUniformCDF`, `geometricUniformCDF_nonneg`, `geometricUniformCDF_le_one`, `measurable_geometricUniformCDF`, `continuous_geometricUniformCDF`, `geometricUniformCDF_reflection`, `geometricUniformCDF_one_half`, `geometricUniformCDF_zero_of_nonpos`, `geometricUniformCDF_one_of_one_le`, `geometricUniformCDF_eq_integral`, `geometricUniformCDF_eq_intervalIntegral`, `geometricUniformDensity`, `geometricUniformCDF_hasDerivAt`, `deriv_geometricUniformCDF`, `continuous_geometricUniformDensity`, `geometricUniformDensity_nonneg`, `geometricUniformDensity_zero_of_nonpos`, `geometricUniformDensity_zero_of_one_le`, `support_geometricUniformDensity_subset_Ioo`, `support_geometricUniformDensity_subset_Icc`, `tsupport_geometricUniformDensity_subset_Icc`, `geometricUniformDensity_hasCompactSupport`, `geometricUniformDensity_reflection`, `geometricUniformDistribution_eq_withDensity`, `contDiff_geometricUniformCDF`, `contDiff_geometricUniformDensity`; continuity and CDF reflection assume `|q| < 1`, exterior CDF values assume `0 ≤ q < 1`, and the conditioning, density, `withDensity`, compact-support, and `C∞` results assume `0 < q < 1`; the density definition is total, but only this strict positive range has the classical density interpretation; the characteristic-function sinc-prefix results are listed separately above |
| Product-probability and CDF representations | `FabiusFunction.ProbabilityRepresentation` | `weightedCoordinateSum_eq_weightedUniformSeries`, `weightedCoordinateSum_eq_geometricUniformSeries_one_half`, `weightedSumDistribution_eq_geometricUniformDistribution_one_half`, `ae_weightedSumDistribution_mem_Icc`, `weightedSumDistribution_restrict_Icc`, `weightedSumCDF_eq_geometricUniformCDF_one_half`, `weightedSumCDF_eq_fabiusReal`, `geometricUniformCDF_one_half_eq_fabiusReal`, `geometricUniformDensity_one_half_eq_rvachevUp`, `fabiusReal_eq_weightedSum_probability`, `rvachevUp_eq_weightedSumCDF`, `rvachevUp_eq_weightedSum_probability_global`; the dyadic smoothing, continuity, exterior-value, and reflection proofs route through the half-base geometric CDF API |
| Generic finite moment functionals and Hankel Gram forms | `FabiusFunction.FiniteMomentGram` | `momentFunctional`, `momentFunctional_of_linearMap`, `momentFunctional_map`, `momentPairing`, `momentHankelMatrix`, `momentHankelMatrix_succ_submatrix`, `momentHankelDet`, `map_momentHankelDet`, `finiteMomentPairing_toMatrix`, `finiteMomentPairing_nondegenerate_iff`; this measure-free layer works over the stated semiring, commutative-ring, and integral-domain hypotheses and by itself asserts no positivity |
| Generic fraction-free and normalized Gram--Stieltjes polynomials | `FabiusFunction.GramStieltjes` | `gramStieltjesNumerator`, `momentPairing_gramStieltjesNumerator_eq_coeff_mul_det`, `momentPairing_gramStieltjesNumerator_self`, `gramStieltjesPolynomial`, `gramStieltjesPolynomial_isMonicOfDegree`, `momentPairing_gramStieltjesPolynomial_eq_zero`, `eq_gramStieltjesPolynomial_of_isMonicOfDegree_of_orthogonal`, `momentPairing_gramStieltjesPolynomial_self`; the fraction-free construction is over a commutative ring, while field normalization and uniqueness assume the displayed Hankel minor is nonzero |
| Generic finite Jacobi coefficients and three-term recurrence | `FabiusFunction.FiniteMomentJacobi` | `momentPairing_X_mul_left`, `gramStieltjesNorm`, `gramStieltjesJacobiDiagonal`, `gramStieltjesJacobiSubdiagonal`, `gramStieltjesJacobiSubdiagonal_eq_det_ratio`, `gramStieltjesPolynomial_three_term_zero`, `gramStieltjesPolynomial_three_term`; over a field, a nonzero first Hankel minor gives the degree-zero base equation and three consecutive nonzero Hankel minors give every higher finite recurrence, with no measure, positivity, root, quadrature, continued-fraction, or convergence assumption |
| Polynomial-basis moment Gram determinants | `FabiusFunction.PolynomialMomentGramDeterminant` | Exhaustive public inventory: two definitions, `polynomialCoefficientMatrix` and `polynomialMomentGramMatrix`; and seven theorems, `polynomialCoefficientMatrix_apply`, `polynomialMomentGramMatrix_apply`, `polynomialMomentGramMatrix_eq_transpose_mul_hankel_mul`, `polynomialMomentGramMatrix_det_eq_coefficient_det_sq_mul`, `polynomialCoefficientMatrix_det_eq_prod_coeff`, `polynomialMomentGramMatrix_det_eq_prod_coeff_sq_mul`, and `gramStieltjesJacobiSubdiagonal_eq_polynomialMomentGramMatrix_det_ratio`.  For a family with `natDegree (p k) ≤ k`, its coefficient matrix `C` is upper triangular and direct bilinear expansion gives `G = Cᵀ H C`; determinant multiplicativity and the diagonal product give `det G = (∏ k, coeff (p k) k)^2 det H`, and a nonzero diagonal transports the zero-based Jacobi subdiagonal to the corresponding Gram-determinant cross-ratio.  No Hankel-nonvanishing hypothesis is imposed on that last Lean equality: division in a field is total, so if the middle Hankel determinant is zero then both cross-ratios are zero; that singular case is not a genuine nonsingular Jacobi recurrence.  This is finite algebra only: it asserts no measure, positivity, orthogonality, entry rationality, Gaunt/Wigner/`3j` formula, Christoffel reconstruction, or infinite Jacobi theory. |
| Scalar naturality of finite Gram--Stieltjes and Jacobi data | `FabiusFunction.GramStieltjesNaturality` | Exhaustive public inventory: zero definitions and six theorems, `momentPairing_map`, `map_gramStieltjesNumerator`, `map_gramStieltjesPolynomial`, `map_gramStieltjesNorm`, `map_gramStieltjesJacobiDiagonal`, and `map_gramStieltjesJacobiSubdiagonal`.  The pairing theorem is over commutative semirings, the fraction-free numerator theorem over commutative rings, and the normalized polynomial, norm, and Jacobi theorems over fields.  This is finite scalar base change only, with no measure, positivity, computation, or convergence claim. |
| Exact all-degree rational Jacobi system of the Rvachev up law | `FabiusFunction.RvachevRationalJacobi` | Exhaustive public inventory: four definitions, `rvachevHankelDetRat`, `rvachevOrthoPolynomialRat`, `rvachevOrthoNormRat`, and `rvachevJacobiSubdiagonalRat`; and thirteen theorems, `upMoment_eq_rvachevRawMomentRat_cast`, `rvachevHankelDetRat_cast`, `rvachevHankelDetRat_pos`, `rvachevOrthoPolynomialRat_cast`, `rvachevOrthoPolynomialRat_isMonicOfDegree`, `momentPairing_rvachevOrthoPolynomialRat_eq_zero`, `rvachevOrthoNormRat_cast`, `rvachevOrthoNormRat_pos`, `gramStieltjesJacobiDiagonal_rvachevRawMomentRat_eq_zero`, `rvachevJacobiSubdiagonalRat_cast`, `rvachevJacobiSubdiagonalRat_pos`, `rvachevJacobiSubdiagonalRat_eq_det_ratio`, and `rvachevOrthoPolynomialRat_three_term`.  These noncomputable finite definitions give positive rational Hankel determinants, monic orthogonal polynomials, positive norms, zero diagonal, positive subdiagonals, cast comparison with every analytic Fabius representative, the determinant cross-ratio, and the exact rational recurrence in every degree.  The zero-based `rvachevJacobiSubdiagonalRat n` is the conventional coefficient `beta_(n+1)`.  No explicit value for the report's `H_4` or `beta_4`, native-code evaluator, root/quadrature theorem, continued fraction, Padé theorem, or asymptotic result is asserted. |
| Legendre Gram/Hankel determinant bridge for the up law | `FabiusFunction.FabiusLegendreHankelDeterminant` | Exhaustive public inventory: two definitions, `upLegendreGramMatrix` and `upLegendreGramDet`; and seven theorems, `upLegendreGramMatrix_apply_eq_integral`, `upLegendreGramDet_eq_prod_leadingCoeff_sq_mul_hankelDet`, `upLegendreGramDet_zero`, `upLegendreGramDet_pos`, `coeff_legendrePolynomial_self_div_succ`, `gramStieltjesJacobiSubdiagonal_upMoment_eq_upLegendreGramDet_ratio`, and `rvachevJacobiSubdiagonalRat_cast_eq_upLegendreGramDet_ratio`.  Writing `D_n` for the determinant of the first `n` ordinary Legendre polynomials in the up-moment pairing and `L_j = 2^(-j) * choose (2*j) j`, the determinant identity `D_n = (∏ j<n, L_j^2) * hankelDet F n`, the empty `0×0` convention `D_0 = 1`, the leading-coefficient quotient, and the real Gram cross-ratio hold for every `F : BoundedFabius`.  Identifying an entry with an integral, strict positivity, and the rational-cast bridge additionally require `IsFabius F`.  Its zero-based index `n` is the conventional `beta_(n+1)` and satisfies `beta_(n+1) = ((n+1)/(2*n+1))^2 * D_(n+2) * D_n / D_(n+1)^2`; in the arbitrary-`BoundedFabius` real theorem this is the same totalized-division equality, while `IsFabius` supplies nonvanishing through positivity and makes it a genuine Jacobi formula.  It does not give a Gaunt/Wigner/`3j` entry expansion or entrywise rationality by that route, Christoffel reconstruction, or an infinite product.  The unrelated `rvachevTranslateGram` is the Gram kernel of shifted-up atoms under unweighted interval integration, not this polynomial-basis moment Gram matrix. |
| Comparison of generic Gram--Stieltjes algebra with the up measure | `FabiusFunction.OrthogonalPolynomialGramBridge` | `momentFunctional_upMoment_eq_integral`, `momentPairing_upMoment_eq_integral`, `momentHankel_eq_momentHankelMatrix`, `hankelDet_eq_momentHankelDet`, `hankelOrthoPolynomial_eq_gramStieltjesNumerator`, `upOrthoPolynomial_eq_gramStieltjesPolynomial`, `hankelRatio_eq_gramStieltjesNorm`, `gramStieltjesJacobiDiagonal_upMoment_eq_zero`, `gramStieltjesJacobiSubdiagonal_upMoment_eq`; these theorems identify both determinant constructions, their monic normalizations, and their finite Jacobi data exactly |
| Fabius-measure Hankel positivity and finite orthogonal-polynomial recurrence | `FabiusFunction.MomentHankelMatrix`, `FabiusFunction.MomentHankelValues`, `FabiusFunction.OrthogonalPolynomialConstruction`, `FabiusFunction.OrthogonalPolynomialParity`, `FabiusFunction.OrthogonalPolynomialRecurrence`, `FabiusFunction.OrthogonalPolynomialJacobi` | `momentHankel_posDef`, `hankelDet_pos`, `hankelRatio_pos`, `upOrthoPolynomial_monic`, `integral_upOrthoPolynomial_sq`, `eq_upOrthoPolynomial_of_monic_of_orthogonal`, `upOrthoPolynomial_comp_neg_X`, `upOrthoPolynomial_three_term`, `upOrthoPolynomial_two`, `upOrthoPolynomial_three`, `upOrthoPolynomial_four`; roots and Gaussian/Lobatto quadrature, finite or infinite continued-fraction identification, and convergence remain separate |
| Generic oriented Cauchy calculus for finite real measures | `FabiusFunction.MeasureCauchyTransform` | Exhaustive public surface: `measureCauchyDomain`, `measureCauchyTransform`, `measureCauchyPower`, `measureCauchyTransform_apply`, `measureCauchyPower_one`, `measureCauchyPower_map_affine`, `measureCauchyTransform_map_affine`, `isOpen_measureCauchyDomain`, `hasDerivAt_measureCauchyTransform`, `analyticOn_measureCauchyTransform`, `measureCauchyPower_succ_of_uniformAffineFixedPoint`, `hasDerivAt_measureCauchyTransform_of_uniformAffineFixedPoint`.  The affine-map identities are total and allow negative nonzero scale.  The two fixed-point theorems require only a finite measure, support in an affine-invariant carrier, nonzero uniform and tail scales, and the displayed uniform affine equality in law; they require neither probability normalization nor topological or measurable hypotheses on the carrier. |
| Generic centered moment/Laurent calculus for bounded finite real measures | `FabiusFunction.MeasureCauchyMomentLaurent` | Exhaustive public surface (one definition and fifteen theorems): `measureCauchyMoment`, `inv_sub_eq_sum_range_add`, `measureCauchyMoment_zero`, `measurable_inv_sub_rclike`, `integrable_centered_pow_div_sub_of_ae_norm_sub_le`, `integrable_inv_sub_of_ae_norm_sub_le`, `norm_measureCauchyMoment_le`, `integral_inv_sub_eq_sum_range_measureCauchyMoment_add`, `norm_integral_inv_sub_sub_sum_range_measureCauchyMoment_le`, `summable_measureCauchyMoment_laurent`, `integral_inv_sub_eq_tsum_measureCauchyMoment`, `hasSum_measureCauchyMoment_laurent`, `measureCauchyTransform_eq_sum_range_measureCauchyMoment_add`, `norm_measureCauchyTransform_sub_sum_range_measureCauchyMoment_le`, `measureCauchyTransform_eq_tsum_measureCauchyMoment`, `hasSum_measureCauchyTransform_measureCauchyMoment_laurent`.  Apart from the field-generic kernel identity, the API works over any `RCLike 𝕜`.  For a finite real measure, arbitrary `c z : 𝕜`, `0 ≤ R`, almost-everywhere support `‖(x : 𝕜) - c‖ ≤ R`, and `R < ‖z-c‖`, it gives the positive-sign expansion in `measureCauchyMoment μ c k / (z-c)^(k+1)`, exact remainder, mass-weighted error `μ.real Set.univ * (‖z-c‖-R)⁻¹ * (R/‖z-c‖)^N`, and `Summable`/`tsum`/`HasSum` forms.  The last four theorems are the complex wrappers for the named oriented transform; no probability normalization or topological-support theorem is assumed. |
| Geometric-uniform Cauchy--Stieltjes hierarchy | `FabiusFunction.GeometricUniformCauchy` | Exhaustive public surface: `geometricUniformStieltjesDomain`, `geometricUniformStieltjesTransform`, `geometricUniformStieltjesPower`, `geometricUniformStieltjesTransform_apply`, `geometricUniformStieltjesPower_one`, `isOpen_geometricUniformStieltjesDomain`, `analyticOn_geometricUniformStieltjesTransform`, `hasDerivAt_geometricUniformStieltjesTransform_refinement`, `geometricUniformStieltjesPower_succ`.  Definitions are total in real `q`; holomorphy assumes `|q| < 1`, and the divided DDE and adjacent-power recurrence also assume `q ≠ 0`.  Negative `q` is included by using the exact series range as invariant carrier; the divided formulas deliberately exclude `q=0`. |
| Ordinary Cauchy--Stieltjes transforms and powers of the canonical up and unit-interval laws | `FabiusFunction.CauchyTransform` | Exhaustive public surface: `rvachevCauchyDomain`, `fabiusStieltjesDomain`, `rvachevCauchyTransform`, `fabiusStieltjesTransform`, `rvachevCauchyPower`, `fabiusStieltjesPower`, `rvachevCauchyTransform_apply`, `fabiusStieltjesTransform_apply`, `rvachevCauchyPower_one`, `fabiusStieltjesPower_one`, `rvachevCauchyTransform_eq_integral_rvachevUp`, `isOpen_rvachevCauchyDomain`, `isOpen_fabiusStieltjesDomain`, `hasDerivAt_rvachevCauchyTransform`, `hasDerivAt_fabiusStieltjesTransform`, `analyticOn_rvachevCauchyTransform`, `analyticOn_fabiusStieltjesTransform`, `fabiusStieltjesTransform_eq_two_mul_rvachevCauchyTransform`, `rvachevCauchyTransform_eq_inv_two_mul_fabiusStieltjesTransform`, `fabiusStieltjesPower_eq_two_pow_mul_rvachevCauchyPower`, `hasDerivAt_fabiusStieltjesTransform_refinement`, `fabiusStieltjesPower_succ`, `rvachevCauchyPower_succ`.  The integral definitions and affine transform/power bridges are total under Lean's Bochner-integral convention; holomorphy, derivative, DDE, and adjacent-order statements use the named slit domains.  The unit DDE and both complex-domain adjacent-power recurrences are direct named theorems; the centered DDE and its Thue--Morse derivative orbit remain the direct named results of `CauchyRenormalization`. |
| Atom-exact compact-support Cauchy--CDF integration by parts | `FabiusFunction.CauchyCDF` | `integral_inv_sub_eq_mass_smul_sub_intervalIntegral_measureReal_Iic`, `integral_inv_sub_eq_sub_intervalIntegral_cdf`, `fabiusStieltjesTransform_eq_inv_sub_one_sub_intervalIntegral_fabiusReal`; the generic results assume an ordered compact interval, almost-everywhere support there, and a spectral parameter off its complexification, with finite-measure and probability normalizations respectively; the Fabius wrapper is on `fabiusStieltjesDomain` |
| Survival and all-power Cauchy integration by parts | `FabiusFunction.CauchySurvival`, `FabiusFunction.CauchyHigherPowers` | `intervalIntegral_inv_sub_sq`, `integral_inv_sub_eq_mass_smul_add_intervalIntegral_measureReal_Ioi`, `fabiusStieltjesTransform_eq_inv_add_intervalIntegral_rvachevUp`, `hasDerivAt_pow_inv_sub`, `intervalIntegral_pow_inv_sub`, `integral_pow_inv_sub_eq_mass_smul_sub_intervalIntegral_measureReal_Iic`, `integral_pow_inv_sub_eq_mass_smul_add_intervalIntegral_measureReal_Ioi`; these are direct named CDF/survival formulas, including atoms, and do not by themselves identify the all-order Thue--Morse derivative orbit with a single named higher-kernel formula. |
| Rvachev Cauchy-transform renormalization and all-order affine orbit | `FabiusFunction.CauchyRenormalization` | `mapsTo_rvachevCauchyDomain_two_mul_add_one`, `mapsTo_rvachevCauchyDomain_two_mul_sub_one`, `hasDerivAt_rvachevCauchyTransform_affineDifference`, `deriv_rvachevCauchyTransform`, `iteratedDeriv_rvachevCauchyTransform_eq_thueMorse_sum`; for every bounded Fabius solution and every point off `[-1,1]`, the exact DDE and all complex derivative orbits hold. |
| Real logarithmic and resolvent-order fixed-point calculus | `FabiusFunction.StieltjesLogFixedPoint`, `FabiusFunction.StieltjesResolventHierarchy`, `FabiusFunction.StieltjesGeneralizedOrder` | The direct named theorems prove the logarithmic fixed-point representation and every positive integer-order hierarchy for real `z > 1`, and the order-lowering hierarchy for real order `α > 1` and real `z > 1`.  These results do not provide a complex logarithm/branch continuation or complex order. |
| Up-measure Laurent, Herglotz, and integrated Stieltjes--Perron layers | `FabiusFunction.StieltjesMomentLaurent`, `FabiusFunction.StieltjesCauchyTransform`, `FabiusFunction.StieltjesHerglotz`, `FabiusFunction.StieltjesInversion`, `FabiusFunction.StieltjesPerron` | The radius-one, center-zero up-measure Laurent layer is connected to the generic API by `ae_norm_sub_zero_le_one_rvachevMeasure` and `measureCauchyMoment_rvachevMeasure_zero` and retains the report-facing `upMoment` results in real exterior and complex `‖z‖ > 1` form.  The remaining direct named theorems give conjugation and upper/lower-half-plane sign and quantitative bounds, exact finite-height Poisson/conjugate-Poisson representations, approximate-identity estimates, and integrated interval Stieltjes--Perron inversion.  Pointwise or nontangential Sokhotski--Plemelj boundary values and principal-value Hilbert-transform identities remain open. |
| Initial exact Jacobi data | `FabiusFunction.OrthogonalPolynomialJacobi` | Direct named theorems compute additional low moments, Hankel determinants and ratios, and the monic degree-three and degree-four orthogonal polynomials with norm/evaluation corollaries.  A full J-fraction/Padé convergence theory and asymptotic Jacobi analysis remain frontier work. |
| Support-free quantile transport, compact inverse-CDF transport, and exact Fabius substitution | `FabiusFunction.QuantileTransport` | `map_quantile_eq`, `map_inverseCDF_volume_restrict_Icc`, `map_fabiusInv_restrict_Icc_eq_weightedSumDistribution`, `integral_comp_fabiusInv_restrict_Icc_eq_weightedSumDistribution` |
| Weighted subgraph/supergraph Fubini, generic survival layer cake, and exact Rvachev stopped primitives | `FabiusFunction.SubgraphFubini`, `FabiusFunction.SurvivalLayerCake`, `FabiusFunction.ProbabilityLaplaceMoments` | `integral_smul_setIntegral_subgraph`, `integral_smul_setIntegral_supergraph`, `intervalIntegral_survival_smul_eq_integral_clamp`, `intervalIntegral_survival_smul_eq_integral_min_of_ae_mem_Icc`, `intervalIntegral_survival_smul_eq_integral_of_ae_mem_Icc`, `intervalIntegral_rvachevUp_smul_eq_integral_min`, `intervalIntegral_rvachevUp_smul_eq_integral` |
| Atom-preserving lower-CDF layer cake and exact positive-real Fabius fractional integrals | `FabiusFunction.CDFLayerCake`, `FabiusFunction.FractionalCDFLayerCake`, `FabiusFunction.FabiusFractionalIntegral` | `intervalIntegral_cdf_smul_eq_integral_clamp`, `intervalIntegral_cdf_smul_eq_integral_max_of_ae_le`, `intervalIntegral_cdf_smul_eq_integral_max_of_ae_mem_Icc`, `intervalIntegral_cdf_smul_eq_integral_of_ae_mem_Icc`, `fractionalVolterra_measureReal_Iic_eq_integral_clamp`, `fractionalVolterra_measureReal_Iic_eq_integral_posPart`, `fractionalVolterra_cdf_eq_integral_posPart`, `fractionalVolterra_measureReal_Iic_eq_integral_rpow_of_ae_mem_Icc`, `fractionalVolterra_fabiusReal_eq_integral_posPart`, `fractionalVolterra_fabiusReal_eq_uniformProduct_integral_posPart`, `fractionalVolterra_fabiusReal_one_eq_integral_rpow`, `fractionalVolterra_fabiusReal_one_eq_uniformProduct_integral_rpow`; the partial terminal identity needs only `c ≤ b` and almost-everywhere upper support `z ≤ b`, the probability wrapper is stated directly with Mathlib's CDF, and the Fabius stopped-power formulas hold for every real endpoint and every positive real order; no fractional derivative or complex-order continuation is asserted |
| Generic inverse-clock and exact Fabius weighted layer-cake identities | `FabiusFunction.InverseLayerCake` | `galoisConnection_Icc_restrict_of_lt_iff_lt`, `intervalIntegral_smul_intervalIntegral_of_lt_iff_lt`, `intervalIntegral_smul_comp_of_lt_iff_lt`, `intervalIntegral_mul_comp_sub_of_lt_iff_lt_of_absolutelyContinuousOnInterval`, `intervalIntegral_mul_comp_of_lt_iff_lt_of_absolutelyContinuousOnInterval`, `intervalIntegral_smul_intervalIntegral_fabiusInv`, `intervalIntegral_smul_comp_fabiusInv`, `intervalIntegral_mul_comp_fabiusInv_of_absolutelyContinuousOnInterval`, `intervalIntegral_mul_fabiusInv_eq`, `intervalIntegral_fabiusInv_eq_intervalIntegral_rvachevUp`, `intervalIntegral_fabiusInv_eq_one_half`; the strict order adjunction makes the interval restrictions a Galois connection and supplies measurable clamped representatives, so none of the public generic layer-cake theorems assumes clock measurability; the explicit-primitive and pointwise-`C¹` forms allow real or complex weights and Banach-valued primitives, while the absolutely-continuous forms allow real or complex `L¹` weights and a real-valued primitive, include degenerate ordered rectangles, and need no separate right-hand-side integrability hypothesis |
| Absolutely-continuous two-function and variable-upper calculus for inverse-order pairs | `FabiusFunction.InversePairIntegral` | `intervalIntegral_deriv_mul_comp_add_comp_mul_deriv_of_lt_iff_lt`, `intervalIntegral_deriv_mul_comp_add_comp_mul_deriv_to_of_lt_iff_lt`, `intervalIntegral_deriv_mul_fabiusReal_add_fabiusInv_mul_deriv`, `intervalIntegral_deriv_mul_fabiusReal_add_fabiusInv_mul_deriv_to`, `intervalIntegral_fabiusReal_add_fabiusInv_eq_one`, `intervalIntegral_fabiusInv_to_eq_mul_sub_intervalIntegral_fabiusReal`; the generic theorems derive monotonicity and measurable clamped extensions of both clocks from the strict order equivalence, include degenerate ordered intervals, and cover every proper compact cut `y ∈ [a,b]`; reversed endpoints still require swapping the corresponding interval, and improper singular endpoints, higher or fractional inverse primitives, complex-valued arbitrary-AC factors, and complex Mellin continuation are not claimed |
| Weighted-partition exponential coefficients over commutative `ℚ`-algebras | `FabiusFunction.ExponentialPartition`, `FabiusFunction.ExponentialBell` | `partitionExpSum_recurrence`, `partitionExpSum_succ`, `partitionExpSum_eq_sum_div`, `partitionExpSum_eq_expCoeff` |
| Complete Bell and moment--cumulant transforms over commutative `ℚ`-algebras | `FabiusFunction.MomentCumulantAlgebra` | `factorialNormalize`, `completeBellPolynomial`, `momentCumulant`, `completeBellPolynomial_succ`, `completeBellPolynomial_momentCumulant`, `momentCumulant_completeBellPolynomial` |
| Euler product transform with natural multiplicities | `FabiusFunction.WeightedEulerTransform` | Exhaustive public surface: `summable_sigma_fin_iff`, `tprod_sigma_fin_eq_tprod_pow`, `tsum_sigma_fin_eq_tsum_nsmul`, `tprod_one_sub_pow_eq_cexp_powerSum`.  The base index is countable.  The summability equivalence assumes a nonnegative real family; the product and sum transfers assume the corresponding sigma-indexed family is multipliable or summable.  The Euler transform assumes `∀ i, ‖f i‖ < 1` and summability of `i ↦ (c i : ℝ) * ‖f i‖`; it is branch-free and asserts no logarithm-of-a-power or principal-log identity. |
| General-weight Euler--zeta expansion of the generalized sinc product | `FabiusFunction.GeneralizedSincZeta` | Exhaustive public surface: `weightedScaleSeries`, `summable_weightedScaleSeries_real`, `summable_weightedScaleSeries`, `tsum_weighted_div_two_pow_even_pow`, `weighted_sinc_pair_powerSum`, `generalizedRvachevProduct_eq_cexp`.  The series definition is total in the natural weight `a` and natural index `k`.  Every theorem assumes admissibility `Summable fun h : ℕ => (a h : ℝ) / 2 ^ h`; the two scale-series summability results and the weighted scale-collapse theorem additionally require `k ≠ 0`.  The pair power-sum theorem holds for every complex `z` and natural `r`, while the product expansion assumes exactly `‖z‖ < 1`.  This is an analytic exponential expansion, not a principal-log, characteristic-function, probabilistic-cumulant, or support theorem. |
| Alternating Newton Euler--zeta kernel | `FabiusFunction.AlternatingNewtonCumulantKernel` | Exhaustive public surface: `tsum_alternatingNewtonWeight_inv_four_pow`, `weightedScaleSeries_alternatingNewton`, `alternatingNewton_eq_cexp`.  The two kernel evaluations hold for every natural `d` and require `k ≠ 0`; the exponential theorem holds for every natural `d` under exactly `‖z‖ < 1`.  The natural weight exists for every `d`, but agreement with the source volume's signed generalized-binomial convention requires even `d`.  These are analytic identities only, with no characteristic-function, probabilistic-cumulant, or variance interpretation. |
| Nonmonic Hensel lifting and formal implicit roots | `FabiusFunction.ImplicitPowerSeries` | `FormalImplicitRoot.exists_isRoot_sub_mem`, `FormalImplicitRoot.eq_of_isRoot_of_sub_mem`, `FormalImplicitRoot.existsUnique_isRoot_sub_mem`, `PowerSeries.Implicit.existsUnique_isRoot_constantCoeff`, `PowerSeries.Implicit.existsUnique_zeroConstant_root`, `PowerSeries.Implicit.root`, `PowerSeries.Implicit.constantCoeff_root`, `PowerSeries.Implicit.eval_root`, `PowerSeries.Implicit.eq_root`; this is a generic formal-series root engine over complete adic commutative rings and arbitrary commutative coefficient rings, with no concrete inverse-Fabius germ, analytic convergence, plateau localization, flat-remainder, or quantile theorem |
| Quarter Catalan formal germ and dyadic-rescaling bridge | `FabiusFunction.QuarterCatalanGerm` | Exhaustive public surface (two definitions and thirteen theorems): `quarterCatalanCoefficient`, `quarterCatalanCoefficient_zero`, `quarterCatalanCoefficient_succ_eq_report`, `quarterCatalanGermSeries`, `quarterCatalanGermSeries_coeff`, `quarterCatalanGermSeries_coeff_succ`, `quarterCatalanGermSeries_constantCoeff`, `quarterCatalanGermSeries_equation`, `powerSeries_quadratic_injectiveOn_zeroConstant`, `eq_quarterCatalanGermSeries_of_equation`, `existsUnique_quarterCatalanGermSeries`, `dyadicGermTwo_functionalEquation`, `rescale_dyadicGermTwo_eq_quadraticInverse`, `dyadicGermTwo_eq_rescale_quadraticInverse`, `coeff_dyadicGermTwo_succ`.  The explicit Catalan coefficient sequence and its rational power series give the unique zero-constant solution of `D + 4D² = (4/9)X`.  Rescaling the dyadic parameter by `9/4` identifies the distinguished dyadic germ exactly with the Catalan inverse of `X + 4X²`, and every positive coefficient is `(4/9)^(m+1) (-4)^m C_m`.  This module is formal power-series algebra only; the downstream actual-jet bridge is supplied separately. |
| Actual quarter inverse Catalan jet | `FabiusFunction.FabiusInverseQuarterJet` | Exhaustive public surface: `iteratedDeriv_centeredFabiusInv_quarter_eq_quadraticInverse`, `iteratedDeriv_fabiusInv_five_seventy_two_succ`.  For every bounded Fabius solution, the full centered derivative jet at `5/72 = F(1/4)` equals the factorial-scaled coefficient sequence of `QuadraticInverse.inverse 4`; in particular `G^(m+1)(5/72) = (m+1)! (-4)^m C_m`.  This is equality of all jets, not local analytic equality: it neither erases the known nonanalytic flat defect nor proves that defect is nonzero by a named remainder theorem. |
| Finite polynomial integrals from raw moments and formal cumulants | `FabiusFunction.PolynomialExpectationCumulant` | `integral_eval₂_eq_sum_moment`, `integral_eval₂_eq_sum_completeBell_momentCumulant_with_mass_correction`, `integral_eval₂_eq_sum_completeBell_momentCumulant_of_moment_zero_eq_one`, `integral_eval₂_eq_sum_completeBell_momentCumulant` |
| Rvachev raw moments, triangular and injective reciprocal-moment Appell deconvolution, and exact shifted-up polynomial synthesis | `FabiusFunction.RvachevMomentAppell`, `FabiusFunction.RvachevPolynomialSynthesis` | `rvachevRawMomentRat`, `rvachevReciprocalMomentRat`, `rvachevAppellPolynomial`, `rvachevDeconvolvedPolynomial`, `rvachevDeconvolutionLinearMap`, `rvachevDeconvolvedPolynomial_finsetSum`, `rvachevDeconvolvedPolynomial_monomial`, `rvachevDeconvolvedPolynomial_X_pow`, `coeff_rvachevDeconvolvedPolynomial_natDegree`, `natDegree_rvachevDeconvolvedPolynomial`, `leadingCoeff_rvachevDeconvolvedPolynomial`, `rvachevDeconvolvedPolynomial_eq_zero_iff`, `rvachevDeconvolutionLinearMap_injective`, `rvachevDeconvolvedPolynomial_injective`, `integral_eval_rvachevDeconvolvedPolynomial_add_mul_rvachev`, `tsum_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`, `normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp` |
| Sharp universal composite-mesh exactness and least natural meshes | `FabiusFunction.CompositeMeshSharpness` | Exhaustive public surface: `exists_shift_tsum_shifted_monomial_ne_integral_nat_real`, `rvachevCombExactThrough`, `rvachevCombExactThrough_iff_padicValNat`, `rvachevCombExactThrough_iff_pow_two_dvd`, `rvachevCombExactThrough_two_pow`, `two_pow_le_of_rvachevCombExactThrough`, `isLeast_rvachevCombExactThrough`, `isLeast_rvachevCombExactThrough_even`.  The `IsLeast` results quantify over meshes exact for the whole real polynomial space through the stated degree; they do not assert minimality for an individual Legendre polynomial, a fixed Legendre partial sum, or a target-adapted mesh. |
| Universal endpoint-transfer polynomials and their formal exponential series | `FabiusFunction.EndpointTransferPolynomials` | `endpointTransferPolynomial_succ`, `endpointTransferPolynomial_eq_partitionExpSum`, `endpointTransferSeries_eq_exp_subst`, `aeval_endpointTransferPolynomial`, `map_endpointTransferSeries` |
| Finite base-`b` layer regrouping in multiplicative and additive form | `FabiusFunction.BaseLayerRegrouping` | `filter_dvd_eq_image`, `prod_multiples_eq_prod_filter`, `sum_multiples_eq_sum_filter`, `prod_layers_eq_prod_pow_card`, `sum_layers_eq_sum_nsmul_card`, `card_filter_pow_dvd`, `prod_layers_eq_prod_pow_multiplicity`, `sum_layers_eq_sum_nsmul_multiplicity` |
| Complete homogeneous evaluations, their finite formal generating series, fixed-degree asymptotic bounds, denominator-free geometric principal specialization, and a second proof of Gaussian symmetry | `FabiusFunction.CompleteHomogeneous`, `FabiusFunction.CompleteHomogeneousGenerating`, `FabiusFunction.CompleteHomogeneousAsymptotics`, `FabiusFunction.GeometricCompleteHomogeneous` | In addition to the generic evaluator, generating-series, and asymptotic APIs, `GeometricCompleteHomogeneous` exhaustively exports six theorems: `completeHomogeneousEval_geometric`, `completeHomogeneousEval_scaled_geometric`, `completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial`, `completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial_degree`, `gaussianBinomial_add_symm`, and `gaussianBinomial_symm_via_completeHomogeneous`.  The principal specializations and both symmetry proofs hold over every commutative semiring without distinctness, division, cancellation, ordering, topology, or convergence assumptions; the separate generating identities are purely formal, while the asymptotic theorem transfers coordinatewise Big-O through every fixed homogeneous degree. |
| Infinite products at summable scales | `FabiusFunction.ScaledInfiniteProducts` | `summable_norm_scaled_sub_one`, `hasProdUniformlyOn_scaled`, `multipliableUniformlyOn_scaled`, `hasProdLocallyUniformly_scaled`, `multipliableLocallyUniformly_scaled`, `continuous_tprod_scaled`, `differentiable_tprod_scaled`, `differentiable_tprod_scaled_of_eq_one`, `tprod_scaled_ne_zero`, `tprod_scaled_eq_zero_iff`; pointwise deviation summability allows an arbitrary normed-ring target, the compact-uniform API assumes a continuous factor and a complete commutative normed-ring target with a normed unit, local uniformity adds local compactness, holomorphy uses a complete normed complex-algebra target, and zero detection adds a multiplicative norm but needs neither continuity nor local compactness |
| Geometric reciprocal-Gamma products and the dyadic Rvachev bridge | `FabiusFunction.GeometricReciprocalGamma` | `shiftedReciprocalGamma`, `shiftedReciprocalGamma_zero`, `shiftedReciprocalGamma_differentiable`, `shiftedReciprocalGamma_sub_one_isBigO`, `shiftedReciprocalGamma_eq_zero_iff`, `shiftedReciprocalGamma_mul_neg`, `summable_norm_qpow`, `geometricReciprocalGamma`, `geometricReciprocalGammaFactors_multipliable`, `geometricReciprocalGamma_differentiable`, `geometricReciprocalGamma_zero`, `geometricReciprocalGamma_mahler`, `geometricReciprocalGamma_eq_zero_iff`, `geometricGamma`, `geometricGamma_meromorphic`, `geometricGamma_mahler`, `geometricSincProduct`, `geometricReciprocalGamma_mul_neg`, `dyadicReciprocalGamma`, `dyadicGamma`, `dyadicReciprocalGamma_differentiable`, `dyadicReciprocalGamma_zero`, `geometricSincProduct_inv_two`, `dyadicReciprocalGamma_mul_neg`, `rvachevFourierProduct_eq_one_div_dyadicGamma_mul`; every generic analytic identity assumes complex `q` with `‖q‖ < 1` (including `q=0`), while normalization at zero is unconditional; `geometricGamma` and `dyadicGamma` are totalized pointwise inverses, not proved raw Gamma tprods away from poles |
| Complex infinite `q`-Pochhammer convergence and the dyadic Rvachev spectral factorization | `FabiusFunction.RvachevPochhammerFactorization` | Exhaustive public surface (one definition and six theorems): `complexQPochhammerInf`; `complexQPochhammerInf_eq_tprod`, `multipliable_one_sub_mul_pow_complex`, `hasProd_complexQPochhammerInf`, `tendsto_finiteQPochhammerIn_complex`, `rvachevFourierProduct_eq_tprod_complexQPochhammerInf`, and `rvachevFourier_eq_tprod_complexQPochhammerInf`.  The symbol is a total complex `tprod`; its named multipliability, product, and finite-prefix convergence theorems require exactly `‖q‖ < 1` and impose no restriction on `a`.  The two spectral theorems are not general-`q` results: they fix the dyadic scale `q = 1/2`, hence Pochhammer nome `1/4`, and hold for every complex `z`, including zeros, without a nonvanishing hypothesis; the Fourier-transform form assumes exactly a bounded Fabius witness and `IsFabius`.  Under the frontier normalization `t = 4πz`, the standalone-product theorem is precisely the inside `q = 1/2` specialization of the centered sinc--Pochhammer formula.  It does not prove the general-`q` characteristic/MGF identity, the reciprocal `|q| > 1` formula, zero--pole exchange, or local-uniform/normal convergence |
| Exact dyadic reciprocal-Gamma zeros and meromorphic pole orders | `FabiusFunction.DyadicGammaOrder` | `dyadicReciprocalGamma_eq_zero_iff`, `dyadicReciprocalGamma_int_ne_zero_of_nonneg`, `dyadicReciprocalGamma_nat_ne_zero`, `dyadicGamma_meromorphic`, `analyticOrderAt_dyadicReciprocalGamma_int_of_neg`, `analyticOrderAt_dyadicReciprocalGamma_neg_nat`, `meromorphicOrderAt_dyadicGamma_int_of_neg`, `meromorphicOrderAt_dyadicGamma_neg_nat`; integer order statements assume a negative center, natural wrappers assume a nonzero index, and negative meromorphic order is Mathlib's encoding of a pole |
| Elementary evaluations, weighted Pascal, and elementary--complete orthogonality | `FabiusFunction.SymmetricFunctionOrthogonality` | Exhaustive public surface: `elementarySymmetricEval`, `elementarySymmetricEval_eq_eval_esymm`, `elementarySymmetricEval_zero`, `elementarySymmetricEval_comp_equiv`, `elementarySymmetricEval_option_succ`, `elementarySymmetricEval_fin_succ`, `sum_elementarySymmetricEval_mul_completeHomogeneousEval`.  The definition, Mathlib identification, zero-degree law, reindexing law, and both adjoining-variable recurrences hold over every commutative semiring.  Together with the existing `completeHomogeneousEval_option_succ`, the option recurrence is the exact weighted-Pascal pair.  The final alternating elementary--complete convolution is the Kronecker delta over every commutative ring, for every degree and every finite family, including degree zero and the empty family; no division, characteristic, domain, or nonvanishing assumption is used. |
| Generic finite lower-triangular transforms | `FabiusFunction.FiniteTriangularTransform` | Exhaustive public surface (one definition and one theorem): `lowerTriangularTransform`, `lowerTriangularTransform_comp`.  Over `[Semiring R] [AddCommMonoid M] [Module R M]`, with no commutativity assumption on `R`, a kernel acts by the finite interval sum over `Icc 0 n`; a total ordered-convolution identity on every pair `n,j` gives equality of the composite transform with the original sequence as functions.  When `n < j` the required interval is empty.  This is the generic finite engine reused by both q-binomial and symmetric-function inversion; it uses no subtraction, topology, or infinite sum. |
| Weighted elementary--complete transforms and inversion | `FabiusFunction.SymmetricFunctionTransform` | Exhaustive public surface (four definitions and five theorems): `completeHomogeneousKernel`, `signedElementaryKernel`, `completeHomogeneousKernel_left_orthogonality`, `completeHomogeneousKernel_right_orthogonality`, `completeHomogeneousTransform`, `signedElementaryTransform`, `signedElementaryTransform_completeHomogeneousTransform`, `completeHomogeneousTransform_signedElementaryTransform`, `weightedSymmetricFunction_inversion`.  The complete kernel and transform are defined over a commutative semiring; the signed kernel, both total-`Icc` convolution identities, both whole-sequence inverse equalities, and the inversion iff use `[CommRing R] [AddCommMonoid M] [Module R M]` and an arbitrary finite weight family.  Both kernels are zero-extended above the diagonal and the compositions reuse the generic finite triangular theorem.  The sums are finite, so no division, nonvanishing, characteristic, domain, topology, or convergence hypothesis is present. |
| Formal generating series for finite symmetric alphabets and the reciprocal finite q-binomial theorem | `FabiusFunction.SymmetricFunctionGenerating` | Exhaustive public surface (two definitions and six theorems): `elementarySymmetricGeneratingSeries`, `completeHomogeneousGeneratingSeries`, `coeff_elementarySymmetricGeneratingSeries`, `coeff_completeHomogeneousGeneratingSeries`, `elementarySymmetricGeneratingSeries_eq_prod`, `elementarySymmetricGeneratingSeries_neg_mul_completeHomogeneousGeneratingSeries`, `completeHomogeneousGeneratingSeries_eq_invOfUnit_elementarySymmetricGeneratingSeries_neg`, `prod_one_sub_qPow_X_mul_gaussianBinomialGeneratingSeries`.  Both definitions, both coefficient results, and the elementary-product theorem hold over every commutative semiring; reciprocity, the canonical `PowerSeries.invOfUnit` identification, and the geometric-alphabet Gaussian reciprocal identity hold over every commutative ring, including the empty alphabet, `n = 0`, singular values of `q`, positive characteristic, and zero divisors.  These are formal-power-series identities only: no analytic evaluation, radius of convergence, or complex convergence claim is made. |
| Every residual moment of finite interpolation and geometric Richardson rows | `FabiusFunction.LagrangeResidualMoments`, `FabiusFunction.GeometricResidualMoments` | `sum_weight_mul_pow_card_add`, `sum_lagrangeEvalWeight_mul_pow_card_add`, `sum_lagrangeEvalWeight_mul_pow_card_add_zero`, `sum_weight_mul_geometric_pow_succ_add`, `sum_weight_mul_geometric_pow_of_pos`, `sum_weight_mul_scaled_geometric_pow_succ_add`, `sum_weight_mul_scaled_geometric_pow_of_pos`, `sum_geometricLagrangeWeight_mul_pow_succ_add`, `sum_geometricLagrangeWeight_mul_pow_of_pos`, `sum_geometricLagrangeWeight_mul_scaled_geometric_pow_of_pos`, `sum_geometricLagrangeWeight_mul_shifted_pow_of_pos`.  The new zero-target theorem assumes a nonempty distinct field-valued node family, exactly excluding the exceptional `0^0` empty-row case, and gives the negative signed nodal product times the complete homogeneous function. |
| Arbitrary finite-node and geometric formal-power-series filters | `FabiusFunction.FinitePowerSeriesFilter`, `FabiusFunction.GeometricPowerSeriesFilter` | `finitePowerSeriesFilter`, `coeff_finitePowerSeriesFilter`, `finitePowerSeriesFilter_rescale`, `map_finitePowerSeriesFilter`, `coeff_finitePowerSeriesFilter_of_exact_of_le`, `geometricSeriesFilter`, `coeff_geometricSeriesFilter_of_exact`, `geometricSeriesFilter_eq_residual_mk`, `geometricLagrangeSeriesFilter_eq_residual_mk`; these are coefficientwise algebraic identities and assert no analytic convergence or remainder estimate |
| Unconditionally summable finite-node and geometric analytic-series filters | `FabiusFunction.AnalyticSeriesFilter` | `finiteAnalyticSeriesFilter`, `summable_finiteAnalyticSeriesFilter_diagonal`, `finiteAnalyticSeriesFilter_eq_tsum`, `finiteAnalyticSeriesFilter_eq_head_add_tail_of_exact`, `finiteAnalyticSeriesFilter_eq_constant_add_tail_of_exact_zero`, `geometricAnalyticSeriesFilter`, `geometricAnalyticSeriesFilter_eq_constant_add_gaussian_tsum`, `geometricLagrangeAnalyticSeriesFilter_eq_constant_add_gaussian_tsum`, `geometricLagrangeAnalyticSeriesFilter_shifted`; the arbitrary finite filter works over a commutative semiring acting on a normed additive group and splits into an exact finite head plus an exact infinite tail under unconditional summability of the weighted sampled series, so a zero-weight node imposes no convergence condition; the geometric and Lagrange wrappers require summability only at nonzero-weight nodes and give the exact denominator-free Gaussian `tsum` tail; conditionally-only convergent boundary series, a formal-power-series evaluation bridge, a sinc-product instantiation, radius-of-convergence or uniform-convergence theorems, norm/sign/error bounds, asymptotic acceleration, positivity, and Fabius-specific acceleration are not asserted |
| Named even Fourier-moment modes and their genuine series sum | `FabiusFunction.AnalyticMoments` | Exhaustive new surface: `rvachevFourierMomentTerm`, `rvachevFourierMomentTerm_zero`, `rvachevFourierMomentTerm_scale`, `hasSum_rvachevFourierMomentTerm`; for every bounded Fabius solution and every complex frequency, the named even modes have constant term one, scale diagonally by `(c^2)^n`, and `HasSum` to the actual Rvachev Fourier transform |
| Exact Gaussian `q`-filter of the Rvachev sinc product | `FabiusFunction.RvachevQBinomialFilter` | Exhaustive public surface: `hasSum_rvachevFourierMomentTerm_product`, `rvachevFourierMomentTerm_pow_scale`, `geometricLagrange_rvachevFourierProduct_eq_gaussian_tsum`, `quarterLagrange_rvachevFourierProduct_eq_gaussian_tsum`, `geometricLagrange_rvachevFourier_eq_gaussian_tsum`.  The generic entire identity takes arbitrary `c,z : ℂ` and `p : ℕ`, uses Gaussian base `q = c^2`, and assumes only `Set.InjOn (fun j ↦ (c^2)^j) (Finset.range (p+1))`; it needs no contraction, realness, positivity, or global nonvanishing hypothesis.  The quarter specialization `c = 1/2`, `q = 1/4` is assumption-free, and the final theorem holds for every bounded `F` satisfying `IsFabius`.  This closes the infinite-product coefficient bridge, not the frontier report's finite prefixes `P_(b,n)`, quotient or Bell-coefficient formulas, conditionally convergent boundary cases, analytic error signs or bounds, uniform convergence, derivative estimates, or asymptotics. |
| Denominator-free finite `q`-binomial algebra | `FabiusFunction.FiniteQBinomialCore` | `map_gaussianBinomial`, `gaussianBinomial_succ_succ`, `gaussianBinomial_succ_succ_alt`, `gaussianBinomial_symm`, `finiteQPochhammerIn_add`, `finiteQPochhammerIn_self_add`, `finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial`, `finite_qBinomial_theorem`; the reusable signed-index extension is `gaussianBinomialInt`, with `gaussianBinomialInt_ofNat`, `gaussianBinomialInt_eq_zero_of_neg`, `gaussianBinomialInt_eq_zero_of_lt`, and total row reflection `gaussianBinomialInt_symm`.  All identities avoid quotient and cancellation hypotheses. |
| Elementary finite `q`-Pochhammer reversal, termination, and adjacent Gaussian ratios | `FabiusFunction.QPochhammerElementaryIdentities` | Exhaustive public surface (13 theorems): `finiteQPochhammerIn_base_reversal_units`, `finiteQPochhammerIn_inv_base_reversal_units`, `finiteQPochhammerIn_base_reversal`, `finiteQPochhammerIn_inv_base_reversal`, `prod_pow_sub_pow_eq_finiteQPochhammerIn`, `pow_mul_finiteQPochhammerIn_inv_pow_eq`, `finiteQPochhammerIn_inv_pow_eq_self_div`, `finiteQPochhammerIn_inv_pow_eq_zero_of_lt`, `one_sub_mul_gaussianBinomial_one`, `gaussianBinomial_adjacent_mul`, `gaussianBinomial_row_adjacent_mul`, `gaussianBinomial_adjacent_div`, `gaussianBinomial_row_adjacent_div`.  The two unit reversals hold in every commutative ring.  The root-safe terminating numerator, first-column clearer, and both adjacent cross-multiplied identities also hold over every commutative ring, including roots of unity; the two cross identities are total in all `n,k`, with zero extension making both sides vanish on and above the row boundary.  The field reversal wrappers require exactly `a != 0` and `q != 0`; the cleared terminating formula and the `k > N` zero theorem require `q != 0`, while its displayed quotient additionally requires `(q;q)_(N-k) != 0`.  The two adjacent quotient theorems remain restricted to `k < n` and require exactly their displayed Gaussian and linear-factor denominators to be nonzero; they do not require `q != 0`. |
| Finite q-Cauchy convolutions and the q-Bernstein partition of unity | `FabiusFunction.QBinomialCauchy` | Exhaustive public surface: `finite_qCauchy_identity`, its compatibility spelling `finiteQPochhammerIn_mul_eq_sum_gaussianBinomial`, `finite_qCauchy_identity_reflected`, `qBernsteinBasis`, `sum_qBernsteinBasis`, and `finite_qCauchy_second_identity` (one definition and five theorems).  The primary identity is `(uv;q)_n = sum_(k=0)^n [n choose k]_q (u;q)_k v^k (v;q)_(n-k)`; its reflected strengthening uses `(v;q)_k v^(n-k) (u;q)_(n-k)`.  The specialization `u = 0` makes the denominator-free q-Bernstein row sum to one, and the second identity evaluates the two-product Cauchy convolution.  All parameters and degrees are arbitrary in every commutative ring, including `n = 0`, `q = 0`, roots of unity, positive characteristic, and zero divisors; no quotient, cancellation, or nonvanishing hypothesis is present. |
| Bit-position and weighted-subset forms of Gauss's finite theorem | `FabiusFunction.BitPositionQBinomial` | Exhaustive public surface: `prod_one_add_mul_pow_eq_gaussianBinomial`, `prod_one_add_pow_eq_sum_gaussianBinomial`, `sum_powersetCard_two_pow`, `sum_pow_bitPositionSum_filter_eq_gaussianBinomial`, `sum_pow_bitPositionSum_filter_eq_gaussianBinomial'`, `sum_pow_sum_powersetCard_eq_gaussianBinomial`, `sum_pow_sum_powersetCard_Icc_eq_gaussianBinomial`, `gaussianBinomial_one_eq_choose`.  The last two subset identities give respectively the zero-based `range N` weight `q^(choose r 2)` and the literal one-based interval `Icc 1 N` weight `q^(choose (r+1) 2)`; they are total in `N,r` over every commutative ring. |
| Division-free Gaussian chains, alternating rows, and mutually inverse scalar kernels | `FabiusFunction.QBinomialInversion` | Exhaustive public surface: `gaussianBinomial_mul`, `sum_gaussianBinomial_alternating_mul_pow`, `sum_gaussianBinomial_alternating`, `gaussianBinomialKernel`, `gaussianBinomialInverseKernel`, `scaledGaussianBinomialKernel`, `scaledGaussianBinomialInverseKernel`, `gaussianBinomialKernel_left_orthogonality`, `gaussianBinomialKernel_right_orthogonality`, `scaledGaussianBinomialKernel_left_orthogonality`, `scaledGaussianBinomialKernel_right_orthogonality`.  The chain identity holds over every commutative semiring; the alternating sums and all four total-`Icc` orthogonality theorems hold over every commutative ring.  The scale `s` is independent of the Gaussian base and is arbitrary: neither it nor `q` is assumed nonzero or invertible. |
| Scaled and classical `q`-binomial transforms of module-valued sequences | `FabiusFunction.QBinomialTransform` | Exhaustive public surface (four definitions and four theorems): `scaledGaussianBinomialTransform`, `scaledGaussianBinomialInverseTransform`, `scaledGaussianBinomialInverseTransform_transform`, `scaledGaussianBinomialTransform_inverseTransform`, `scaledGaussianBinomial_inversion`, `gaussianBinomialTransform`, `gaussianBinomialInverseTransform`, `gaussianBinomial_inversion`.  The forward definitions need only `[Semiring R] [AddCommMonoid M] [Module R M]`, and the inverse definitions need only `[Ring R] [AddCommMonoid M] [Module R M]`.  For `[CommRing R] [AddCommMonoid M] [Module R M]`, both composition theorems are equalities of whole sequence functions and the two triangular relations are equivalent as whole-sequence equalities.  The proofs reuse `lowerTriangularTransform_comp`; the Gaussian coefficient zero-extends each scalar kernel above its row.  These finite algebraic maps require no topology, convergence, division, or invertibility; the unscaled theorem is classical `q`-binomial inversion. |
| Scaled Gaussian characteristic polynomials and exact `q`-difference annihilation | `FabiusFunction.QDifferenceAnnihilation` | Exhaustive public surface (four theorems): `sum_scaledGaussianBinomialInverseKernel_mul_pow`, `sum_gaussianBinomialInverseKernel_mul_geometric_pow`, `qDifference_sum_eval₂_eq_map_coeff_mul`, `qDifference_sum_eval₂_eq_zero_of_degree_lt`.  Over every commutative ring, `sum_(k=0)^n (-s)^(n-k) q^(choose (n-k) 2) [n choose k]_q z^k = prod_(j<n) (z-s q^j)`.  At `s = 1` and `z = q^d`, this gives every monomial moment `prod_(j<n) (q^d-q^j)`, hence zero for `d < n`.  More strongly, after any scalar extension `φ : A →+* R` from a semiring, the row applied to a polynomial of degree at most `n` is `φ(p.coeff n) * prod_(j<n) (q^n-q^j)`, and it annihilates every polynomial of degree strictly below `n`.  The statements include `n = 0` and the zero polynomial; nodes may collide and the surviving product may vanish.  No division, node distinctness, nonzero/invertible base, domain, characteristic, topology, or convergence hypothesis is used. |
| Exact q-Gaussian inversion specializations | `FabiusFunction.QBinomialInversionSpecializations` | Exhaustive public surface (two definitions and four theorems): `qGaussianResidualCoeff`, `qGaussianReconstructionCoeff`, `qGaussianResidualCoeff_eq`, `qGaussianReconstructionCoeff_eq`, `qGaussianReconstructionCoeff_residualCoeff_delta`, `qGaussianResidualCoeff_reconstructionCoeff_delta`.  The two definitions and their pointwise closed-form theorems require only `[Ring R]`, allowing a noncommutative coefficient ring.  At Gaussian base `q^2` and scale `-q`, the residual coefficient is `(-q)^(n-k) [n choose k]_(q^2)` and its reconstruction coefficient is `q^((n-k)^2) [n choose k]_(q^2)`.  Exactly the two total-`Icc` convolution-delta theorems require `[CommRing R]`. |
| Denominator-free `q`-Vandermonde and central convolutions | `FabiusFunction.QBinomialVandermonde` | Exhaustive public surface: `gaussianBinomial_add_vandermonde`, `gaussianBinomial_add_vandermonde'`, `gaussianBinomial_add_central`, `gaussianBinomial_add_central_min`, `gaussianBinomial_two_mul_add_shifted_central`, `gaussianBinomial_two_mul_sub_shifted_central`, `gaussianBinomial_two_mul_sub_shifted_central_Icc`, `gaussianBinomial_two_mul_int_shifted_central`, `gaussianBinomial_two_mul_int_shifted_central_finsum`.  All nine hold over an arbitrary commutative semiring without division, cancellation, or a restriction on `q`; the first seven are the natural-index forms, while the last two prove the report's single formula for every `k : ℤ`, first on the finite natural range `0,…,N` and then literally as a finite-support sum over `ℤ`. |
| Geometric Richardson filters, Gaussian coefficients, all residual moments, and finite conditioning | `FabiusFunction.GeometricQBinomialLagrange`, `FabiusFunction.GeometricRichardson`, `FabiusFunction.GeometricLagrangeWeights`, `FabiusFunction.GeometricLagrangeQBinomial`, `FabiusFunction.GeometricLagrangeQMoments` | `geometricQBinomialWeightNumerator_eq_scaledGaussianBinomialInverseKernel`, `reversed_finite_qBinomial_theorem`, `sum_geometricLagrangeWeight_mul_pow_eq_gaussianBinomial`, `geometricLagrangeWeightPolynomial_eq_forwardGeometricRichardsonPolynomial`, `geometricLagrangeQMoment_eq_residual_qBinomial`, `sum_abs_geometricLagrangeWeight_eq_prod`.  The first theorem, now owned by `GeometricQBinomialLagrange`, globally identifies the denominator-free geometric numerator with the inverse kernel at base and scale `q`, including indices above the diagonal and without `k ≤ n`; it is the `s = q` specialization of the scaled characteristic polynomial.  This does not weaken the separate `Field`/finite-node-`InjOn`/in-range assumptions of normalized quotient formulas.  The remaining rational closed forms use their stated nonzero-base and nonvanishing finite-denominator hypotheses, while sign and variation assume `0 < q < 1`. |
| Quotient-defined rational geometric moments and exact finite conditioning | `FabiusFunction.GeometricLagrangeQMoments` | Exhaustive public surface (one definition and 37 theorems): `geometricLagrangeQMoment`; `geometricLagrangeQMoment_eq_weightPolynomial_eval`, `geometricLagrangeQMoment_eq_forwardRichardson_eval`, `geometricRootPolynomial_inv_eval_pow_mul_signedPowers`, `geometricRootPolynomial_inv_eval_pow_mul_triangular`, `geometricRootPolynomial_inv_eval_one_mul_triangular`, `geometricLagrangeQMoment_eq_qPochhammer`, `geometricLagrangeQMoment_zero`, `geometricLagrangeQMoment_eq_zero`, `geometricRootPolynomial_inv_eval_pow_eq_qPochhammer_of_le`, `geometricLagrangeQMoment_eq_residual_qPochhammer`, `qPochhammer_self_add`, `qPochhammer_self_pos_of_pos_of_lt_one`, `qBinomial_pos_of_pos_of_lt_one`, `gaussianBinomial_eq_qBinomial_of_pos_of_lt_one`, `qPochhammer_pow_pos_of_pos_of_lt_one`, `qPochhammer_tail_div_self_eq_qBinomial`, `geometricLagrangeQMoment_eq_residual_qBinomial`, `geometricLagrangeQMoment_firstUncancelled`, `negOnePow_mul_geometricLagrangeQMoment_eq_positiveResidual`, `negOnePow_mul_geometricLagrangeQMoment_pos`, `qPochhammer_self_succ`, `qBinomial_succ_succ_of_pos_of_lt_one'`, `qBinomial_succ_succ_of_pos_of_lt_one`, `qBinomial_theorem_of_pos_of_lt_one`, `sum_qBinomial_triangular_succ_eq_neg_qPochhammer`, `abs_geometricLagrangeWeight_eq_qBinomial`, `abs_geometricLagrangeWeight_eq_sign_mul`, `abs_geometricLagrangeWeight_complement_eq_qBinomial`, `sum_abs_geometricLagrangeWeight_eq_qPochhammer_ratio`, `neg_qPochhammer_div_self_eq_prod`, `sum_abs_geometricLagrangeWeight_eq_prod`, `quarterGeometricLagrangeQMoment_eq_qPochhammer`, `quarterGeometricLagrangeQMoment_eq_zero`, `quarterGeometricLagrangeQMoment_eq_residual_qPochhammer`, `quarterGeometricLagrangeQMoment_eq_residual_qBinomial`, `quarterGeometricLagrangeQMoment_firstUncancelled`, and `sum_abs_quarterGeometricLagrangeWeight_eq_qPochhammer_ratio`.  These are finite rational identities.  The quotient and injectivity forms retain their explicit nonzero-denominator hypotheses; positivity, sign, and absolute-value formulas retain `0 < q < 1`; no analytic convergence or error estimate is asserted. |
| Report-facing geometric complete-homogeneous bridges | `FabiusFunction.GeometricLagrangeCompleteHomogeneous` | Exhaustive five-theorem surface: `completeHomogeneousEvalOn_geometric_range`, `sum_geometricLagrangeWeight_mul_pow_succ_add_eq_gaussianBinomial`, `geometricLagrangeQMoment_eq_residual_gaussianBinomial`, `completeHomogeneousEvalOn_geometric_range_eq_qBinomial`, and `geometricLagrangeQMoment_eq_residual_qBinomial_via_completeHomogeneous`.  The semiring principal-specialization alias is denominator-free; the field residual uses finite-node injectivity; the rational quotient bridges retain their stated nonzero-Pochhammer or `0 < q < 1` hypotheses. |
| Exact finite polynomial filters | `FabiusFunction.FinitePolynomialFilterExactness` | Exhaustive five-theorem surface: `polynomialFilter_response_eq`, `polynomialFilter_exact`, `normalizedGeometricRootPolynomial_filter_exact`, `forwardGeometricRichardsonPolynomial_filter_exact`, and `forwardGeometricRichardsonPolynomial_filter_firstUncancelled`.  The first two are arbitrary commutative-semiring response and mass-one/root-cancellation laws.  The geometric field specializations preserve the baseline, cancel the prescribed inverse or forward modes, and evaluate the first surviving forward mode as `(-1)^n q^(choose (n+1) 2)` under their explicit nonzero-base and normalization-denominator hypotheses. |
| Formal geometric Richardson filters and the quarter Catalan--Gaussian specialization | `FabiusFunction.QuarterCatalanRichardson` | Exhaustive public surface (three definitions and 15 theorems): `finiteRescaleFilter`, `geometricRichardsonPowerSeriesFilter`, `quarterCatalanRichardsonFilter`; `finiteRescaleFilter_coeff`, `geometricRichardsonPowerSeriesFilter_coeff`, `geometricRichardsonPowerSeriesFilter_coeff_zero`, `geometricRichardsonPowerSeriesFilter_coeff_eq_zero`, `geometricRichardsonPowerSeriesFilter_coeff_eq_qPochhammer`, `geometricRichardsonPowerSeriesFilter_coeff_eq_qBinomial`, `geometricRichardsonPowerSeriesFilter_firstUncancelled_coeff_of_nonzero`, `geometricRichardsonPowerSeriesFilter_firstUncancelled_coeff`, `quarterCatalanRichardsonFilter_coeff`, `quarterCatalanRichardsonFilter_coeff_zero`, `quarterCatalanRichardsonFilter_coeff_eq_zero`, `quarterCatalanRichardsonFilter_coeff_eq_zero_of_le`, `quarterCatalanRichardsonFilter_coeff_eq_qBinomial`, `quarterCatalanRichardsonFilter_coeff_succ_eq_qBinomial`, and `quarterCatalanRichardsonFilter_firstUncancelled_coeff`.  These are coefficientwise formal-power-series identities: the generic row diagonalizes rescaling, preserves degree zero, cancels degrees `1,…,p`, and exposes every residual and the first survivor; the quarter specialization multiplies those factors by the exact Catalan coefficients.  No convergence, real-function error sign, remainder bound, or analytic acceleration is asserted. |
| Exact lower-Lambert phase locking, reciprocal-grid Richardson moments, complete-homogeneous pullback, fixed-order growing-row bounds, and analytic extraction of the periodic Fabius endpoint term | `FabiusFunction.LambertPhaseLockedRichardson`, `FabiusFunction.LambertReciprocalAsymptotics`, `FabiusFunction.FabiusLambertPhaseLockedPullback`, `FabiusFunction.FabiusLambertPhaseExtraction` | `fabiusLambertPhase_phaseLockedNode`, `Periodic.apply_fabiusLambertPhase_phaseLockedNode`, `shiftedReciprocalLagrangeWeight_eq_choose`, `sum_shiftedReciprocalLagrangeWeight_mul_periodicPhaseLocked`, `sum_shiftedReciprocalLagrangeWeight_mul_invPow_card_add`, `sum_shiftedReciprocalLagrangeWeight_mul_invPow_eq_completeHomogeneous`, `sum_shiftedReciprocalLagrangeWeight_residual`, `shiftedReciprocalLagrangeWeight_mul_invPow_isBigO_atTop`, `tendsto_lambertPhaseLockedNode_smallArgument`, `log_fabius_phaseLockedNode_sub_WikipediaLambertExpansion_isBigO`, `fabiusPhaseLockedPeriodicEstimator_sub_residual_isBigO`, `fabiusPhaseLockedPeriodicEstimator_sub_firstOmitted_isBigO`, `fabiusPhaseLockedPeriodicEstimator_tendsto_periodicAlong`; for every fixed row order `r` and residual depth `S`, subtracting the first `S` exact residual terms leaves `O(lambda⁻¹^(r+1+S))`, and integer phase rays converge to the corresponding value of `negativeLaplacePsi`; no uniformity for growing `r` or `S` is asserted |
| Infinite `q`-Pochhammer symbols and the limiting general-`q` row condition number | `FabiusFunction.LimitConditionNumber` | `qPochhammerInf`, `multipliable_one_sub_mul_pow`, `tendsto_finiteQPochhammerIn`, `qPochhammerInf_self_pos`, `qConditionNumberLimit`, `tendsto_sum_abs_qToeplitzWeight`, `one_div_one_sub_le_qConditionNumberLimit`, `tendsto_qConditionNumberLimit_atTop_at_one_left`, `one_lt_qConditionNumberLimit`, `qConditionNumberLimit_zero`, `thousand_le_qConditionNumberLimit`; for `0 ≤ q < 1` the finite row variation converges to `(-q;q)_∞ / (q;q)_∞`, whose denominator is strictly positive and whose value is at least `1 / (1-q)`; consequently the limit tends to `+∞` as `q → 1⁻`, so no uniform-in-`q` bound exists |
| Closed real Lambert branches, endpoint continuity, and the principal small-argument equivalent | `FabiusFunction.LowerLambertW`, `FabiusFunction.PrincipalLambertW` | The new lower-branch continuity surface is `lowerLambertW_continuousWithinAt_branchPoint`, `lowerLambertW_continuousAt`, `lowerLambertW_continuousOn`, and `lowerLambertW_continuousOn_Ico`: it gives continuity on the full natural domain `[-exp(-1),0)`, including the finite branch point but not zero.  The principal companion exposes `principalLambertArg`, `principalLambertW`, `principalLambertW_mul_exp`, `neg_one_le_principalLambertW`, `principalLambertW_unique`, `principalLambertW_branchPoint`, `principalLambertW_zero`, `principalLambertW_exp_one`, `mul_exp_strictMonoOn`, `principalLambertW_strictMonoOn`, `principalLambertW_nonpos`, `neg_one_lt_principalLambertW`, `principalLambertW_image_Ioi`, `principalLambertW_image_Icc`, `principalLambertW_continuousWithinAt_branchPoint`, `principalLambertW_continuousAt`, `principalLambertW_continuousOn`, `principalLambertW_continuousOn_Ici`, `principalLambertW_hasDerivAt`, `deriv_principalLambertW_pos`, `deriv_principalLambertW_zero`, and `principalLambertW_isEquivalent_zero`.  Thus `W₀` is continuous on `[-exp(-1),∞)`, its derivative claims are only above the branch point, and `W₀(z) ~ z` at zero.  No branch-point Puiseux expansion, second derivative, or curvature theorem is asserted. |
| Two real Lambert inverses of scaled power--exponential saddles, exact root classification, full phase continuity, and small-input asymptotics | `FabiusFunction.PowerExponentialLambert`, `FabiusFunction.PowerExponentialLambertCalculus`, `FabiusFunction.PowerExponentialLambertInverse`, `FabiusFunction.PowerExponentialLambertAsymptotics`, `FabiusFunction.PowerExponentialLambertFabius` | `powerExponentialSaddle`, `powerExponentialPeak`, `powerExponentialLambertArgument`, `principalPowerExponentialPhase`, `lowerPowerExponentialPhase`, the three `powerExponentialLambertArgument_mem_*` domain theorems, both branch solve laws and endpoint values, `principalPowerExponentialPhase_mem_Icc`, `lowerPowerExponentialPhase_mem_Ici`, `powerExponentialLambertArgument_strictAntiOn`, `principalPowerExponentialPhase_strictMonoOn`, `lowerPowerExponentialPhase_strictAntiOn`, both branch `HasDerivAt`/`deriv`/derivative-sign and interior-continuity pairs, `principalPowerExponentialPhase_continuousOn_Icc`, `lowerPowerExponentialPhase_continuousOn_Ioc`, `powerExponentialLambertArgument_image_Icc`, `powerExponentialLambertArgument_image_Ioc`, `principalPowerExponentialPhase_image_Icc`, `lowerPowerExponentialPhase_image_Ioc`, both branch `LeftInvOn`/`RightInvOn`/`InvOn` packages, `powerExponentialSaddle_eq_iff_eq_principal_or_eq_lower`, and `principalPowerExponentialPhase_ne_lowerPowerExponentialPhase`.  All of these generic branch results assume `m ≠ 0`, `A > 0`, and `beta > 0`; the root iff additionally assumes `x ∈ (0,peak]` and `lambda ≥ 0` (the restriction is essential for even `m`), while distinctness holds only for `x ∈ (0,peak)`.  The principal phase is continuous on `[0,peak]`, the lower phase on `(0,peak]`, and derivatives remain restricted to `(0,peak)`.  The small-input surface is `powerExponentialLambertEpsilon`, `powerExponentialLambertArgument_eq_neg_epsilon`, `powerExponentialLambertEpsilon_pos`, `tendsto_powerExponentialLambertEpsilon_nhdsGT_zero`, `principalPowerExponentialPhase_isEquivalent_rpow`, `tendsto_lowerPowerExponentialPhase_nhdsGT_zero_atTop`, `lowerPowerExponentialPhaseIntrinsicMain`, and `lowerPowerExponentialPhase_sub_intrinsicMain_tendsto_zero`: along `x ↓ 0`, the principal root is equivalent to `(x/A)^(1/m)`, while the lower root diverges and has only the proved intrinsic `epsilon`-coordinate two-term remainder.  The bridges are `lowerPowerExponentialPhase_rate_one`, `generalizedLambertCoordinate_argument_mem_Ioo`, `generalizedLambertCoordinate_argument_mem_Ico`, `generalizedLambertCoordinate_solves_saddle_of_mem`, `powerExponentialSaddle_one_one_log_two`, `powerExponentialPeak_one_one_log_two`, `lowerPowerExponentialPhase_one_one_log_two`, `fabiusPrincipalLambertPhase`, `fabiusSaddle_eq_iff_eq_principal_or_eq_lower`, `fabiusPrincipalLambertPhase_ne_fabiusLambertPhase`, `fabiusPrincipalLambertPhase_continuousOn_Icc`, `fabiusLambertPhase_continuousOn_Ioc`, and `fabiusPrincipalLambertPhase_isEquivalent_id`; their root/continuity domains specialize respectively to `(0,exp(-1)/log 2]`, `(0,exp(-1)/log 2)`, `[0,exp(-1)/log 2]`, and `(0,exp(-1)/log 2]`.  No cleaned `L = log(A/x)` form, second-derivative/curvature/Puiseux theory, or generic complete asymptotic series is claimed. |
| Formal power-series logarithms and finite-product additivity | `FabiusFunction.LogSeriesMultiplicative` | `SaddleExpansion.logOf`, `SaddleExpansion.massSeries_coeff`, `SaddleExpansion.constantCoeff_logOf`, `SaddleExpansion.mul_derivative_logOf`, `SaddleExpansion.logOf_eq_of`, `SaddleExpansion.logOf_mul`, `SaddleExpansion.logOf_one`, `SaddleExpansion.logOf_prod` |
| Generic unit-interval Laplace-moment bounds | `FabiusFunction.UnitLaplaceMomentBounds` | `unitLaplaceMoment_midpoint_sq_le_all`, `unitLaplaceMoment_le_of_tilt_sub`, `pow_mul_exp_neg_le_factorial`, `fabiusLaplaceMoment_midpoint_sq_le_all`, `fabiusLaplaceMoment_le_of_tilt_sub` |
| Exact dyadic computation and analytic correctness | `FabiusFunction.DyadicAnalytic`, `FabiusFunction.GlobalDyadic` | `fabiusDyadicValue`, `evalFabiusDyadic`, `fabiusDyadicUnit_cast`, `extendedFabiusDyadicValue_cast` |
| First and second published papers | `FabiusFunction.Paper05442`, `FabiusFunction.Paper06487` | the theorem maps in the module docstrings and [`docs/PAPER_COVERAGE.md`](docs/PAPER_COVERAGE.md) |
| Corrected sharp and all-orders asymptotics | `FabiusFunction.PaperFabiusAsymptotic` | `abs_log_fabius_dyadic_sub_explicitCumulantMain_le`, `log_fabius_sub_sharpLambertMain_hasAsymptoticExpansion`, `fabiusSharpLambertExpansion_two` |
| Complex finite Hamming-weight and Thue--Morse exponential block transforms | `FabiusFunction.ThueMorseComplexExponential` | `sum_range_two_pow_binaryWeight_cexp`, `sum_range_two_pow_binaryWeight_cexp_affine`, `sum_range_two_pow_thueMorseSign_cexp`, `sum_range_two_pow_thueMorseSign_cexp_affine`; the weight, exponent, and affine shift are arbitrary complex parameters, and the empty product at `m = 0` is included; these declarations are the raw finite transforms, while `ThueMorseComplexProductBridge` supplies the total complex sinc and negative-Laplace normalizations |
| Denominator-cleared centered sinc shells and their Thue--Morse zero classification | `FabiusFunction.CenteredRvachevThueMorseFourier` | `centeredSincPartialProduct_dyadic_eq_thueMorse`, `rvachevFourierProduct_dyadic_eq_thueMorse`, `rvachevFourierProduct_dyadic_eq_zero_iff_thueMorse`, `rvachevFourierProduct_dyadic_eq_zero_iff_exists` |
| Finite odd-coset DFT traces and odd-coset-filtered convolution (Ramanujan at power-of-two moduli) | `FabiusFunction.HalfIntegerOddDFT` | `sum_odd_powers_eq_root_filter`, `oddDFT_add_period`, `oddDFTPowerTrace_eq_ramanujanConvolution`, `normalizedOddDFTPowerTrace_eq_two_mul_half` |
| Fourier--Legendre expansions, least squares, coefficient energy, exact rational approximants, Fourier/sinc energy identities, finite translate blocks, and uniformly convergent fixed-scale self-reconstruction | `FabiusFunction.FabiusTranslatedLegendreSeries`, `FabiusFunction.FabiusLegendreLeastSquares`, `FabiusFunction.FabiusLegendreEnergy`, `FabiusFunction.FabiusLegendreRationalEnergy`, `FabiusFunction.FabiusSquareEnergyFourier`, `FabiusFunction.FabiusLegendreTranslateBlocks`, `FabiusFunction.FabiusLegendreTranslateSeries` | `hasSum_canonical_rvachevLegendreSeries_formula`, `rvachevLegendrePartialSum_pythagorean`, `rvachevLegendreBlock`, `intervalIntegral_rvachevLegendreBlock_mul`, `hasSum_rvachevLegendreCoefficient_energy`, `hasSum_rvachevLegendreCoefficient_energy_tail`, `rvachevLegendreSquaredError_partialSum_eq_tsum_tail`, `fabiusSquareEnergy_eq_tsum_legendre`, `canonicalRvachevLegendreCoefficientRat`, `fabiusSquareEnergyPartialSumRat`, `fabiusSquareEnergyPartialSumRat_pos`, `monotone_fabiusSquareEnergyPartialSumRat`, `fabiusSquareEnergyPartialSumRat_three`, `tendsto_fabiusSquareEnergyPartialSumRat_cast`, `integral_norm_sq_rvachevFourier_eq_two_mul_fabiusSquareEnergy`, `fabiusSquareEnergy_eq_integral_Ioi_norm_sq_rvachevFourier`, `fabiusSquareEnergy_eq_integral_Ioi_tprod_sinc_sq`, `fabiusSquareEnergy_eq_scaled_integral_Ioi_tprod_sinc_sq`, `rvachevLegendreDeconvolutionPolynomial`, `natDegree_rvachevLegendreDeconvolutionPolynomial`, `leadingCoeff_rvachevLegendreDeconvolutionPolynomial`, `eval_legendrePolynomial_eq_sum_rvachevUp`, `eval_legendrePolynomial_even_eq_sum_rvachevUp`, `rvachevLegendreScale`, `rvachevLegendreIndexSet`, `rvachevLegendreAtomCoefficient`, `rvachevLegendreTranslateBlock`, `rvachevLegendreTranslateBlock_eq_rvachevLegendreBlock`, `intervalIntegral_rvachevLegendreTranslateBlock_mul`, `rvachevTranslateGram`, `sum_rvachevLegendreAtomCoefficient_mul_gram`, `hasSum_rvachevLegendreTranslateBlock`, `hasSum_rvachevLegendreTranslateBlock_uniform`, `rvachevLegendrePartialSumDeconvolutionPolynomial`, `natDegree_rvachevLegendrePartialSumDeconvolutionPolynomial`, `leadingCoeff_rvachevLegendrePartialSumDeconvolutionPolynomial`, `rvachevLegendrePartialSumTranslateBlock`, `rvachevLegendrePartialSumTranslateBlockOnInterval`, `rvachevLegendrePartialSumTranslateBlockOnInterval_apply`, `rvachevLegendrePartialSumTranslateBlockOnInterval_eq_eval_partialSumPolynomial`, `rvachevLegendrePartialSumTranslateBlockOnInterval_eq_sum`, `tendsto_rvachevLegendrePartialSumTranslateBlockOnInterval`, `rvachevLegendrePartialSumTranslateBlock_tendstoUniformlyOn`, `tendsto_norm_rvachevLegendrePartialSumTranslateBlockOnInterval_sub`, `tendsto_rvachevLegendrePartialSumTranslateBlock`, `eval_rvachevLegendrePartialSumPolynomial_eq_sum_rvachevUp` |
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
specialization proves finite residual moments, not spectral-tail convergence.
The Lambert tranche goes further: it proves fixed-order phase extraction and
weighted residual Big-O estimates, but no uniformity as the row order or
residual depth grows and no Bell/generalized-harmonic closed form for the
complete-homogeneous residual.  The full-order centered parity API is coefficientwise formal
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

`FabiusLegendreEnergy.lean` defines the Legendre blocks
`B_n(x) = u_n * P_(2n)(x)`, proves their complete orthogonality formula, and
closes the coefficient-energy side of this expansion.  In the notation above
it proves

```text
integral (-1..1), B_m(x) * B_n(x) dx
  = if m = n then 2 * u_n^2 / (4n+1) else 0,
integral (-1..1), up(x)^2 dx
  = sum (n = 0..infinity), 2 * u_n^2 / (4n+1),
E(S_N)
  = sum (n = N+1..infinity), 2 * u_n^2 / (4n+1),
A_2 := integral (0..1), F(t)^2 dt
  = sum (n = 0..infinity), u_n^2 / (4n+1).
```

The ten public declarations consist of the two definitions
`Fabius.rvachevLegendreBlock` and `Fabius.fabiusSquareEnergy`, together with
the eight theorems `Fabius.intervalIntegral_rvachevLegendreBlock_mul`,
`Fabius.integral_sq_eval_rvachevLegendrePartialSumPolynomial`,
`Fabius.hasSum_rvachevLegendreCoefficient_energy`,
`Fabius.hasSum_rvachevLegendreCoefficient_energy_tail`,
`Fabius.rvachevLegendreSquaredError_partialSum_eq_tsum_tail`,
`Fabius.integral_sq_rvachevUp_eq_two_mul_fabiusSquareEnergy`,
`Fabius.hasSum_fabiusSquareEnergy_legendre`, and
`Fabius.fabiusSquareEnergy_eq_tsum_legendre`.  The block is defined directly
in its polynomial form.

At compiled source checkpoint `9d5f41c2c`,
`FabiusLegendreRationalEnergy.lean` adds three executable rational definitions:
`Fabius.canonicalRvachevLegendreCoefficientRat`,
`Fabius.fabiusSquareEnergyTermRat`, and
`Fabius.fabiusSquareEnergyPartialSumRat`.  Its fifteen theorems are
`Fabius.canonicalRvachevLegendreCoefficientRat_cast`,
`Fabius.canonicalRvachevLegendreCoefficientRat_zero`,
`Fabius.fabiusSquareEnergyTermRat_cast`,
`Fabius.fabiusSquareEnergyTermRat_nonneg`,
`Fabius.fabiusSquareEnergyTermRat_zero`,
`Fabius.fabiusSquareEnergyPartialSumRat_cast`,
`Fabius.monotone_fabiusSquareEnergyPartialSumRat`,
`Fabius.fabiusSquareEnergyPartialSumRat_pos`,
`Fabius.fabiusSquareEnergyPartialSumRat_zero`,
`Fabius.fabiusSquareEnergyPartialSumRat_one`,
`Fabius.fabiusSquareEnergyPartialSumRat_two`,
`Fabius.fabiusSquareEnergyPartialSumRat_three`,
`Fabius.hasSum_fabiusSquareEnergy_ratCast`,
`Fabius.fabiusSquareEnergy_eq_tsum_ratCast`, and
`Fabius.tendsto_fabiusSquareEnergyPartialSumRat_cast`.  Thus every Legendre
energy partial sum is represented by a positive rational number, the rational
partial sums are monotone, and their real casts converge to `A_2`.  The four
displayed values are certified exactly:
`1/4`, `7/18`, `3271/8100`, and `3246043/8037225` for cutoffs
`N = 0, 1, 2, 3`, respectively.

At compiled source checkpoint `b9b240bc0`,
`FabiusSquareEnergyFourier.lean` exports no definitions and exactly four
theorems:
`Fabius.integral_norm_sq_rvachevFourier_eq_two_mul_fabiusSquareEnergy`,
`Fabius.fabiusSquareEnergy_eq_integral_Ioi_norm_sq_rvachevFourier`,
`Fabius.fabiusSquareEnergy_eq_integral_Ioi_tprod_sinc_sq`, and
`Fabius.fabiusSquareEnergy_eq_scaled_integral_Ioi_tprod_sinc_sq`.  They
identify the full real-axis squared Fourier mass with twice `A_2`, the
positive-half-line mass with `A_2`, and the latter with both the unscaled and
`1/(2*pi)`-scaled dyadic sinc-product integrals in the Self-Reconstruction
report.

At compiled source checkpoint `a3854643d`,
`RvachevMomentAppell.lean` exports six public definitions:
`Fabius.rvachevRawMomentRat`, `Fabius.rvachevReciprocalMomentRat`,
`Fabius.rvachevAppellPolynomialRat`, `Fabius.rvachevAppellPolynomial`, and
`Fabius.rvachevDeconvolvedPolynomial`, together with the linear-map package
`Fabius.rvachevDeconvolutionLinearMap`.  Its thirty public theorems are
`Fabius.rvachevRawMomentRat_zero`, `Fabius.rvachevRawMomentRat_even`,
`Fabius.rvachevRawMomentRat_odd`,
`Fabius.rvachevReciprocalMomentRat_zero`,
`Fabius.binomialConv_rvachevRawMomentRat_reciprocal`,
`Fabius.rvachevReciprocalMomentRat_eq_completeBellPolynomial`,
`Fabius.monic_rvachevAppellPolynomialRat`,
`Fabius.natDegree_rvachevAppellPolynomialRat`,
`Fabius.rvachevAppellPolynomial_eq_poly_cast`,
`Fabius.monic_rvachevAppellPolynomial`,
`Fabius.natDegree_rvachevAppellPolynomial`,
`Fabius.eval_rvachevAppellPolynomial_add`,
`Fabius.integral_pow_mul_rvachev_eq_rvachevRawMomentRat_cast`,
`Fabius.integral_eval_rvachevAppellPolynomial_add_mul_rvachev`,
`Fabius.rvachevDeconvolutionLinearMap_apply`,
`Fabius.rvachevDeconvolvedPolynomial_zero`,
`Fabius.rvachevDeconvolvedPolynomial_add`,
`Fabius.rvachevDeconvolvedPolynomial_smul`,
`Fabius.rvachevDeconvolvedPolynomial_finsetSum`,
`Fabius.rvachevDeconvolvedPolynomial_C_mul`,
`Fabius.rvachevDeconvolvedPolynomial_monomial`,
`Fabius.rvachevDeconvolvedPolynomial_X_pow`,
`Fabius.coeff_rvachevDeconvolvedPolynomial_natDegree`,
`Fabius.natDegree_rvachevDeconvolvedPolynomial_le`,
`Fabius.natDegree_rvachevDeconvolvedPolynomial`,
`Fabius.leadingCoeff_rvachevDeconvolvedPolynomial`,
`Fabius.rvachevDeconvolvedPolynomial_eq_zero_iff`,
`Fabius.rvachevDeconvolutionLinearMap_injective`,
`Fabius.rvachevDeconvolvedPolynomial_injective`, and
`Fabius.integral_eval_rvachevDeconvolvedPolynomial_add_mul_rvachev`.  They
package the full rational raw-moment sequence, its formal binomial-convolution
reciprocal and complete-Bell description, rational and real monic Appell
families of exact degree, and polynomial deconvolution as an explicit real
linear map.  In particular deconvolution preserves zero, addition, scalar
multiplication, finite sums, and multiplication by constant polynomials; it
sends a monomial and `X^n` to the correspondingly scaled and unscaled
Rvachev--Appell polynomial.  Its triangular top term is unchanged: it
preserves the coefficient in the original `natDegree`, hence preserves exact
`natDegree` and `leadingCoeff`, has trivial kernel, and is injective both as
the packaged linear map and as the underlying raw operation.  Smoothing it by
`up` recovers the original polynomial.

At compiled source checkpoint `c51a41fcf`,
`RvachevPolynomialSynthesis.lean` exports no public definitions and exactly
four public theorems:
`Fabius.tsum_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`,
`Fabius.normalized_tsum_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`,
`Fabius.sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`, and
`Fabius.normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`.
For every nonzero natural mesh `M` and polynomial of degree at most `v₂(M)`,
they give both global `tsum` synthesis and, on `[-1,1]`, its exact finite
`k ∈ (-2M,2M)` form with the `1/M` normalization.

The focused-build `CompositeMeshSharpness.lean` module exports one public
definition and seven public theorems.  The definition
`Fabius.rvachevCombExactThrough F M d` requires `M ≠ 0` and shifted-comb
exactness at every real shift for every real polynomial of natural degree at
most `d`.  Its two classification theorems prove that this is equivalent to
`M ≠ 0 ∧ d ≤ v₂(M)`, equivalently `M ≠ 0 ∧ 2^d ∣ M`.  The
remaining order theorems put the canonical mesh `2^d` in this class, bound
every member below by `2^d`, prove that it is the least member, and specialize
the least mesh for the complete degree-`2N` space to `4^N`.  The real
first-defect theorem supplies a shift where the monomial of degree
`v₂(M)+1` fails.  These are universal polynomial-space statements: they do
not prove that `2^d` is minimal for one Legendre polynomial or that `4^N` is
minimal for one particular partial sum `S_N`.

At compiled source checkpoint `a3854643d`,
`FabiusLegendreTranslateBlocks.lean` exports six
public definitions: `Fabius.rvachevLegendreDeconvolutionPolynomial`,
`Fabius.rvachevLegendreScale`, `Fabius.rvachevLegendreIndexSet`,
`Fabius.rvachevLegendreAtomCoefficient`,
`Fabius.rvachevLegendreTranslateBlock`, and `Fabius.rvachevTranslateGram`.
Its seven public theorems are
`Fabius.natDegree_rvachevLegendreDeconvolutionPolynomial`,
`Fabius.leadingCoeff_rvachevLegendreDeconvolutionPolynomial`,
`Fabius.eval_legendrePolynomial_eq_sum_rvachevUp`,
`Fabius.eval_legendrePolynomial_even_eq_sum_rvachevUp`,
`Fabius.rvachevLegendreTranslateBlock_eq_rvachevLegendreBlock`,
`Fabius.intervalIntegral_rvachevLegendreTranslateBlock_mul`, and
`Fabius.sum_rvachevLegendreAtomCoefficient_mul_gram`.  They specialize the
finite synthesis to mesh `2^d`, then to the even mesh `4^n`.  For
`Q_d = D(P_d)`, they prove exact degree `d` and the explicit unchanged leading
coefficient `(1/2)^d * choose (2*d) d`; they also identify the
literal finite translate block with the existing polynomial block on
`[-1,1]`, and prove both its orthogonality and exact finite atom-Gram formula.

At compiled source checkpoint `a3854643d`, the focused-build module
`FabiusLegendreTranslateSeries.lean` exports five
public definitions: `Fabius.rvachevLegendrePartialSumDeconvolutionPolynomial`,
`Fabius.rvachevLegendrePartialSumAtomCoefficient`,
`Fabius.rvachevLegendrePartialSumTranslateBlock`,
`Fabius.rvachevLegendreTranslateBlockOnInterval`, and
`Fabius.rvachevLegendrePartialSumTranslateBlockOnInterval`.  Its twenty-five
public theorems
are
`Fabius.natDegree_rvachevLegendrePartialSumDeconvolutionPolynomial`,
`Fabius.leadingCoeff_rvachevLegendrePartialSumDeconvolutionPolynomial`,
`Fabius.summable_norm_rvachevLegendreTranslateBlock`,
`Fabius.summable_rvachevLegendreTranslateBlock`,
`Fabius.hasSum_rvachevLegendreTranslateBlock`,
`Fabius.tsum_rvachevLegendreTranslateBlock`,
`Fabius.rvachevLegendrePartialSumDeconvolutionPolynomial_eq_sum`,
`Fabius.rvachevLegendrePartialSumAtomCoefficient_eq_sum`,
`Fabius.eval_rvachevLegendrePartialSumPolynomial_eq_tsum_rvachevUp`,
`Fabius.eval_rvachevLegendrePartialSumPolynomial_eq_sum_rvachevUp`,
`Fabius.rvachevLegendrePartialSumTranslateBlock_eq_eval_partialSumPolynomial`,
`Fabius.rvachevLegendrePartialSumTranslateBlock_eq_sum_translateBlock`,
`Fabius.rvachevLegendreTranslateBlockOnInterval_apply`,
`Fabius.rvachevLegendreTranslateBlockOnInterval_eq_smul`,
`Fabius.summable_norm_rvachevLegendreTranslateBlockOnInterval`,
`Fabius.summable_rvachevLegendreTranslateBlockOnInterval`,
`Fabius.hasSum_rvachevLegendreTranslateBlock_uniform`,
`Fabius.tsum_rvachevLegendreTranslateBlock_uniform`,
`Fabius.rvachevLegendrePartialSumTranslateBlockOnInterval_apply`,
`Fabius.rvachevLegendrePartialSumTranslateBlockOnInterval_eq_eval_partialSumPolynomial`,
`Fabius.rvachevLegendrePartialSumTranslateBlockOnInterval_eq_sum`,
`Fabius.tendsto_rvachevLegendrePartialSumTranslateBlockOnInterval`,
`Fabius.rvachevLegendrePartialSumTranslateBlock_tendstoUniformlyOn`,
`Fabius.tendsto_norm_rvachevLegendrePartialSumTranslateBlockOnInterval_sub`, and
`Fabius.tendsto_rvachevLegendrePartialSumTranslateBlock`.  Thus the literal outer
translate blocks are absolutely summable pointwise and in the interval
supremum norm, have pointwise and uniform `HasSum`/`tsum` forms, and sum to
`rvachevUp`.  The same module identifies the partial-sum deconvolution
polynomial with the finite sum of separately deconvolved modes, expands every
common-mesh coefficient, proves global `tsum` and finite `[-1,1]` synthesis at
mesh `4^N`, and identifies the resulting finite train both with the polynomial
partial sum and with the sum of its separately scaled blocks.  It also proves
that `C_N = D(S_N)` has exactly the `natDegree` and `leadingCoeff` of `S_N`,
including every degenerate case in which the visible degree drops.  The bundled
common-mesh trains converge to `rvachevUp` in `C([-1,1])`, equivalently in the
interval supremum norm; the module also exports the raw `TendstoUniformlyOn`
form, convergence of the supremum-norm error to zero, and the pointwise
corollary on `[-1,1]`.

The five modules in this tranche have respectively `6/30`, `0/4`, `1/7`,
`6/7`, and `5/25` public definition/theorem inventories, for exactly 91 public
declarations in total.  Universal whole-space mesh sharpness is now proved,
but target-specific minimality for an individual Legendre polynomial or
partial sum is not.  The modules also do not assert an
analytic reciprocal-MGF or differential-series realization of deconvolution,
the displayed low reciprocal coefficients, parity or the displayed closed
formulas for the deconvolved Legendre family,
coefficient rationality for the atom rows, equality of the fixed-scale and
separately scaled coefficient vectors, an unconditional
`natDegree(S_N) = 2*N` theorem or nonvanishing of its top Legendre
coefficient, or the later refinement, projector, and asymptotic layers.

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
identity gives the all-real oriented centered-integral formula
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
  [`docs/semi-formalized-research-frontiers/`](docs/semi-formalized-research-frontiers/),
  not in the primary exposition. Frontier documents label conjectures,
  heuristics, partial formalizations, refutations, and the precise outstanding
  Lean obligations rather than presenting them as established results.
- **Treat drafts as a temporary inbox.** Content under
  `docs/semi-formalized-research-frontiers/drafts/incoming/` is reviewed claim-by-claim.
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
