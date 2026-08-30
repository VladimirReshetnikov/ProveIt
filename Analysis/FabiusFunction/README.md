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
| Definitions, the bounded characterization, and folded `up` | `FabiusFunction.Basic`, `FabiusFunction.Differential` | `BoundedFabius`, `IsFabius`, `rvachevUp`, `rvachevUp_even`, `rvachevUp_eq_zero_of_not_mem_Ioo`, `support_rvachev_subset_Ioo`, `rvachev_hasDerivAt` |
| Existence, uniqueness, and the canonical functions | `FabiusFunction.PaperStatements` | `existsUnique_fabius`, `fabius`, `fabius_spec`, `globalFabius` |
| Original compact-support characterization and bounded/original bridge | `FabiusFunction.OriginalUniqueness` | `IsOriginalFabius`, `IsOriginalFabius.mk_of_derivative_law`, `IsFabius.isOriginalFabius_rvachevUp`, `rvachevUp_eq_iff_eqOn_Iic_one`, `isFabius_iff_isOriginalFabius_rvachevUp_and_rightTail`, `isOriginalFabius_iff_existsUnique_isFabius` |
| Generic affine-difference iterates and derivative orbits | `FabiusFunction.AffineDifferenceOrbit` | `affineDifference_iterate_apply`, `iteratedDeriv_eq_affineDifference_iterate_on`, `affineDifference_iterate_two_one_apply`; the module assumes a one-step derivative identity and does not prove the up-law resolvent equation |
| Total complex finite Thue--Morse sinc and negative-Laplace bridges | `FabiusFunction.ThueMorseComplexProductBridge` | `shiftedComplexSincPrefix`, `complexLaplacePrefix`, `sum_thueMorseSign_cexp_eq_sin_prod`, `thueMorseBlock_cexp_eq_sincPrefix`, `thueMorseBlock_cexp_eq_sincPrefix_of_pos`, `thueMorseBlock_exp_neg_eq_laplacePrefix`, `shiftedComplexSincPrefix_eq_thueMorseBlock_cexp_of_pos`, `complexLaplacePrefix_eq_thueMorseBlock_exp_neg`, `complexExpm1Div_neg_eq_exp_mul_complexSinc`, `complexLaplacePrefix_eq_exp_mul_shiftedComplexSincPrefix`, `shiftedComplexSincPrefix_apply_zero`, `complexLaplacePrefix_apply_zero`; the primary equalities and the finite Fourier--Laplace rotation hold at every level and at the removable origin, while the quotient forms assume a nonzero free variable |
| Exact first jets and simple zeros of reciprocal Gamma | `FabiusFunction.ReciprocalGammaJets` | `deriv_Gamma_inv_neg_nat`, `hasDerivAt_Gamma_inv_neg_nat`, `hasDerivAt_Gamma_inv_zero`, `analyticOrderAt_Gamma_inv_neg_nat`, `tendsto_Gamma_inv_div_add_nat`; all five statements hold for every natural zero index, concern the entire reciprocal function, and assign no derivative to raw Gamma at a pole |
| Thue--Morse continuation jets and Gamma tower | `FabiusFunction.ThueMorseGammaTower` | `hasDerivAt_dirichletMellinContinuation_neg_nat`, `deriv_dirichletMellinContinuation_neg_nat`, `thueMorseGammaLog`, `thueMorseGammaTower`, `thueMorseGammaLog_eq_mellin`, `thueMorseGammaLog_eq_integral`, `thueMorseGammaLog_dyadic`, `thueMorseGammaTower_dyadic`, `ofReal_exp_mpLimit_eq_gammaTower_div`; the two definitions are total in `a`, all analytic laws assume `0 < a` (and the ratio bridge also `0 < b`), GammaLog is a chosen coordinate rather than a proved `Complex.log` identity, and only the parameter differential/iterated ladder remains open |
| Generic normalized Volterra calculus over real normed spaces (Banach only for the FTC/Taylor layer) | `FabiusFunction.NormalizedVolterra` | `volterraPrimitive`, `iteratedPrimitive`, `normalizedVolterra`, `normalizedVolterra_affine`, `normalizedVolterra_comp_affine`, `normalizedVolterra_basepoint_shift`, `normalizedVolterra_succ_eq_taylor_of_eq_zero`, `iteratedPrimitive_add`, `iteratedPrimitive_succ_hasStrictDerivAt`, `iteratedPrimitive_eq_normalizedVolterra`, `normalizedVolterra_succ_hasStrictDerivAt`, `iteratedDeriv_normalizedVolterra_add`, `contDiff_normalizedVolterra`, `normalizedVolterra_add`, `normalizedVolterra_succ_iteratedDeriv_eq_sub_taylor`, `intervalIntegrable_normalizedVolterraKernel_add`, `normalizedVolterra_succ_polynomial_of_taylor_support_kernel_intervalIntegrable`, `normalizedVolterra_succ_polynomial_of_kernel_intervalIntegrable`, `normalizedVolterra_polynomial`, `normalizedVolterra_monomial` |
| Positive-real fractional Volterra calculus over real normed spaces | `FabiusFunction.FractionalVolterra`, `FabiusFunction.FractionalVolterraSemigroup` | `fractionalVolterra`, `fractionalVolterra_self`, `fractionalVolterra_congr`, `fractionalVolterra_smul`, `intervalIntegrable_fractionalVolterra_kernel`, `intervalIntegral_eq_integral_min_of_eq_zero`, `fractionalVolterra_eq_intervalIntegral_min_of_eq_zero`, `fractionalVolterra_add_input`, `fractionalVolterra_one`, `fractionalVolterra_nat_succ`, `intervalIntegral_fractionalVolterra_betaKernel`, `intervalIntegrable_fractionalVolterra_betaKernel`, `intervalIntegral_fractionalVolterra_normalizedBetaKernel`, `fractionalVolterra_normalized_rpow_smul`, `fractionalVolterra_rpow_smul`, `fractionalVolterra_const`, `fractionalVolterra_add`; the definition and algebraic endpoint/integer rules use oriented interval integrals, while kernel integrability and input additivity assume `0 < α`, `a ≤ x`, and continuity on `[a,x]`; if `a ≤ b`, `a ≤ x`, and an interval-integrable kernel vanishes on `Ioo b x`, its integral cuts off at `min x b`, and for `0 < α` the same support truncation holds for a continuous fractional input vanishing on that open tail; for `0 < α`, `0 < β`, the raw shifted beta kernel is interval-integrable when `s ≤ x`, and its raw and Gamma-normalized values are evaluated when `s < x`; on a complete target, normalized shifted powers (`α, β > 0`, `a < x`), general shifted powers (`α > 0`, `ρ > -1`, `a < x`), and constants (`α > 0`, `a ≤ x`) have their exact Gamma-quotient values, and `fractionalVolterra_add` proves additive composition of two positive orders when `a ≤ x` and the input is continuous on `[a,x]`; no order-zero law, reversed-endpoint fractional interpretation, semigroup theorem for merely interval-integrable inputs or noncomplete targets, fractional derivative or Caputo theorem, or complex order is claimed |
| Increasing-affine covariance, ordinary-derivative order raising, causal Rvachev fractional primitives, and one-step Fabius--Rvachev shifts | `FabiusFunction.FractionalVolterraCalculus`, `FabiusFunction.FabiusFractionalVolterra` | `fractionalVolterra_affine`, `fractionalVolterra_comp_affine`, `fractionalVolterra_add_one_deriv`, `fractionalVolterra_add_one_deriv_of_eq_zero`, `rvachevFractionalPrimitive`, `rvachevFractionalPrimitive_eq_intervalIntegral_min`, `rvachevFractionalPrimitive_nat_succ`, `rvachevFractionalPrimitive_add`, `fractionalVolterra_add_one_extendedFabius_of_nonneg`, `fractionalVolterra_add_one_fabiusReal`, `fractionalVolterra_add_one_rvachevUp`; affine covariance holds for every real order, positive scale, and ordered endpoints without regularity, integrability, or completeness assumptions; on a complete target, order raising assumes `0 < α`, `a ≤ x`, continuity of the primitive on `[a,x]`, an interval-integrable displayed derivative, and its right derivative on the open interval, records the exact Gamma-normalized left-boundary term, and includes the degenerate interval; `rvachevFractionalPrimitive` is total, its classical support-truncated formula assumes `0 < β` and `-1 ≤ x`, its positive-natural-order bridge is total in the endpoint, and its additive semigroup assumes `α, β > 0` and `-1 ≤ x`; the three shift specializations give `I₀^(α+1) 𝓕(x) = 2^α I₀^α 𝓕(x/2)` for `α > 0`, `x ≥ 0`, its bounded form for `x ∈ [0,1]`, and `I₋₁^(α+1) up(x) = 2^α I₀^α F((x+1)/2)` for `x ≥ -1`; no nonpositive-scale or reversed-endpoint covariance, negative- or complex-order fractional-calculus extension, fractional derivative or Caputo theorem, shifted dyadic-lattice or endpoint-moment wrapper, transform/tail-series theorem, or inverse-function specialization is claimed |
| Exact signed-global and bounded Fabius primitive ladders with finite polynomial weights | `FabiusFunction.FabiusAntiderivatives` | `normalizedVolterra_extendedFabius`, `normalizedVolterra_fabiusReal_of_le_one`, `normalizedVolterra_polynomial_mul_extendedFabius`, `normalizedVolterra_pow_mul_extendedFabius`, `normalizedVolterra_polynomial_mul_fabiusReal_of_le_one`, `normalizedVolterra_pow_mul_fabiusReal_of_le_one`, `integral_cube_mul_fabiusReal_eq`; signed formulas are global, while bounded formulas assume `x ≤ 1` |
| Absolutely summable uniform-coordinate series and their canonical pushforward laws | `FabiusFunction.WeightedUniformSeries` | `weightedUniformSeries`, `weightedUniformSeries_smul_weights`, `weightedUniformSeries_split`, `weightedUniformDistribution`, `isProbabilityMeasure_weightedUniformDistribution`, `weightedUniformDistribution_split`, `weightedUniformDistribution_reflection`, `ae_weightedUniformDistribution_mem_Icc`, `weightedUniformDistribution_restrict_Icc`, `weightedUniformDistribution_Icc` |
| Compatibility names, scalar/unit-mass refinements, and absolute continuity for weighted real laws | `FabiusFunction.WeightedUniformDistribution` | `uniformProduct_map_head_tail_function`, `weightedUniformDistribution_isProbabilityMeasure`, `weightedUniformDistribution_smul_weights`, `uniformProduct_map_head_tail_weightedUniformSeries`, `weightedUniformDistribution_unitInterval`, `weightedUniformDistribution_compl_unitInterval`, `uniformScaledAdd_absolutelyContinuous`, `weightedUniformDistribution_absolutelyContinuous_of_head_ne_zero`, `weightedUniformDistribution_absolutelyContinuous`, `weightedUniformDistribution_nullSingletonClass` |
| Exact topological support of weighted-uniform laws | `FabiusFunction.WeightedUniformSupport` | `isOpenPosMeasure_infinitePi`, `uniformProduct_isOpenPosMeasure`, `support_map_eq_closure_range_of_continuous`, `weightedUniformSeries_constCoordinates`, `weightedUniformDistribution_support_eq_range`, `range_weightedUniformSeries_eq_Icc_min_max`, `weightedUniformDistribution_support_eq_Icc_min_max`, `range_weightedUniformSeries_eq_Icc`, `weightedUniformDistribution_support_eq_Icc`, `weightedUniformDistribution_support_eq_unitInterval` |
| Continuous CDF calculus for atomless real probability laws | `FabiusFunction.ContinuousCDF` | `continuous_cdf_of_nullSingleton`, `cdf_reflection_sub`, `measure_eq_withDensity_of_cdf_hasDerivAt`; the last theorem turns an everywhere pointwise CDF derivative into the exact Lebesgue `withDensity` representation without assuming derivative continuity or prior absolute continuity, because CDF monotonicity supplies nonnegativity and local integrability |
| Contractive affine independent-copy probability laws | `FabiusFunction.AffineIndependentCopy` | At compiled checkpoint `d312c0603`: `affineIndependentCopyLaw`, `affineIndependentCopyLaw_isProbabilityMeasure`, `affineIndependentCopyLaw_eq_map_prod`, `charFun_affineIndependentCopyLaw`, `charFun_eq_mul_charFun_of_affineIndependentCopy_fixedPoint`, `charFun_iterate_of_affineIndependentCopy_fixedPoint`, `eq_of_charFun_affine_recurrence`, `affineIndependentCopyLaw_fixedPoint_unique`, `affineIndependentCopy_map_fixedPoint_unique`; the digit space is an arbitrary measurable space and the target is a second-countable Borel real inner-product space; a measurable digit map and probability digit/candidate laws suffice for the operator-level fixed-point API, while completeness is assumed only by the characteristic-recurrence and two fixed-point uniqueness theorems; uniqueness requires `|q| < 1`, includes `q = 0` and negative `q`, and uses no support, density, or moment hypothesis |
| Geometrically weighted uniform laws and their characterization | `FabiusFunction.GeometricUniformLaw`, `FabiusFunction.GeometricUniformUniqueness` | `geometricUniformWeight`, `hasSum_geometricUniformWeight`, `geometricUniformSeries`, `geometricUniformSeries_split`, `geometricUniformDistribution_selfSimilar`, `geometricUniformDistribution_absolutelyContinuous`, `geometricUniformDistribution_nullSingletonClass`, `geometricUniformDistribution_reflection`, `geometricUniformDistribution_Icc`, `eq_geometricUniformDistribution_of_selfSimilar`; the last theorem characterizes the law among all probability measures satisfying the affine product-map equation whenever `|q| < 1`, including `q = 0` and negative `q`, without support, density, or moment assumptions |
| Geometric tail dictionary and sinc-prefix factorization | `FabiusFunction.GeometricUniformDictionary`, `FabiusFunction.GeometricSincFactorization` | `charFun_geometricUniformDigit`, `charFun_geometricUniformDistribution_prefix`, `charFun_geometricUniformDistribution_prefix_sinc`, `tendsto_prefix_sinc_charFun`, `charFun_weightedSumDistribution_prefix_sinc`, `tendsto_prefix_sinc_charFun_weightedSumDistribution`; the digit formula is unconditional, while for every real `q` with `|q| < 1`, depth `m`, and frequency `t`, the law has the exact residual factorization `φ_q(t) = exp(i(1-q^m)t/2) · ∏_{k<m} sinc((1-q)q^k t/2) · φ_q(q^m t)`, and the phase-bearing prefix without the residual converges pointwise to `φ_q(t)`; this includes `q = 0` and negative `q`, and the final two declarations are the `q = 1/2` weighted-sum wrappers.  `geometric_tail_dictionary_geometricUniform` already supplies finite characteristic-function, MGF, and CGF tail factorizations, while `geometricSincProduct` already packages the rescaled sinc factors as a `tprod`.  A named characteristic-function-to-`geometricSincProduct` bridge (or explicit `HasProd` theorem), compact-uniform prefix convergence, rapid-decay bounds and Fourier inversion, explicit Bernoulli-cumulant/Bell-moment formulas and asymptotics, further transform formulas, centered packaging, and shape theory remain frontier targets |
| CDF and explicit density of the geometric uniform law | `FabiusFunction.GeometricUniformCDF` | `geometricUniformCDF`, `monotone_geometricUniformCDF`, `geometricUniformCDF_nonneg`, `geometricUniformCDF_le_one`, `measurable_geometricUniformCDF`, `continuous_geometricUniformCDF`, `geometricUniformCDF_reflection`, `geometricUniformCDF_one_half`, `geometricUniformCDF_zero_of_nonpos`, `geometricUniformCDF_one_of_one_le`, `geometricUniformCDF_eq_integral`, `geometricUniformCDF_eq_intervalIntegral`, `geometricUniformDensity`, `geometricUniformCDF_hasDerivAt`, `deriv_geometricUniformCDF`, `continuous_geometricUniformDensity`, `geometricUniformDensity_nonneg`, `geometricUniformDensity_zero_of_nonpos`, `geometricUniformDensity_zero_of_one_le`, `support_geometricUniformDensity_subset_Ioo`, `support_geometricUniformDensity_subset_Icc`, `tsupport_geometricUniformDensity_subset_Icc`, `geometricUniformDensity_hasCompactSupport`, `geometricUniformDensity_reflection`, `geometricUniformDistribution_eq_withDensity`, `contDiff_geometricUniformCDF`, `contDiff_geometricUniformDensity`; continuity and CDF reflection assume `|q| < 1`, exterior CDF values assume `0 ≤ q < 1`, and the conditioning, density, `withDensity`, compact-support, and `C∞` results assume `0 < q < 1`; the density definition is total, but only this strict positive range has the classical density interpretation; the characteristic-function sinc-prefix results are listed separately above |
| Product-probability and CDF representations | `FabiusFunction.ProbabilityRepresentation` | `weightedCoordinateSum_eq_weightedUniformSeries`, `weightedCoordinateSum_eq_geometricUniformSeries_one_half`, `weightedSumDistribution_eq_geometricUniformDistribution_one_half`, `ae_weightedSumDistribution_mem_Icc`, `weightedSumDistribution_restrict_Icc`, `weightedSumCDF_eq_geometricUniformCDF_one_half`, `weightedSumCDF_eq_fabiusReal`, `geometricUniformCDF_one_half_eq_fabiusReal`, `geometricUniformDensity_one_half_eq_rvachevUp`, `fabiusReal_eq_weightedSum_probability`, `rvachevUp_eq_weightedSumCDF`, `rvachevUp_eq_weightedSum_probability_global`; the dyadic smoothing, continuity, exterior-value, and reflection proofs route through the half-base geometric CDF API |
| Ordinary Cauchy--Stieltjes transforms of the canonical up and unit-interval laws | `FabiusFunction.CauchyTransform` | `rvachevCauchyTransform_apply`, `rvachevCauchyTransform_eq_integral_rvachevUp`, `hasDerivAt_rvachevCauchyTransform`, `analyticOn_rvachevCauchyTransform`, `fabiusStieltjesTransform_eq_two_mul_rvachevCauchyTransform`; the definitions are total under Lean's Bochner-integral convention, while the analytic statements use the named slit domains |
| Atom-exact compact-support Cauchy--CDF integration by parts | `FabiusFunction.CauchyCDF` | `integral_inv_sub_eq_mass_smul_sub_intervalIntegral_measureReal_Iic`, `integral_inv_sub_eq_sub_intervalIntegral_cdf`, `fabiusStieltjesTransform_eq_inv_sub_one_sub_intervalIntegral_fabiusReal`; the generic results assume an ordered compact interval, almost-everywhere support there, and a spectral parameter off its complexification, with finite-measure and probability normalizations respectively; the Fabius wrapper is on `fabiusStieltjesDomain` |
| Rvachev Cauchy-transform renormalization and all-order affine orbit | `FabiusFunction.CauchyRenormalization` | `mapsTo_rvachevCauchyDomain_two_mul_add_one`, `mapsTo_rvachevCauchyDomain_two_mul_sub_one`, `hasDerivAt_rvachevCauchyTransform_affineDifference`, `deriv_rvachevCauchyTransform`, `iteratedDeriv_rvachevCauchyTransform_eq_thueMorse_sum`; for every bounded Fabius solution and every point off `[-1,1]`, the exact DDE and all complex derivative orbits hold; no logarithmic fixed point, higher-kernel integral identity, Stieltjes-transform DDE wrapper, boundary/Plemelj theorem, moment/Laurent expansion, generalized order, or Jacobi/Padé result is claimed |
| Support-free quantile transport, compact inverse-CDF transport, and exact Fabius substitution | `FabiusFunction.QuantileTransport` | `map_quantile_eq`, `map_inverseCDF_volume_restrict_Icc`, `map_fabiusInv_restrict_Icc_eq_weightedSumDistribution`, `integral_comp_fabiusInv_restrict_Icc_eq_weightedSumDistribution` |
| Weighted subgraph/supergraph Fubini, generic survival layer cake, and exact Rvachev stopped primitives | `FabiusFunction.SubgraphFubini`, `FabiusFunction.SurvivalLayerCake`, `FabiusFunction.ProbabilityLaplaceMoments` | `integral_smul_setIntegral_subgraph`, `integral_smul_setIntegral_supergraph`, `intervalIntegral_survival_smul_eq_integral_clamp`, `intervalIntegral_survival_smul_eq_integral_min_of_ae_mem_Icc`, `intervalIntegral_survival_smul_eq_integral_of_ae_mem_Icc`, `intervalIntegral_rvachevUp_smul_eq_integral_min`, `intervalIntegral_rvachevUp_smul_eq_integral` |
| Atom-preserving lower-CDF layer cake and exact positive-real Fabius fractional integrals | `FabiusFunction.CDFLayerCake`, `FabiusFunction.FractionalCDFLayerCake`, `FabiusFunction.FabiusFractionalIntegral` | `intervalIntegral_cdf_smul_eq_integral_clamp`, `intervalIntegral_cdf_smul_eq_integral_max_of_ae_le`, `intervalIntegral_cdf_smul_eq_integral_max_of_ae_mem_Icc`, `intervalIntegral_cdf_smul_eq_integral_of_ae_mem_Icc`, `fractionalVolterra_measureReal_Iic_eq_integral_clamp`, `fractionalVolterra_measureReal_Iic_eq_integral_posPart`, `fractionalVolterra_cdf_eq_integral_posPart`, `fractionalVolterra_measureReal_Iic_eq_integral_rpow_of_ae_mem_Icc`, `fractionalVolterra_fabiusReal_eq_integral_posPart`, `fractionalVolterra_fabiusReal_eq_uniformProduct_integral_posPart`, `fractionalVolterra_fabiusReal_one_eq_integral_rpow`, `fractionalVolterra_fabiusReal_one_eq_uniformProduct_integral_rpow`; the partial terminal identity needs only `c ≤ b` and almost-everywhere upper support `z ≤ b`, the probability wrapper is stated directly with Mathlib's CDF, and the Fabius stopped-power formulas hold for every real endpoint and every positive real order; no fractional derivative or complex-order continuation is asserted |
| Generic inverse-clock and exact Fabius weighted layer-cake identities | `FabiusFunction.InverseLayerCake` | `galoisConnection_Icc_restrict_of_lt_iff_lt`, `intervalIntegral_smul_intervalIntegral_of_lt_iff_lt`, `intervalIntegral_smul_comp_of_lt_iff_lt`, `intervalIntegral_mul_comp_sub_of_lt_iff_lt_of_absolutelyContinuousOnInterval`, `intervalIntegral_mul_comp_of_lt_iff_lt_of_absolutelyContinuousOnInterval`, `intervalIntegral_smul_intervalIntegral_fabiusInv`, `intervalIntegral_smul_comp_fabiusInv`, `intervalIntegral_mul_comp_fabiusInv_of_absolutelyContinuousOnInterval`, `intervalIntegral_mul_fabiusInv_eq`, `intervalIntegral_fabiusInv_eq_intervalIntegral_rvachevUp`, `intervalIntegral_fabiusInv_eq_one_half`; the strict order adjunction makes the interval restrictions a Galois connection and supplies measurable clamped representatives, so none of the public generic layer-cake theorems assumes clock measurability; the explicit-primitive and pointwise-`C¹` forms allow real or complex weights and Banach-valued primitives, while the absolutely-continuous forms allow real or complex `L¹` weights and a real-valued primitive, include degenerate ordered rectangles, and need no separate right-hand-side integrability hypothesis |
| Absolutely-continuous two-function and variable-upper calculus for inverse-order pairs | `FabiusFunction.InversePairIntegral` | `intervalIntegral_deriv_mul_comp_add_comp_mul_deriv_of_lt_iff_lt`, `intervalIntegral_deriv_mul_comp_add_comp_mul_deriv_to_of_lt_iff_lt`, `intervalIntegral_deriv_mul_fabiusReal_add_fabiusInv_mul_deriv`, `intervalIntegral_deriv_mul_fabiusReal_add_fabiusInv_mul_deriv_to`, `intervalIntegral_fabiusReal_add_fabiusInv_eq_one`, `intervalIntegral_fabiusInv_to_eq_mul_sub_intervalIntegral_fabiusReal`; the generic theorems derive monotonicity and measurable clamped extensions of both clocks from the strict order equivalence, include degenerate ordered intervals, and cover every proper compact cut `y ∈ [a,b]`; reversed endpoints still require swapping the corresponding interval, and improper singular endpoints, higher or fractional inverse primitives, complex-valued arbitrary-AC factors, and complex Mellin continuation are not claimed |
| Weighted-partition exponential coefficients over commutative `ℚ`-algebras | `FabiusFunction.ExponentialPartition`, `FabiusFunction.ExponentialBell` | `partitionExpSum_recurrence`, `partitionExpSum_succ`, `partitionExpSum_eq_sum_div`, `partitionExpSum_eq_expCoeff` |
| Complete Bell and moment--cumulant transforms over commutative `ℚ`-algebras | `FabiusFunction.MomentCumulantAlgebra` | `factorialNormalize`, `completeBellPolynomial`, `momentCumulant`, `completeBellPolynomial_succ`, `completeBellPolynomial_momentCumulant`, `momentCumulant_completeBellPolynomial` |
| Nonmonic Hensel lifting and formal implicit roots | `FabiusFunction.ImplicitPowerSeries` | `FormalImplicitRoot.exists_isRoot_sub_mem`, `FormalImplicitRoot.eq_of_isRoot_of_sub_mem`, `FormalImplicitRoot.existsUnique_isRoot_sub_mem`, `PowerSeries.Implicit.existsUnique_isRoot_constantCoeff`, `PowerSeries.Implicit.existsUnique_zeroConstant_root`, `PowerSeries.Implicit.root`, `PowerSeries.Implicit.constantCoeff_root`, `PowerSeries.Implicit.eval_root`, `PowerSeries.Implicit.eq_root`; this is a generic formal-series root engine over complete adic commutative rings and arbitrary commutative coefficient rings, with no concrete inverse-Fabius germ, analytic convergence, plateau localization, flat-remainder, or quantile theorem |
| Finite polynomial integrals from raw moments and formal cumulants | `FabiusFunction.PolynomialExpectationCumulant` | `integral_eval₂_eq_sum_moment`, `integral_eval₂_eq_sum_completeBell_momentCumulant_with_mass_correction`, `integral_eval₂_eq_sum_completeBell_momentCumulant_of_moment_zero_eq_one`, `integral_eval₂_eq_sum_completeBell_momentCumulant` |
| Universal endpoint-transfer polynomials and their formal exponential series | `FabiusFunction.EndpointTransferPolynomials` | `endpointTransferPolynomial_succ`, `endpointTransferPolynomial_eq_partitionExpSum`, `endpointTransferSeries_eq_exp_subst`, `aeval_endpointTransferPolynomial`, `map_endpointTransferSeries` |
| Finite base-`b` layer regrouping in multiplicative and additive form | `FabiusFunction.BaseLayerRegrouping` | `filter_dvd_eq_image`, `prod_multiples_eq_prod_filter`, `sum_multiples_eq_sum_filter`, `prod_layers_eq_prod_pow_card`, `sum_layers_eq_sum_nsmul_card`, `card_filter_pow_dvd`, `prod_layers_eq_prod_pow_multiplicity`, `sum_layers_eq_sum_nsmul_multiplicity` |
| Infinite products at summable scales | `FabiusFunction.ScaledInfiniteProducts` | `summable_norm_scaled_sub_one`, `hasProdUniformlyOn_scaled`, `multipliableUniformlyOn_scaled`, `hasProdLocallyUniformly_scaled`, `multipliableLocallyUniformly_scaled`, `continuous_tprod_scaled`, `differentiable_tprod_scaled`, `differentiable_tprod_scaled_of_eq_one`, `tprod_scaled_ne_zero`, `tprod_scaled_eq_zero_iff`; pointwise deviation summability allows an arbitrary normed-ring target, the compact-uniform API assumes a continuous factor and a complete commutative normed-ring target with a normed unit, local uniformity adds local compactness, holomorphy uses a complete normed complex-algebra target, and zero detection adds a multiplicative norm but needs neither continuity nor local compactness |
| Geometric reciprocal-Gamma products and the dyadic Rvachev bridge | `FabiusFunction.GeometricReciprocalGamma` | `shiftedReciprocalGamma`, `shiftedReciprocalGamma_zero`, `shiftedReciprocalGamma_differentiable`, `shiftedReciprocalGamma_sub_one_isBigO`, `shiftedReciprocalGamma_eq_zero_iff`, `shiftedReciprocalGamma_mul_neg`, `summable_norm_qpow`, `geometricReciprocalGamma`, `geometricReciprocalGammaFactors_multipliable`, `geometricReciprocalGamma_differentiable`, `geometricReciprocalGamma_zero`, `geometricReciprocalGamma_mahler`, `geometricReciprocalGamma_eq_zero_iff`, `geometricGamma`, `geometricGamma_meromorphic`, `geometricGamma_mahler`, `geometricSincProduct`, `geometricReciprocalGamma_mul_neg`, `dyadicReciprocalGamma`, `dyadicGamma`, `dyadicReciprocalGamma_differentiable`, `dyadicReciprocalGamma_zero`, `geometricSincProduct_inv_two`, `dyadicReciprocalGamma_mul_neg`, `rvachevFourierProduct_eq_one_div_dyadicGamma_mul`; every generic analytic identity assumes complex `q` with `‖q‖ < 1` (including `q=0`), while normalization at zero is unconditional; `geometricGamma` and `dyadicGamma` are totalized pointwise inverses, not proved raw Gamma tprods away from poles |
| Exact dyadic reciprocal-Gamma zeros and meromorphic pole orders | `FabiusFunction.DyadicGammaOrder` | `dyadicReciprocalGamma_eq_zero_iff`, `dyadicReciprocalGamma_int_ne_zero_of_nonneg`, `dyadicReciprocalGamma_nat_ne_zero`, `dyadicGamma_meromorphic`, `analyticOrderAt_dyadicReciprocalGamma_int_of_neg`, `analyticOrderAt_dyadicReciprocalGamma_neg_nat`, `meromorphicOrderAt_dyadicGamma_int_of_neg`, `meromorphicOrderAt_dyadicGamma_neg_nat`; integer order statements assume a negative center, natural wrappers assume a nonzero index, and negative meromorphic order is Mathlib's encoding of a pole |
| Complete homogeneous evaluations and denominator-free geometric principal specialization | `FabiusFunction.CompleteHomogeneous`, `FabiusFunction.GeometricCompleteHomogeneous` | `completeHomogeneousEval_eq_eval_hsymm`, `completeHomogeneousEval_smul`, `completeHomogeneousEval_option_zero`, `completeHomogeneousEval_fin_succ`, `completeHomogeneousEval_geometric`, `completeHomogeneousEval_scaled_geometric`, `completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial` |
| Every residual moment of finite interpolation and geometric Richardson rows | `FabiusFunction.LagrangeResidualMoments`, `FabiusFunction.GeometricResidualMoments` | `sum_weight_mul_pow_card_add`, `sum_lagrangeEvalWeight_mul_pow_card_add`, `sum_weight_mul_geometric_pow_succ_add`, `sum_weight_mul_geometric_pow_of_pos`, `sum_weight_mul_scaled_geometric_pow_succ_add`, `sum_weight_mul_scaled_geometric_pow_of_pos`, `sum_geometricLagrangeWeight_mul_pow_succ_add`, `sum_geometricLagrangeWeight_mul_pow_of_pos`, `sum_geometricLagrangeWeight_mul_scaled_geometric_pow_of_pos`, `sum_geometricLagrangeWeight_mul_shifted_pow_of_pos` |
| Arbitrary finite-node and geometric formal-power-series filters | `FabiusFunction.FinitePowerSeriesFilter`, `FabiusFunction.GeometricPowerSeriesFilter` | `finitePowerSeriesFilter`, `coeff_finitePowerSeriesFilter`, `finitePowerSeriesFilter_rescale`, `map_finitePowerSeriesFilter`, `coeff_finitePowerSeriesFilter_of_exact_of_le`, `geometricSeriesFilter`, `coeff_geometricSeriesFilter_of_exact`, `geometricSeriesFilter_eq_residual_mk`, `geometricLagrangeSeriesFilter_eq_residual_mk`; these are coefficientwise algebraic identities and assert no analytic convergence or remainder estimate |
| Unconditionally summable finite-node and geometric analytic-series filters | `FabiusFunction.AnalyticSeriesFilter` | `finiteAnalyticSeriesFilter`, `summable_finiteAnalyticSeriesFilter_diagonal`, `finiteAnalyticSeriesFilter_eq_tsum`, `finiteAnalyticSeriesFilter_eq_head_add_tail_of_exact`, `finiteAnalyticSeriesFilter_eq_constant_add_tail_of_exact_zero`, `geometricAnalyticSeriesFilter`, `geometricAnalyticSeriesFilter_eq_constant_add_gaussian_tsum`, `geometricLagrangeAnalyticSeriesFilter_eq_constant_add_gaussian_tsum`, `geometricLagrangeAnalyticSeriesFilter_shifted`; the arbitrary finite filter works over a commutative semiring acting on a normed additive group and splits into an exact finite head plus an exact infinite tail under unconditional summability of the weighted sampled series, so a zero-weight node imposes no convergence condition; the geometric and Lagrange wrappers require summability only at nonzero-weight nodes and give the exact denominator-free Gaussian `tsum` tail; conditionally-only convergent boundary series, a formal-power-series evaluation bridge, a sinc-product instantiation, radius-of-convergence or uniform-convergence theorems, norm/sign/error bounds, asymptotic acceleration, positivity, and Fabius-specific acceleration are not asserted |
| Denominator-free finite `q`-binomial algebra | `FabiusFunction.FiniteQBinomialCore` | `map_gaussianBinomial`, `gaussianBinomial_succ_succ`, `gaussianBinomial_succ_succ_alt`, `gaussianBinomial_symm`, `finiteQPochhammerIn_add`, `finiteQPochhammerIn_self_add`, `finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial`, `finite_qBinomial_theorem`; all identities avoid quotient and cancellation hypotheses |
| Geometric Richardson filters, Gaussian coefficients, all residual moments, and finite conditioning | `FabiusFunction.GeometricQBinomialLagrange`, `FabiusFunction.GeometricRichardson`, `FabiusFunction.GeometricLagrangeWeights`, `FabiusFunction.GeometricLagrangeQBinomial`, `FabiusFunction.GeometricLagrangeQMoments` | `reversed_finite_qBinomial_theorem`, `sum_geometricLagrangeWeight_mul_pow_eq_gaussianBinomial`, `geometricLagrangeWeightPolynomial_eq_forwardGeometricRichardsonPolynomial`, `geometricLagrangeQMoment_eq_residual_qBinomial`, `sum_abs_geometricLagrangeWeight_eq_prod`; the rational closed forms use their stated nonzero-base and nonvanishing finite-denominator hypotheses, while sign and variation assume `0 < q < 1` |
| Infinite `q`-Pochhammer symbols and the limiting general-`q` row condition number | `FabiusFunction.LimitConditionNumber` | `qPochhammerInf`, `multipliable_one_sub_mul_pow`, `tendsto_finiteQPochhammerIn`, `qPochhammerInf_self_pos`, `qConditionNumberLimit`, `tendsto_sum_abs_qToeplitzWeight`, `one_div_one_sub_le_qConditionNumberLimit`, `tendsto_qConditionNumberLimit_atTop_at_one_left`, `one_lt_qConditionNumberLimit`, `qConditionNumberLimit_zero`, `thousand_le_qConditionNumberLimit`; for `0 ≤ q < 1` the finite row variation converges to `(-q;q)_∞ / (q;q)_∞`, whose denominator is strictly positive and whose value is at least `1 / (1-q)`; consequently the limit tends to `+∞` as `q → 1⁻`, so no uniform-in-`q` bound exists |
| Exact lower-Lambert phase locking and reciprocal-grid Richardson moments | `FabiusFunction.LambertPhaseLockedRichardson` | `fabiusLambertPhase_phaseLockedNode`, `shiftedReciprocalLagrangeWeight_eq_choose`, `sum_shiftedReciprocalLagrangeWeight_mul_invPow_card_add`, `sum_shiftedReciprocalLagrangeWeight_mul_invPow_eq_completeHomogeneous` |
| Formal power-series logarithms and finite-product additivity | `FabiusFunction.LogSeriesMultiplicative` | `SaddleExpansion.logOf`, `SaddleExpansion.massSeries_coeff`, `SaddleExpansion.constantCoeff_logOf`, `SaddleExpansion.mul_derivative_logOf`, `SaddleExpansion.logOf_eq_of`, `SaddleExpansion.logOf_mul`, `SaddleExpansion.logOf_one`, `SaddleExpansion.logOf_prod` |
| Generic unit-interval Laplace-moment bounds | `FabiusFunction.UnitLaplaceMomentBounds` | `unitLaplaceMoment_midpoint_sq_le_all`, `unitLaplaceMoment_le_of_tilt_sub`, `pow_mul_exp_neg_le_factorial`, `fabiusLaplaceMoment_midpoint_sq_le_all`, `fabiusLaplaceMoment_le_of_tilt_sub` |
| Exact dyadic computation and analytic correctness | `FabiusFunction.DyadicAnalytic`, `FabiusFunction.GlobalDyadic` | `fabiusDyadicValue`, `evalFabiusDyadic`, `fabiusDyadicUnit_cast`, `extendedFabiusDyadicValue_cast` |
| First and second published papers | `FabiusFunction.Paper05442`, `FabiusFunction.Paper06487` | the theorem maps in the module docstrings and [`docs/PAPER_COVERAGE.md`](docs/PAPER_COVERAGE.md) |
| Corrected sharp and all-orders asymptotics | `FabiusFunction.PaperFabiusAsymptotic` | `abs_log_fabius_dyadic_sub_explicitCumulantMain_le`, `log_fabius_sub_sharpLambertMain_hasAsymptoticExpansion`, `fabiusSharpLambertExpansion_two` |
| Fourier--Legendre expansions, least squares, and coefficient energy | `FabiusFunction.FabiusTranslatedLegendreSeries`, `FabiusFunction.FabiusLegendreLeastSquares`, `FabiusFunction.FabiusLegendreEnergy` | `hasSum_canonical_rvachevLegendreSeries_formula`, `rvachevLegendrePartialSum_pythagorean`, `rvachevLegendreBlock`, `intervalIntegral_rvachevLegendreBlock_mul`, `hasSum_rvachevLegendreCoefficient_energy`, `hasSum_rvachevLegendreCoefficient_energy_tail`, `rvachevLegendreSquaredError_partialSum_eq_tsum_tail`, `fabiusSquareEnergy_eq_tsum_legendre` |
| Inverse construction, exact smoothness locus, interior calculus, curvature, and endpoint steepness | `FabiusFunction.FabiusInverse` | `fabiusInv`, `fabiusReal_fabiusInv`, `fabiusInv_hasDerivAt`, `deriv_fabiusInv_eq_inv_two_mul_rvachevUp`, `deriv_fabiusInv_pos`, `fabiusInv_contDiffOn_Ioo`, `fabiusInv_contDiffAt_infty_iff`, `fabiusInv_differentiableAt_iff`, `deriv_deriv_fabiusInv`, `deriv_fabiusInv_half`, `deriv_deriv_fabiusInv_half`, `deriv_deriv_fabiusInv_neg_iff`, `deriv_deriv_fabiusInv_pos_iff`, `deriv_deriv_fabiusInv_eq_zero_iff`, `strictConcaveOn_fabiusInv_firstHalf`, `strictConvexOn_fabiusInv_secondHalf`, `id_isLittleO_fabiusInv_pow_at_zero_right`, `one_sub_isLittleO_one_sub_fabiusInv_pow_at_one_left`, `tendsto_deriv_fabiusInv_atTop_at_zero_right`, `tendsto_deriv_fabiusInv_atTop_at_one_left` |
| Elementary functions and non-elementarity | `FabiusFunction.ElementaryFunction`, `FabiusFunction.AlgebraicBranch`, `FabiusFunction.InverseBranch`, `FabiusFunction.NotElementary`, `FabiusFunction.InverseNotElementary` | `IsElementary`, `IsElementary.comp`, `IsElementary.rpow_of_ne_zero`, `IsElementary.dense_analyticLocus`, `analyticDenseOn_of_algebraic`, `canonical_fabius_not_isElementary_on_Ioo`, `canonical_fabius_not_isElementary`, `canonical_fabius_not_algebraicBranch_on_Ioo`, `IsElementaryOrInverse`, `fabiusInv_not_analyticAt`, `canonical_fabiusInv_not_isElementary_on_Ioo`, `canonical_fabiusInv_not_isElementaryOrInverse_on_Ioo` |
| Computable-real-function theorems | `FabiusFunction.FabiusComputableSpline` | `fabiusSplineApproxPR_computable`, `extendedFabiusSplineApproxPR_computable`, `fabius_isComputableRealFunction`, `globalFabius_isComputableRealFunction` |

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
in its polynomial form; these declarations do not formalize its finite
up-translate realization, the separate Fourier-product or infinite-sinc
integral for `A_2`, or a rationality theorem for its partial sums.

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
`Fabius.isGreatest_abs_iteratedDeriv_fabiusReal`.

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
