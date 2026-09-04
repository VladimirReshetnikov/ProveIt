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

> **Artifact status (2026-09-03).**  The live facade union contains exactly
> 902 source modules and 11,443 public declarations.  The documentation audit
> reports no missing module headers or declaration comments.  Its q-series union retains
> `QPochhammerEntire` 0+5, `GeometricPochhammerNormalConvergence` 0+3,
> `QPochhammerDissection` 0+2,
> `QPochhammerInfinite` 1+29,
> `GaussianBinomialAtNegOneDerivative` 0+4,
> `GaussianBinomialContinuity` 0+3,
> `GaussianBinomialCumulants` 2+24,
> `GaussianBinomialPalindromic` 0+14,
> `GaussianBinomialPolynomialStructure` 0+5,
> `CentralQBinomialReduction` 0+6, `CyclotomicFactorization` 0+7,
> `JacobiTripleProduct` 2+25,
> `QBinomialTheoremInfinite` 1+22, `QPascalSummation` 0+4,
> `QuantumBinomial` 0+2, `RogersSzegoPolynomial` 1+9,
> `QPochhammerInfiniteBounds` 0+5, `HeineTransformation` 2+5,
> `QGaussSummation` 0+2, `QPochhammerComplexOrder` 1+4,
> `BasicHypergeometricSeries` 2+5, `QMultinomial` 1+9,
> `GaussianBinomialPalindromic` 0+14, `JacksonIntegral` 1+7,
> `QExponential` 3+8, `ThetaQuasiPeriodicity` 1+6,
> `GaussianBinomialPolynomialStructure` 0+5, `JacobiCubic` 0+2,
> `QPochhammerLogDerivative` 0+10, `QPochhammerOrderDerivative` 0+3,
> `CentralQBinomialReduction` 0+6, `CyclotomicFactorization` 0+7,
> `PrimitiveRootBlock` 0+3, `QLucas` 0+7,
> `CyclotomicDivisibility` 0+3, `QCatalan` 1+11,
> `NewtonInterpolation` 3+19, `QBetaIntegral` 1+8,
> `GaussianBinomialInteger` 1+10, `GaussianBinomialComplexOrder` 1+5,
> `QPfaffSaalschutz` 0+3, `TwoPhiOneReversal` 2+12,
> `QChuVandermonde` 0+10, `QuantumMultinomial` 0+5, and
> `GaussianBinomialBounds` 0+6.  The geometric-interpolation union now also
> includes `GeometricRichardsonGenerating` 3+7.
> The retained
> primary exposition, Lean walkthrough, canonical frontier, Representation
> Frontiers, filed New Frontiers, notation catalogue, Integration-and-Transform
> master, comb-interpolation, and q-series synthesis PDFs contain respectively
> 183, 130, 257, 301, 41, 88, 377, 158, and 389 A4 pages.  Their current TeX
> sources contain post-render unions, including the centered
> Appell/deconvolution, arbitrary-phase synthesis, Lagrange--Rvachev,
> prime-power companion-row, outer Pochhammer normal convergence, total
> rational integer-index zero-row Wigner-square, and
> finite/infinite q-Pochhammer material, as well as the fixed-depth effective
> inverse realizer and total inverse computability theorem.  These retained PDFs
> are historical receipts, not source/PDF-parity claims; fresh uninterrupted three-pass
> Libertinus rebuilds remain pending.  The reorganized q-series roots whose
> shared-notation input paths changed likewise remain pending parity rebuilds.

The formally proved small-argument hierarchy—including the corrected sharp
asymptotic, the general coefficient algebra for the recursive all-orders
expansion, and the first two explicit periodic saddle corrections—is integrated
into the primary exposition. Exploratory derivations, the small-argument
notebook, and the primary-exposition gap register are preserved in the canonical
[research-frontier LaTeX volume](docs/semi-formalized-research-frontiers/semi-formalized-research-frontiers.tex)
([PDF](docs/semi-formalized-research-frontiers/semi-formalized-research-frontiers.pdf)).
That volume labels claims still awaiting literal Lean counterparts and records
their exact outstanding proof obligations.

Inverse analyticity, non-elementarity, endpoint asymptotics, dyadic
self-sampling, and effective inverse computation are treated together in
[*Inverse Fabius Theory: Analyticity, Asymptotics, Computability, and Dyadic
Sampling*](docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/Inverse_Fabius_Analyticity_Asymptotics_and_Computability/inverse_fabius_theory.tex)
([PDF](docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/Inverse_Fabius_Analyticity_Asymptotics_and_Computability/inverse_fabius_theory.pdf)).
Its
[theorem concordance](docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/Inverse_Fabius_Analyticity_Asymptotics_and_Computability/theorem_concordance.csv)
distinguishes exact Lean counterparts from human-proved frontier results,
conjectures, open problems, and non-theorem source material; its
[provenance ledger](docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/Inverse_Fabius_Analyticity_Asymptotics_and_Computability/PROVENANCE.md)
records the five retired source packages and their immutable recovery points.

On the formal side, the class of elementary functions of one real variable is
proved real analytic on a dense open subset of the line, and this is combined
with nowhere analyticity to show that no elementary function agrees with the
Fabius function on any subset of `[0,1]` with nonempty interior. The same
conclusion holds for the stated class of continuous algebraic branches, which
also reaches algebraic functions not expressible by radicals. The inverse
Fabius function is nowhere real analytic on `[0,1]`, hence is not elementary;
neither it nor the Fabius function becomes representable after closing the
class under continuous inverse branches at any depth, a closure that includes
the Lambert `W` function.

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

The current New Frontiers finite Gram--Legendre crosswalk has eleven modules,
twenty public definitions, and 109 public theorems, hence 129 declarations.
Its former nine-module `18+81=99` subtotal is extended by
`LegendreGauntClosedForm` (`2+25`) and `FabiusLegendreGauntClosedForm` (`0+3`).
Thus the integer-index zero-row square datum and finite Wigner-square Gram route
are closed; only signed/general Wigner and the later infinite spectral layers
remain outside this tranche.

Precisely, the directly defined square datum is not a bridge to a separately
implemented general Wigner symbol.  There is no signed value or phase
convention, half-integer or nonzero-magnetic-index API, general
`3j`/`6j`/`9j`, orthogonality, recoupling, or named Wigner-symmetry theorem.
The Gaunt factorial form and product-coefficient nonnegativity/zero criteria are
available by composing the listed results but have no separate named wrappers.
Infinite Legendre interchange, Christoffel reconstruction, roots/quadrature,
Padé/J-fractions, infinite Jacobi theory, and asymptotics also remain open.

| Purpose | Focused import | Good starting declarations |
| --- | --- | --- |
| Definitions, the bounded characterization, folded `up`, and the global first-jet reflection law | `FabiusFunction.Basic`, `FabiusFunction.Differential` | `BoundedFabius`, `IsFabius`, `rvachevUp`, `rvachevUp_even`, `rvachevUp_eq_zero_of_not_mem_Ioo`, `support_rvachev_subset_Ioo`, `rvachev_hasDerivAt`, `fabius_hasDerivAt`, `deriv_fabiusReal`, `deriv_fabiusReal_one_sub` |
| Sharp bounded derivatives and the exact zero-interleaved Thue--Morse pattern on every matched dyadic grid | `FabiusFunction.BoundedDerivatives` | `iteratedDeriv_fabiusReal_of_lt_one`, `iteratedDeriv_fabiusReal_dyadicGrid_eq_ite`, `iteratedDeriv_fabiusReal_dyadicGrid_eq_zero_iff`, `abs_iteratedDeriv_fabiusReal_dyadicGrid_of_odd`, `abs_iteratedDeriv_fabiusReal_le`, `isGreatest_abs_iteratedDeriv_fabiusReal` |
| Exact derivative cells, signed natural moments, and normalized signed/absolute-value distributions | `FabiusFunction.RvachevDerivativeDistribution` | Exhaustive public surface (one definition and 18 theorems): `rvachevDerivativeCell`; `rvachevDerivativeCell_eq_div_add`, `rvachevDerivativeCell_one_eq_succ_neg_one`, `rvachevDerivativeCell_zero_neg_one`, `rvachevDerivativeCell_two_pow_neg_one`, `rvachevDerivativeCell_mem_Icc`, `iteratedDeriv_rvachev_cell`, `iteratedDeriv_rvachev_cell_zero`, `abs_iteratedDeriv_rvachev_cell`, `intervalIntegral_comp_iteratedDeriv_rvachev`, `intervalIntegral_iteratedDeriv_rvachev_pow`, `intervalIntegral_iteratedDeriv_rvachev_pow_of_even`, `intervalIntegral_iteratedDeriv_rvachev_pow_eq_zero_of_odd`, `intervalIntegral_comp_normalized_iteratedDeriv_rvachev`, `intervalIntegral_comp_abs_iteratedDeriv_rvachev`, `intervalIntegral_comp_normalized_abs_iteratedDeriv_rvachev`, `map_normalized_abs_iteratedDeriv_rvachev_restrict_Icc`, `map_normalized_iteratedDeriv_rvachev_restrict_Icc`, and `intervalIntegral_abs_iteratedDeriv_rvachev_rpow`.  The signed-moment theorems take `F : BoundedFabius`, `hF : IsFabius F`, and `n m : ℕ`.  With `T_n=(n+1).choose 2`, the hypothesis-free general formula multiplies the base moment by `((2 : ℝ)^n)⁻¹ * (1 + (-1 : ℝ)^m)^n * ((2 : ℝ)^T_n)^m`; at `n=0` and odd `m`, its Boolean-cube factor is deliberately `0^0=1`, so it recovers the generally nonzero original odd moment.  The even corollary assumes exactly `Even m` and holds for every `n`, including `n=0` and `m=0`; the odd vanishing corollary assumes exactly `0<n` and `Odd m`.  At every positive derivative order, `intervalIntegral_comp_normalized_iteratedDeriv_rvachev` gives the sharply normalized symmetric half-mixture of `up` and `-up` for a continuous `H : ℝ → E` valued in any real Banach space: the normalization is `((2 : ℝ)^T_n)⁻¹` and the mixture scalar is `(2 : ℝ)⁻¹`.  Under the same exact hypothesis `0<n`, `map_normalized_iteratedDeriv_rvachev_restrict_Icc` gives the corresponding equality of Borel pushforwards of `volume.restrict (Set.Icc (-1) 1)`, with measure scalar `(2 : NNReal)⁻¹`.  This positivity hypothesis is essential: at `n=0` the normalized signed derivative has the unsymmetrized original `rvachevUp` law.  Separately, the absolute-moment theorem uses `Real.rpow` for every real `p>=0`, and the normalized absolute derivative has the same restricted-Lebesgue pushforward as `up` at every order, including zero.  No separate product-space Rademacher realization, `eLpNorm` or general rearrangement-invariant norm ladder, inverse-Fabius level-set formula, packaged beta theorem, or spectral layer is asserted. |
| Existence, uniqueness, and the canonical functions | `FabiusFunction.PaperStatements` | `existsUnique_fabius`, `fabius`, `fabius_spec`, `globalFabius` |
| Original compact-support characterization and bounded/original bridge | `FabiusFunction.OriginalUniqueness` | `IsOriginalFabius`, `IsOriginalFabius.mk_of_derivative_law`, `IsFabius.isOriginalFabius_rvachevUp`, `rvachevUp_eq_iff_eqOn_Iic_one`, `isFabius_iff_isOriginalFabius_rvachevUp_and_rightTail`, `isOriginalFabius_iff_existsUnique_isFabius` |
| Generic affine-difference iterates and derivative orbits | `FabiusFunction.AffineDifferenceOrbit` | `affineDifference_iterate_apply`, `iteratedDeriv_eq_affineDifference_iterate_on`, `affineDifference_iterate_two_one_apply`; the module assumes a one-step derivative identity and does not prove the up-law resolvent equation |
| Central-binomial valuation and the Thue--Morse sign | `FabiusFunction.CentralBinomialValuation` | Exhaustive public surface: `padicValNat_two_centralBinom`, `thueMorseSign_eq_neg_one_pow_centralBinom`, `padicValNat_two_centralBinom_eq_zero_iff`; for every natural `n`, the valuation is `binaryWeight n`, the sign is its `(-1)`-power, and valuation zero is equivalent to binary weight zero (hence occurs only at `n = 0`, not at positive powers of two) |
| Prime-power Pascal-row valuations and the dyadic-comb weights | `FabiusFunction.PrimePowerBinomialValuation` | Exhaustive zero-definition/six-theorem surface: `primePowerChoose_padicValNat_add`, `primePowerChoose_padicValNat`, `primePowerSubOneChoose_padicValNat`, `primePowerSubTwoChoose_padicValNat`, `twoPowChoose_padicValNat`, and `twoPowSubTwoChoose_padicValNat`.  For every prime `p`, `j ≤ p^m`, and `j ≠ 0`, the first two give the truncation-free additive valuation identity and its natural-subtraction form, including `j = p^m` and `m = 0`.  Every column `j < p^m` of row `p^m-1` is a `p`-adic unit, and for exactly `0 < j < p^m` one has `v_p(C(p^m-2,j-1)) = v_p(j)`.  The two dyadic wrappers give the ordinary row formula and this endpoint-flat companion for `0 < j < 2^m`.  The strict upper bound is essential because the companion binomial coefficient is zero at `j=p^m`; only valuation-histogram counts remain open. |
| Rademacher sine signs and the Thue--Morse product | `FabiusFunction.RademacherSine` | Exhaustive nine-theorem surface: `sin_pi_mul_eq_neg_one_zpow_floor`, `sin_pi_mul_fract_pos`, `sign_sin_pi_mul`, `floor_rademacherPoint`, `fract_rademacherPoint_ne_zero`, `sign_sin_rademacherPoint`, `sign_sin_rademacherPoint_eq_one_of_lt`, `thueMorseSign_eq_prod_sign_sin`, and `thueMorseSign_eq_tprod_sign_sin`.  The factored sine identity is unconditional; the two general sign statements assume exactly a nonzero fractional part; the half-shifted point is never integral; the finite product assumes `n < 2^m`; and the `tprod` identity is total because all sufficiently late factors are proved to equal one.  This is finite-support sign bookkeeping, not convergence of a genuinely nontrivial infinite product or an unshifted sine formula. |
| Binary digits as differences of dyadic floors | `FabiusFunction.BinaryDigitFloor` | Exhaustive public surface: `div_two_pow_succ_eq_div_div`, `sub_two_mul_div_two`, `div_two_pow_sub_two_mul_div_two_pow_succ`, `testBit_toNat_eq_div_sub_two_mul_div`; the identities are total in their natural-number inputs and give the atlas's exact floor-difference digit formula, without an analytic or real-floor generalization |
| General-base cumulative scale multiplicities and digit recovery | `FabiusFunction.BaseDigitMultiplicity` | Exhaustive public inventory: zero definitions and five theorems, `sum_range_weightedScaleMultiplicity_of_log_lt`, `sum_range_weightedScaleMultiplicity_log`, `sum_range_div_pow_log_eq_self_add_tail`, `sub_one_mul_sum_padicValNat_succ_add_digitSum`, and `sum_range_padicValNat_succ_eq_sub_digitSum_div`.  The first two hold over every additive commutative monoid; the explicit-height form assumes `1 < b` and `Nat.log b N < H`, while the sharp-height form assumes only `1 < b`.  The remaining natural-number identities also assume exactly `1 < b`, include `N = 0`, and require no primality.  This is the finite count `(b-1) * sum_(n=1)^N (1+nu_b(n)) + s_b(N) = bN` and its quotient form, not an analytic zero-multiplicity theorem. |
| Total complex finite Thue--Morse sinc and negative-Laplace bridges | `FabiusFunction.ThueMorseComplexProductBridge` | `shiftedComplexSincPrefix`, `complexLaplacePrefix`, `sum_thueMorseSign_cexp_eq_sin_prod`, `thueMorseBlock_cexp_eq_sincPrefix`, `thueMorseBlock_cexp_eq_sincPrefix_of_pos`, `thueMorseBlock_exp_neg_eq_laplacePrefix`, `shiftedComplexSincPrefix_eq_thueMorseBlock_cexp_of_pos`, `complexLaplacePrefix_eq_thueMorseBlock_exp_neg`, `complexExpm1Div_neg_eq_exp_mul_complexSinc`, `complexLaplacePrefix_eq_exp_mul_shiftedComplexSincPrefix`, `shiftedComplexSincPrefix_apply_zero`, `complexLaplacePrefix_apply_zero`; the primary equalities and the finite Fourier--Laplace rotation hold at every level and at the removable origin, while the quotient forms assume a nonzero free variable |
| Centered mixed differences and symmetric Thue--Morse blocks | `FabiusFunction.ThueMorseSymmetricDifference` | Exhaustive public surface (two definitions and 11 theorems): `symmetricMixedDifference`, `symmetricMixedDifference_empty`, `symmetricMixedDifference_singleton`, `symmetricMixedDifference_insert`, `symmetricMixedDifference_eq_sum_powerset_smul`, `symmetricMixedDifference_polynomial_eq_coeff_card`, `symmetricMixedDifference_polynomial_of_degree_lt`, `symmetricMixedDifference_pow_card`, `symmetricDyadicMixedDifference`, `symmetricDyadicMixedDifference_zero`, `symmetricDyadicMixedDifference_eq_sum_thueMorseSign_smul`, `symmetricDyadicMixedDifference_inv_two_pow_eq_sum_thueMorseSign_smul`, and `symmetricDyadicMixedDifference_inv_two_pow_succ_eq_sum_thueMorseSign_smul`.  The general centered-cube layer needs only additive commutative groups and an additive action, permits repeated half-step values, and gives the exact powerset expansion.  Over a commutative ring, a polynomial of degree at most `s.card` is reduced to its degree-`s.card` coefficient times the sign-free factor `s.card! * ∏_(i∈s) (2*a_i)`; degree below `s.card` is annihilated, including the zero-polynomial/empty-support boundary, and the first surviving power has the displayed top factor.  The dyadic block identity is group-valued; the two increasing-grid wrappers require a characteristic-zero field in the argument and give `x-(1-2^-m)+2*n*2^-m` for every `m`, including `m=0`.  At positive order `m+1`, the full point is `x-(1-2^-(m+1))+n/2^m`; its varying term is `n/2^m` and its mesh spacing is `1/2^m`.  This closes the Boolean-cube, polynomial, and affine-grid clauses of the continuous-chaos report's Thue--Morse corner theorem.  Its repeated-integral identity under `C^N` hypotheses remains unformalized, so that report theorem is still near-complete rather than complete; the following Walsh conditional-expectation corollary also still lacks its sign--magnitude probability construction and `2^-N` normalization. |
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
| Totalized real hyperbolic sinc, activation odds, and activation probability | `FabiusFunction.HyperbolicActivation` | Exhaustive public surface (four definitions and 58 theorems): `realSinhc`, `realSinhc_zero`, `realSinhc_of_ne_zero`, `realSinhc_eq_dslope`, `continuous_realSinhc`, `realSinhc_neg`, `realSinhc_even`, `realSinhc_pos`, `realSinhc_ne_zero`, `realSinhc_two_mul`, `sinh_lt_mul_cosh`, `realSinhc_lt_cosh_of_pos`, `realSinhc_le_cosh`, `realSinhc_lt_cosh_iff`, `tanhDiv`, `tanhDiv_zero`, `tanhDiv_of_ne_zero`, `tanhDiv_neg`, `tanhDiv_even`, `continuous_tanhDiv`, `tanhDiv_pos`, `tanhDiv_ne_zero`, `tanhDiv_le_one`, `tanhDiv_lt_one_iff`, `tanhDiv_le_inv_of_pos`, `hasDerivAt_tanh`, `tanhDiv_eq_dslope`, `tanh_nonneg_of_nonneg`, `tanh_pos_of_pos`, `tanh_lt_self_of_pos`, `tanh_le_self_of_nonneg`, `tanh_cubic_lower`, `activationOdds`, `activationProbability`, `activationOdds_zero`, `activationProbability_zero`, `activationProbability_of_ne_zero`, `activationOdds_neg`, `activationOdds_even`, `activationProbability_neg`, `activationProbability_even`, `continuous_activationOdds`, `continuous_activationProbability`, `one_add_activationOdds`, `one_add_activationOdds_pos`, `activationOdds_of_ne_zero`, `activationOdds_nonneg`, `activationOdds_pos_iff`, `tanhDiv_mul_one_add_activationOdds`, `activationProbability_mul_one_add_activationOdds`, `activationProbability_eq_odds_div`, `one_sub_activationProbability`, `one_sub_activationProbability_pos`, `one_sub_activationProbability_le_one`, `one_sub_activationProbability_le_inv_of_pos`, `one_sub_activationProbability_le_min_one_inv_of_pos`, `activationProbability_nonneg`, `activationProbability_pos_iff`, `activationProbability_lt_one`, `activationProbability_le_sq_div_three_of_nonneg`, `activationProbability_le_sq_div_three`, and `activationProbability_le_min_one_sq_div_three`. The module totalizes `sinh(x)/x` and `tanh(x)/x` at the origin, proves continuity, evenness, strict positivity, the double-angle law, the exact comparison with `cosh`, elementary real-`tanh` estimates, the identification of `tanhDiv` with the divided slope of `tanh`, and denominator-free and quotient forms of the odds/probability bridge. Globally, `0 ≤ activationProbability x < 1`, positivity is equivalent to `x ≠ 0`, and `activationProbability x ≤ min 1 (x^2/3)`; for `x>0`, its complement is positive and bounded by `min 1 x⁻¹`. This is a real totalized-kernel API, not an identification with the complex sinc functions, an analyticity theorem, or an all-order Taylor-series theorem. |
| Square-summable activation-series bounds | `FabiusFunction.ActivationSeries` | Exhaustive public surface (three theorems): `activationProbability_mul_le_quadratic`, `summable_activationProbability_mul_of_summable_sq`, and `tsum_activationProbability_mul_le`. The first packages the sharp one-coordinate rescaling bound. For an arbitrary index type and every real family `w` with summable squares, the series `∑' i, activationProbability (w i * t)` is genuinely summable for every real `t` and is at most `(t^2/3) * ∑' i, w i^2`. This is a deterministic analytic statement and requires no countability, sign, or probability-law hypothesis beyond what `Summable` itself entails. |
| Sharp local activation asymptotics | `FabiusFunction.ActivationAsymptotics` | Exhaustive public surface (two theorems): `tendsto_activationProbability_div_sq` and `tendsto_activationProbability_mul_div_sq`. The first proves the punctured-neighborhood limit `activationProbability x / x^2 → 1/3` as `x → 0`, so the coefficient in the global bound `activationProbability x ≤ x^2/3` is optimal. The second transports it through every real dilation: `activationProbability (a*x) / x^2 → a^2/3`, including `a=0`. The base proof uses one l'Hopital step and the continuous totalization `tanhDiv 0 = 1`; neither theorem asserts a higher Taylor coefficient or remainder. |
| Finite activation Taylor jet | `FabiusFunction.ActivationTaylor` | Exhaustive public surface (three theorems): `tanh_sub_taylor_nine_isBigO`, `activationProbability_sub_taylor_eight_isBigO`, and `activationProbability_sub_taylor_eight_isBigO_pow`. The first proves `tanh x = x - x^3/3 + 2*x^5/15 - 17*x^7/315 + 62*x^9/2835 + O(‖x‖^11)` at the origin. Dividing its removable remainder by `x` gives the exact report expansion `activationProbability x = x^2/3 - 2*x^4/15 + 17*x^6/315 - 62*x^8/2835 + O(‖x‖^10)`, together with a literal `O(x^10)` wrapper. The proof obtains the derivative table structurally from `tanh * cosh = sinh` and `iteratedDeriv_mul`, then invokes the analytic power-series remainder theorem; it does not claim the all-order Bernoulli series or its radius of convergence. |
| Sharp square-summable activation-series asymptotics | `FabiusFunction.ActivationSeriesAsymptotics` | Exhaustive public surface (one theorem): `tendsto_tsum_activationProbability_mul_div_sq`. For every square-summable real family on an arbitrary index type, `(∑' i, activationProbability (w i*t))/t^2` tends through nonzero `t` to `(∑' i, w i^2)/3`. Tannery's theorem justifies the interchange of limit and `tsum`, with the global quadratic estimate supplying exactly the limiting summable majorant; consequently the preceding global series budget is coefficient-sharp. |
| Geometric and dyadic effective activation dimensions | `FabiusFunction.GeometricActivationDimension` | Exhaustive public surface (two definitions and 30 theorems): `activationProbability_pow_mul_le`, `summable_activationProbability_pow_mul`, `tsum_activationProbability_pow_mul_le`, `hasSum_normalizedGeometricWeight_sq`, `geometricActivationDimension`, `summable_geometricActivationDimension_terms`, `geometricActivationDimension_zero`, `geometricActivationDimension_nonneg`, `geometricActivationDimension_even`, `geometricActivationDimension_refinement`, `geometricActivationDimension_sub_refinement`, `geometricActivationDimension_zero_ratio`, `activationProbability_scale_le_geometricActivationDimension`, `geometricActivationDimension_pos_iff`, `geometricActivationDimension_le_quadratic`, `geometricActivationDimension_le_normalized_quadratic`, `geometricActivationDimension_eq_sum_range_add`, `geometricActivationDimension_tail_le`, `sum_range_activationProbability_le_geometricActivationDimension`, `geometricActivationDimension_le_sum_range_add_tail`, `dyadicEffectiveDimension`, `dyadicEffectiveDimension_eq_tsum`, `dyadicEffectiveDimension_zero`, `dyadicEffectiveDimension_nonneg`, `dyadicEffectiveDimension_even`, `dyadicEffectiveDimension_half_refinement`, `dyadicEffectiveDimension_two_mul`, `dyadicEffectiveDimension_refinement`, `dyadicEffectiveDimension_pos_iff`, `dyadicEffectiveDimension_le_sq_div_nine`, `dyadicEffectiveDimension_eq_sum_range_add`, and `dyadicEffectiveDimension_tail_le`. The `HasSum` theorem isolates the exact squared mass `(1-q)/(1+q)` of the normalized geometric weights and supplies both convergence and the evaluated `tsum`. For every real `q` with `|q|<1`, the sampled activation series is summable, is bounded by the normalized quadratic majorant `(1-q)*t^2/(3*(1+q))`, is positive exactly off the origin, and satisfies one-step and arbitrary finite-prefix refinements with certified two-sided enclosures; the next module proves that this quadratic coefficient is exact. At `q=1/2`, Lean uses report digit `j=n+1` and proves the refinement, global bound, and tail certificate for the literal object `dyadicEffectiveDimension`: `dyadicEffectiveDimension (2*t) - dyadicEffectiveDimension t = activationProbability t`, `dyadicEffectiveDimension t ≤ t^2/9`, and `dyadicEffectiveDimension ((1/2)^N*t) ≤ t^2/(9*4^N)`. The definition is total in `q` because a nonsummable real `tsum` is zero. The API proves a uniform, nondegenerate convergence theory under `|q|<1`; outside that range no general summability is promised, although degenerate parameter choices may still converge. Negative `q` is included in the deterministic activation identities. The separate geometric-uniform pushforward remains a probability law under its own hypotheses, including negative ratios, but the frontier report's positive-weight active-count interpretation assumes `0<q<1`; no identity with an active-count expectation is asserted here. |
| Sharp geometric and dyadic activation asymptotics | `FabiusFunction.GeometricActivationAsymptotics` | Exhaustive public surface (two theorems): `tendsto_geometricActivationDimension_div_sq` and `tendsto_dyadicEffectiveDimension_div_sq`. For every real `q` with `|q|<1`, `geometricActivationDimension q t / t^2` tends through nonzero `t` to `(1-q)/(3*(1+q))`; at `q=1/2`, `dyadicEffectiveDimension t / t^2` tends to `1/9`. Thus the global quadratic bounds in the preceding module are sharp on the full analytic range, including negative `q`; the negative-ratio result remains algebraic rather than a probability-law extension. |
| Exact topological support of weighted-uniform laws | `FabiusFunction.WeightedUniformSupport` | `isOpenPosMeasure_infinitePi`, `uniformProduct_isOpenPosMeasure`, `support_map_eq_closure_range_of_continuous`, `weightedUniformSeries_constCoordinates`, `weightedUniformDistribution_support_eq_range`, `range_weightedUniformSeries_eq_Icc_min_max`, `weightedUniformDistribution_support_eq_Icc_min_max`, `range_weightedUniformSeries_eq_Icc`, `weightedUniformDistribution_support_eq_Icc`, `weightedUniformDistribution_support_eq_unitInterval` |
| Continuous CDF calculus for atomless real probability laws | `FabiusFunction.ContinuousCDF` | `continuous_cdf_of_nullSingleton`, `cdf_reflection_sub`, `measure_eq_withDensity_of_cdf_hasDerivAt`; the last theorem turns an everywhere pointwise CDF derivative into the exact Lebesgue `withDensity` representation without assuming derivative continuity or prior absolute continuity, because CDF monotonicity supplies nonnegativity and local integrability |
| Contractive affine independent-copy probability laws | `FabiusFunction.AffineIndependentCopy` | At compiled checkpoint `d312c0603`: `affineIndependentCopyLaw`, `affineIndependentCopyLaw_isProbabilityMeasure`, `affineIndependentCopyLaw_eq_map_prod`, `charFun_affineIndependentCopyLaw`, `charFun_eq_mul_charFun_of_affineIndependentCopy_fixedPoint`, `charFun_iterate_of_affineIndependentCopy_fixedPoint`, `eq_of_charFun_affine_recurrence`, `affineIndependentCopyLaw_fixedPoint_unique`, `affineIndependentCopy_map_fixedPoint_unique`; the digit space is an arbitrary measurable space and the target is a second-countable Borel real inner-product space; a measurable digit map and probability digit/candidate laws suffice for the operator-level fixed-point API, while completeness is assumed only by the characteristic-recurrence and two fixed-point uniqueness theorems; uniqueness requires `|q| < 1`, includes `q = 0` and negative `q`, and uses no support, density, or moment hypothesis |
| Geometrically weighted uniform laws and their characterization | `FabiusFunction.GeometricUniformLaw`, `FabiusFunction.GeometricUniformUniqueness` | `geometricUniformWeight`, `hasSum_geometricUniformWeight`, `geometricUniformSeries`, `geometricUniformSeries_split`, `geometricUniformDistribution_selfSimilar`, `geometricUniformDistribution_absolutelyContinuous`, `geometricUniformDistribution_nullSingletonClass`, `geometricUniformDistribution_reflection`, `geometricUniformDistribution_Icc`, `eq_geometricUniformDistribution_of_selfSimilar`; the last theorem characterizes the law among all probability measures satisfying the affine product-map equation whenever `|q| < 1`, including `q = 0` and negative `q`, without support, density, or moment assumptions |
| Fixed half--quarter geometric multisection | `FabiusFunction.GeometricUniformMultisection` | `evenCoordinates`, `oddCoordinates`, `geometricUniformSeries_one_half_multisection`, `geometricUniformDistribution_one_half_multisection`, `geometricUniformDistribution_one_half_conv_one_quarter`; the pointwise normalized series splits exactly as `Y_(1/2)(ω) = (2/3) Y_(1/4)(ω_even) + (1/3) Y_(1/4)(ω_odd)`, and under the product-uniform law the parity processes are independent copies, yielding both the exact product-map law and the convolution of the `2/3`- and `1/3`-scaled quarter laws; this fixed theorem needs no user hypotheses and does not claim general `q`/multisection, MGF or cumulant identities, centered-density formulas, or spectral dissection |
| Geometric tail dictionary and sinc-prefix factorization | `FabiusFunction.GeometricUniformDictionary`, `FabiusFunction.GeometricSincFactorization` | `charFun_geometricUniformDigit`, `charFun_geometricUniformDistribution_prefix`, `charFun_geometricUniformDistribution_prefix_sinc`, `tendsto_prefix_sinc_charFun`, `charFun_weightedSumDistribution_prefix_sinc`, `tendsto_prefix_sinc_charFun_weightedSumDistribution`; the digit formula is unconditional, while for every real `q` with `|q| < 1`, depth `m`, and frequency `t`, the law has the exact residual factorization `φ_q(t) = exp(i(1-q^m)t/2) · ∏_{k<m} sinc((1-q)q^k t/2) · φ_q(q^m t)`, and the phase-bearing prefix without the residual converges pointwise to `φ_q(t)`; this includes `q = 0` and negative `q`, and the final two declarations are the `q = 1/2` weighted-sum wrappers.  `geometric_tail_dictionary_geometricUniform` already supplies finite characteristic-function, MGF, and CGF tail factorizations.  This predecessor module itself remains pointwise; the next row records the named upgrade of the same full prefixes to locally uniform convergence on the real frequency line and uniform convergence on every compact real frequency set. |
| Geometric sinc/Gamma characteristic-function bridge and phase-prefix convergence | `FabiusFunction.GeometricSincCharacteristicFunction` | Exhaustive public surface (zero definitions and four theorems): `charFun_geometricUniformDistribution_eq_phase_mul_geometricSincProduct`, `charFun_geometricUniformDistribution_eq_phase_mul_geometricReciprocalGamma`, `tendstoLocallyUniformly_prefix_sinc_charFun`, and `tendstoUniformlyOn_prefix_sinc_charFun`.  For every real `q` with the sharp hypothesis `|q| < 1`—including `q = 0` and negative `q`—and every real `t`, put `z = (1-q)t/(2π)`.  Then exactly `φ_q(t) = exp(it/2) · geometricSincProduct q z = exp(it/2) · geometricReciprocalGamma q z · geometricReciprocalGamma q (-z)`, with the real parameters cast to `ℂ` in Lean.  Moreover the full prefixes `P_m(t) = exp(i(1-q^m)t/2) · ∏_{k<m} sinc((1-q)q^k t/2)` converge locally uniformly on `ℝ` to `φ_q`, and hence uniformly on every compact `K ⊆ ℝ`.  The Gamma-side row below supplies the named locally uniform complex-variable pure product, pointwise `Multipliable`/`HasProd`, and entireness of `geometricSincProduct`.  No complex-frequency analogue for the full phase-bearing prefixes or uniform-convergence claim on all of `ℝ` is made.  Still absent are general-`q` rapid-decay bounds and Fourier inversion, a separately packaged centered family and MGF wrapper, explicit Bernoulli-cumulant/Bell-moment formulas and asymptotics, further transform formulas, and shape theory. |
| CDF and explicit density of the geometric uniform law | `FabiusFunction.GeometricUniformCDF` | `geometricUniformCDF`, `monotone_geometricUniformCDF`, `geometricUniformCDF_nonneg`, `geometricUniformCDF_le_one`, `measurable_geometricUniformCDF`, `continuous_geometricUniformCDF`, `geometricUniformCDF_reflection`, `geometricUniformCDF_one_half`, `geometricUniformCDF_zero_of_nonpos`, `geometricUniformCDF_one_of_one_le`, `geometricUniformCDF_eq_integral`, `geometricUniformCDF_eq_intervalIntegral`, `geometricUniformDensity`, `geometricUniformDensity_zero`, `geometricUniformDensity_nonpos_of_neg`, `volume_withDensity_geometricUniformDensity_eq_zero_of_nonpos`, `geometricUniformDistribution_ne_withDensity_geometricUniformDensity_of_nonpos`, `geometricUniformCDF_hasDerivAt`, `deriv_geometricUniformCDF`, `continuous_geometricUniformDensity`, `geometricUniformDensity_nonneg`, `geometricUniformDensity_zero_of_nonpos`, `geometricUniformDensity_zero_of_one_le`, `support_geometricUniformDensity_subset_Ioo`, `support_geometricUniformDensity_subset_Icc`, `tsupport_geometricUniformDensity_subset_Icc`, `geometricUniformDensity_hasCompactSupport`, `geometricUniformDensity_reflection`, `geometricUniformDistribution_eq_withDensity`, `contDiff_geometricUniformCDF`, `contDiff_geometricUniformDensity`; continuity and CDF reflection assume `|q| < 1`, exterior CDF values assume `0 ≤ q < 1`, and the conditioning, derivative-density, positive `withDensity`, compact-support, and `C∞` results assume `0 < q < 1`.  The selected total formula is identically zero at `q = 0` and nonpositive for `q < 0`; hence its `ENNReal.ofReal` `withDensity` measure is zero for `q ≤ 0` and cannot equal the probability law when also `|q| < 1`.  A Lean theorem for the paper-level corrected signed-ratio density at negative `q` remains open; the characteristic-function sinc-prefix results are listed separately above. |
| Product-probability and CDF representations | `FabiusFunction.ProbabilityRepresentation` | `weightedCoordinateSum_eq_weightedUniformSeries`, `weightedCoordinateSum_eq_geometricUniformSeries_one_half`, `weightedSumDistribution_eq_geometricUniformDistribution_one_half`, `ae_weightedSumDistribution_mem_Icc`, `weightedSumDistribution_restrict_Icc`, `weightedSumCDF_eq_geometricUniformCDF_one_half`, `weightedSumCDF_eq_fabiusReal`, `geometricUniformCDF_one_half_eq_fabiusReal`, `geometricUniformDensity_one_half_eq_rvachevUp`, `fabiusReal_eq_weightedSum_probability`, `rvachevUp_eq_weightedSumCDF`, `rvachevUp_eq_weightedSum_probability_global`; the dyadic smoothing, continuity, exterior-value, and reflection proofs route through the half-base geometric CDF API |
| Generic finite moment functionals and Hankel Gram forms | `FabiusFunction.FiniteMomentGram` | `momentFunctional`, `momentFunctional_of_linearMap`, `momentFunctional_map`, `momentPairing`, `momentHankelMatrix`, `momentHankelMatrix_succ_submatrix`, `momentHankelDet`, `map_momentHankelDet`, `finiteMomentPairing_toMatrix`, `finiteMomentPairing_nondegenerate_iff`; this measure-free layer works over the stated semiring, commutative-ring, and integral-domain hypotheses and by itself asserts no positivity |
| Generic fraction-free and normalized Gram--Stieltjes polynomials | `FabiusFunction.GramStieltjes` | `gramStieltjesNumerator`, `momentPairing_gramStieltjesNumerator_eq_coeff_mul_det`, `momentPairing_gramStieltjesNumerator_self`, `gramStieltjesPolynomial`, `gramStieltjesPolynomial_isMonicOfDegree`, `momentPairing_gramStieltjesPolynomial_eq_zero`, `eq_gramStieltjesPolynomial_of_isMonicOfDegree_of_orthogonal`, `momentPairing_gramStieltjesPolynomial_self`; the fraction-free construction is over a commutative ring, while field normalization and uniqueness assume the displayed Hankel minor is nonzero |
| Generic finite Jacobi coefficients and three-term recurrence | `FabiusFunction.FiniteMomentJacobi` | `momentPairing_X_mul_left`, `gramStieltjesNorm`, `gramStieltjesJacobiDiagonal`, `gramStieltjesJacobiSubdiagonal`, `gramStieltjesJacobiSubdiagonal_eq_det_ratio`, `gramStieltjesPolynomial_three_term_zero`, `gramStieltjesPolynomial_three_term`; over a field, a nonzero first Hankel minor gives the degree-zero base equation and three consecutive nonzero Hankel minors give every higher finite recurrence, with no measure, positivity, root, quadrature, continued-fraction, or convergence assumption |
| Polynomial-basis moment Gram determinants | `FabiusFunction.PolynomialMomentGramDeterminant` | Exhaustive public inventory: two definitions, `polynomialCoefficientMatrix` and `polynomialMomentGramMatrix`; and seven theorems, `polynomialCoefficientMatrix_apply`, `polynomialMomentGramMatrix_apply`, `polynomialMomentGramMatrix_eq_transpose_mul_hankel_mul`, `polynomialMomentGramMatrix_det_eq_coefficient_det_sq_mul`, `polynomialCoefficientMatrix_det_eq_prod_coeff`, `polynomialMomentGramMatrix_det_eq_prod_coeff_sq_mul`, and `gramStieltjesJacobiSubdiagonal_eq_polynomialMomentGramMatrix_det_ratio`.  For a family with `natDegree (p k) ≤ k`, its coefficient matrix `C` is upper triangular and direct bilinear expansion gives `G = Cᵀ H C`; determinant multiplicativity and the diagonal product give `det G = (∏ k, coeff (p k) k)^2 det H`, and a nonzero diagonal transports the zero-based Jacobi subdiagonal to the corresponding Gram-determinant cross-ratio.  No Hankel-nonvanishing hypothesis is imposed on that last Lean equality: division in a field is total, so if the middle Hankel determinant is zero then both cross-ratios are zero; that singular case is not a genuine nonsingular Jacobi recurrence.  The coefficient matrix and its entry formula are semiring-level; the Gram matrix, its entry formula, and the congruence are commutative-semiring-level; determinant identities are commutative-ring-level; and the quotient identity is field-level.  This generic module alone asserts no measure, positivity, orthogonality, entry rationality, or Wigner datum.  The downstream Gaunt and closed-form leaves provide the finite rational entry formulas and the total squared zero-row integer-index datum.  Signed `3j` phase, half-integer or nonzero magnetic indices, orthogonality, recoupling, Christoffel reconstruction, and infinite Jacobi theory remain outside the current surface. |
| Scalar naturality of finite Gram--Stieltjes and Jacobi data | `FabiusFunction.GramStieltjesNaturality` | Exhaustive public inventory: zero definitions and six theorems, `momentPairing_map`, `map_gramStieltjesNumerator`, `map_gramStieltjesPolynomial`, `map_gramStieltjesNorm`, `map_gramStieltjesJacobiDiagonal`, and `map_gramStieltjesJacobiSubdiagonal`.  The pairing theorem is over commutative semirings, the fraction-free numerator theorem over commutative rings, and the normalized polynomial, norm, and Jacobi theorems over fields.  This is finite scalar base change only, with no measure, positivity, computation, or convergence claim. |
| Exact all-degree rational Jacobi system of the Rvachev up law | `FabiusFunction.RvachevRationalJacobi` | Exhaustive public inventory: four definitions, `rvachevHankelDetRat`, `rvachevOrthoPolynomialRat`, `rvachevOrthoNormRat`, and `rvachevJacobiSubdiagonalRat`; and thirteen theorems, `upMoment_eq_rvachevRawMomentRat_cast`, `rvachevHankelDetRat_cast`, `rvachevHankelDetRat_pos`, `rvachevOrthoPolynomialRat_cast`, `rvachevOrthoPolynomialRat_isMonicOfDegree`, `momentPairing_rvachevOrthoPolynomialRat_eq_zero`, `rvachevOrthoNormRat_cast`, `rvachevOrthoNormRat_pos`, `gramStieltjesJacobiDiagonal_rvachevRawMomentRat_eq_zero`, `rvachevJacobiSubdiagonalRat_cast`, `rvachevJacobiSubdiagonalRat_pos`, `rvachevJacobiSubdiagonalRat_eq_det_ratio`, and `rvachevOrthoPolynomialRat_three_term`.  These noncomputable finite definitions give positive rational Hankel determinants, monic orthogonal polynomials, positive norms, zero diagonal, positive subdiagonals, cast comparison with every analytic Fabius representative, the determinant cross-ratio, and the exact rational recurrence in every degree.  The zero-based `rvachevJacobiSubdiagonalRat n` is the conventional coefficient `beta_(n+1)`.  This module itself remains noncomputable and is not a native evaluator; the downstream executable rational Legendre Gram/value modules now supply the explicit report values `H_4` and `beta_4`.  Root/quadrature, Christoffel, continued-fraction, Padé, and asymptotic results remain outside this layer. |
| Executable rational ordinary Legendre polynomials | `FabiusFunction.LegendrePolynomialRational` | Exhaustive public inventory: two definitions, `legendrePolynomialCoeffRat` and `legendrePolynomialRat`; and six theorems, `legendrePolynomialRat_cast`, `coeff_legendrePolynomialRat`, `natDegree_legendrePolynomialRat`, `coeff_legendrePolynomialRat_self`, `coeff_legendrePolynomialRat_self_ne_zero`, and `coeff_legendrePolynomialRat_self_div_succ`.  The scalar coefficient function is an executable finite sum, while the polynomial wrapper is noncomputable; all public statements are unconditional in their natural indices and identify its real cast, every coefficient, exact degree, top coefficient, nonvanishing, and consecutive top-coefficient quotient.  Two private construction helpers are excluded. |
| Legendre Gram/Hankel determinant bridge for the up law | `FabiusFunction.FabiusLegendreHankelDeterminant` | Exhaustive public inventory: two definitions, `upLegendreGramMatrix` and `upLegendreGramDet`; and seven theorems, `upLegendreGramMatrix_apply_eq_integral`, `upLegendreGramDet_eq_prod_leadingCoeff_sq_mul_hankelDet`, `upLegendreGramDet_zero`, `upLegendreGramDet_pos`, `coeff_legendrePolynomial_self_div_succ`, `gramStieltjesJacobiSubdiagonal_upMoment_eq_upLegendreGramDet_ratio`, and `rvachevJacobiSubdiagonalRat_cast_eq_upLegendreGramDet_ratio`.  Writing `D_n` for the determinant of the first `n` ordinary Legendre polynomials in the up-moment pairing and `L_j = 2^(-j) * choose (2*j) j`, the determinant identity `D_n = (∏ j<n, L_j^2) * hankelDet F n`, the empty `0×0` convention `D_0 = 1`, the leading-coefficient quotient, and the real Gram cross-ratio hold for every `F : BoundedFabius`.  Identifying an entry with an integral, strict positivity, and the rational-cast bridge additionally require `IsFabius F`.  Its zero-based index `n` is the conventional `beta_(n+1)` and satisfies `beta_(n+1) = ((n+1)/(2*n+1))^2 * D_(n+2) * D_n / D_(n+1)^2`; in the arbitrary-`BoundedFabius` real theorem this is the same totalized-division equality, while `IsFabius` supplies nonvanishing through positivity and makes it a genuine Jacobi formula.  This module itself does not give a Gaunt or Wigner-square entry expansion or entrywise rationality by that route; the downstream Gaunt and closed-form modules below do.  Signed `3j` phase, half-integer or nonzero magnetic indices, recoupling, Christoffel reconstruction, and an infinite product remain outside the development.  The unrelated `rvachevTranslateGram` is the Gram kernel of shifted-up atoms under unweighted interval integration, not this polynomial-basis moment Gram matrix. |
| Executable rational Legendre Gram data for the up law | `FabiusFunction.FabiusLegendreRationalGram` | Exhaustive public inventory: three executable definitions, `rvachevLegendreGramEntryRat`, `rvachevLegendreGramMatrixRat`, and `rvachevLegendreGramDetRat`; and eleven theorems, `rvachevLegendreGramEntryRat_eq_momentPairing`, `rvachevLegendreGramMatrixRat_apply`, `rvachevLegendreGramMatrixRat_eq_polynomialMomentGramMatrix`, `rvachevLegendreGramEntryRat_cast`, `rvachevLegendreGramMatrixRat_cast`, `rvachevLegendreGramDetRat_cast`, `rvachevLegendreGramDetRat_eq_prod_leadingCoeff_sq_mul_rvachevHankelDetRat`, `rvachevLegendreGramDetRat_zero`, `rvachevLegendreGramDetRat_pos`, `rvachevOrthoNormRat_eq_rvachevLegendreGramDetRat_ratio`, and `rvachevJacobiSubdiagonalRat_eq_rvachevLegendreGramDetRat_ratio`.  The entry is a bounded double sum of executable rational Legendre coefficients and `rvachevRawMomentRat`; its finite matrix and determinant agree with the abstract polynomial moment Gram objects, and their real casts agree with the up-law entry, matrix, and determinant for every `F : BoundedFabius` satisfying `IsFabius F`.  Over `ℚ`, the determinant is the rational Hankel determinant times the product of squared Legendre leading coefficients, is one in order zero and strictly positive in every order; exact rational Gram-determinant ratios recover `rvachevOrthoNormRat n` and the zero-based `rvachevJacobiSubdiagonalRat n = beta_(n+1)`, with prefactor `((n+1)/(2*n+1))^2` in the latter.  This module closes executable rational coefficient/entry/matrix/determinant data and cast bridges.  The downstream Gaunt modules supply its finite Gaunt entry expansions, and `FabiusLegendreGauntClosedForm` supplies the rational entry/matrix and real matrix sums against the total squared zero-row integer datum.  This layer itself makes no such identification.  Signed `3j` phase, half-integer or nonzero magnetic indices, recoupling, Christoffel reconstruction, root or quadrature theory, an infinite Jacobi product/continued fraction, and asymptotics remain outside the development. |
| Executable rational Legendre Gaunt coefficients and finite product linearization | `FabiusFunction.LegendreGaunt` | Exhaustive public inventory: four definitions, `legendreLebesgueMomentRat`, `legendreGauntRat`, `legendreGaunt`, and `legendreProductLinearizationCoeffRat`; and twelve theorems, `legendreLebesgueMomentRat_even`, `legendreLebesgueMomentRat_odd`, `legendreLebesgueMomentRat_cast`, `legendreGauntRat_eq_momentFunctional`, `legendreGauntRat_cast`, `legendreGauntRat_swap_left`, `legendreGauntRat_swap_right`, `legendrePolynomial_mul_eq_sum_gaunt`, `legendrePolynomialRat_mul_eq_sum_gaunt`, `legendreGauntRat_eq_zero_of_odd_sum`, `legendreGauntRat_eq_zero_of_add_lt`, and `legendreGauntRat_eq_zero_of_triangle_violation`.  For every `n : ℕ`, `legendreLebesgueMomentRat n` is `2/(n+1)` at even `n` and zero at odd `n`, and its real cast is `∫ x in (-1)..1, x^n`.  For every `i j k : ℕ`, `legendreGauntRat i j k` is the bounded triple coefficient–moment sum for `P_i P_j P_k`, `legendreGaunt i j k = ∫ x in (-1)..1, P_i(x) P_j(x) P_k(x)`, and `legendreProductLinearizationCoeffRat i j k = ((2*k+1)/2) * legendreGauntRat i j k`.  The rational sum equals the moment functional and casts to the real integral, is invariant under the displayed first-two and last-two swaps, and gives the exact real and rational identities `P_i P_j = ∑ k ∈ range(i+j+1), legendreProductLinearizationCoeffRat i j k • P_k`.  The only hypotheses are `Odd (i+j+k)` for the parity zero, `i+j<k` for the one-sided degree zero, and `i+j<k ∨ i+k<j ∨ j+k<i` for the triangle-violation zero; all definitions and other theorems are total at arbitrary natural indices.  This module itself proves only the necessary support zeros and makes no converse support, Wigner-square, factorial, positivity, or asymptotic claim; the next closed-form leaf proves the total squared zero-row integer-index case and sharpens those support statements. |
| Total zero-row Wigner-square Gaunt closed form, sharp support, positivity, and product coefficients | `FabiusFunction.LegendreGauntClosedForm` | Exhaustive public inventory: two definitions, `legendreGauntAdmissible` and `legendreWignerThreeJZeroSqRat`; and twenty-five theorems, `legendreGauntAdmissible_iff_exists_pairwise_add`, `legendreGauntAdmissible_pairwise_add`, `legendreWignerThreeJZeroSqRat_pairwise_add`, `legendreWignerThreeJZeroSqRat_pairwise_add_factorial`, `legendreWignerThreeJZeroSqRat_eq_factorial_of_halfSum`, `legendreWignerThreeJZeroSqRat_eq_zero_of_not_admissible`, `legendreGauntRat_add_boundary`, `legendreGauntRat_add_boundary_eq_two_mul_wignerThreeJZeroSqRat`, `legendreGauntRat_zero_left`, `legendreGauntRat_zero_left_eq_two_mul_wignerThreeJZeroSqRat`, `legendreGauntRat_pairwise_add_eq_two_mul_wignerThreeJZeroSqRat`, `legendreGauntRat_eq_zero_of_not_admissible`, `legendreGauntRat_eq_two_mul_wignerThreeJZeroSqRat`, `legendreGaunt_eq_two_mul_wignerThreeJZeroSqRat`, `legendreWignerThreeJZeroSqRat_pos_iff_admissible`, `legendreWignerThreeJZeroSqRat_nonneg`, `legendreWignerThreeJZeroSqRat_eq_zero_iff_not_admissible`, `legendreGauntRat_pos_iff_admissible`, `legendreGauntRat_eq_zero_iff_not_admissible`, `legendreGaunt_pos_iff_admissible`, `legendreGaunt_eq_zero_iff_not_admissible`, `legendreGauntRat_nonneg`, `legendreGaunt_nonneg`, `legendreProductLinearizationCoeffRat_eq_mul_wignerThreeJZeroSqRat`, and `legendreProductLinearizationCoeffRat_pos_iff_admissible`.  Admissibility is even total degree plus the three weak triangle inequalities, equivalently a triple of pairwise-sum coordinates.  The total rational square datum is zero off this support and has both central-binomial and factorial forms on it; the half-sum factorial theorem assumes the displayed half-sum identity and domination of all three indices.  At arbitrary natural indices the rational and real Gaunt coefficients are twice this datum, are positive exactly on the admissible support and otherwise zero, and are nonnegative; the coefficient of `P_k` in `P_i P_j` is `(2*k+1)` times the datum and has the same sharp positivity support.  This is only an integer-index, zero-magnetic-row square datum defined by its rational formula: no signed symbol or phase convention, half-integer indices, nonzero magnetic indices, general `3j`/`6j`/`9j` symbols, Wigner orthogonality, or recoupling identity is supplied. |
| Finite Gaunt sums for rational and real up-law Legendre Gram entries | `FabiusFunction.FabiusLegendreGaunt` | Exhaustive public inventory: one definition, `canonicalRvachevFullLegendreCoefficientRat`; and eight theorems, `canonicalRvachevFullLegendreCoefficientRat_even`, `canonicalRvachevFullLegendreCoefficientRat_odd`, `canonicalRvachevFullLegendreCoefficientRat_cast`, `canonicalRvachevFullLegendreCoefficientRat_eq_normalized_moment`, `rvachevLegendreGramEntryRat_eq_sum_full_gaunt`, `rvachevLegendreGramEntryRat_eq_sum_gaunt`, `rvachevLegendreGramMatrixRat_apply_eq_sum_gaunt`, and `upLegendreGramMatrix_apply_eq_sum_gaunt`.  The full coefficient is `canonicalRvachevLegendreCoefficientRat (k/2)` when `2 ∣ k` and zero otherwise, hence it restricts to the canonical coefficient at `2*n` and vanishes at `2*n+1`.  Unconditionally in `k`, it equals `((2*k+1)/2) * momentFunctional rvachevRawMomentRat (legendrePolynomialRat k)`.  For all natural `i,j`, the rational Gram entry is both `∑ k ∈ range(i+j+1), canonicalRvachevFullLegendreCoefficientRat k * legendreGauntRat i j k` and the reindexed even sum `∑ r ∈ range((i+j)/2+1), canonicalRvachevLegendreCoefficientRat r * legendreGauntRat i j (2*r)`; the latter is also the exact entry formula for every `i j : Fin n`.  Only the cast theorem and the real matrix formula require `F : BoundedFabius` and `hF : IsFabius F`; then the full rational coefficient casts to `rvachevFullLegendreCoefficient F k`, and the real entry is the same even finite sum with `rvachevLegendreCoefficient F r` and `legendreGaunt`.  This module itself proves finite polynomial and finite Gaunt-sum identities; the next leaf substitutes the total squared zero-row integer datum.  It does not choose a signed `3j` phase or treat half-integer/nonzero magnetic indices, orthogonality, recoupling, infinite Legendre-series interchange, Christoffel reconstruction, named values for the displayed `G_3` entries, or a new asymptotic result. |
| Finite zero-row Wigner-square sums for rational Rvachev and real up-law Legendre Gram entries | `FabiusFunction.FabiusLegendreGauntClosedForm` | Exhaustive public inventory: zero definitions and exactly three theorems, `rvachevLegendreGramEntryRat_eq_two_mul_sum_wignerThreeJZeroSqRat`, `rvachevLegendreGramMatrixRat_apply_eq_two_mul_sum_wignerThreeJZeroSqRat`, and `upLegendreGramMatrix_apply_eq_two_mul_sum_wignerThreeJZeroSqRat`.  The first gives every executable rational entry as twice the finite sum of `canonicalRvachevLegendreCoefficientRat r` times `legendreWignerThreeJZeroSqRat i j (2*r)`; the second is its entrywise finite rational matrix form.  For `F : BoundedFabius` with `IsFabius F`, the third gives the real up-law matrix entry as twice the corresponding finite sum with `rvachevLegendreCoefficient F r` and the real cast of that datum.  These are finite rational entry/matrix and real matrix sums against the total squared zero-row integer datum.  No signed `3j` phase, half-integer or nonzero magnetic index, general Wigner-symbol API, orthogonality, or recoupling theorem is claimed. |
| Exact low-order rational Legendre Gram and Jacobi values | `FabiusFunction.FabiusLegendreRationalGramValues` | Exhaustive public inventory: zero definitions and eleven theorems, `moment_four`, `rvachevLegendreGramDetRat_one`, `rvachevLegendreGramDetRat_two`, `rvachevLegendreGramDetRat_three`, `rvachevLegendreGramDetRat_four`, `rvachevLegendreGramDetRat_five`, `rvachevOrthoNormRat_four`, `rvachevJacobiSubdiagonalRat_three`, `hankelRatio_four`, `integral_sq_upOrthoPolynomial_four`, and `hankelRatio_four_div_three`.  The first theorem gives the raw eighth moment `132809/32531625`; the five determinant theorems give orders one through five as `1`, `1/9`, `8/2025`, `39616/602791875`, and `16544275456/27453718922765625`.  The rational norm is `H_4 = rvachevOrthoNormRat 4 = 26727424/55791736875`, while the zero-based index-three subdiagonal is the conventional `beta_4 = rvachevJacobiSubdiagonalRat 3 = 835232/4640643`.  The rational computations have no analytic input; each of `hankelRatio_four`, `integral_sq_upOrthoPolynomial_four`, and `hankelRatio_four_div_three` transports these values to a real squared norm, squared orthogonal-polynomial integral, or consecutive-ratio quotient only for `F : BoundedFabius` with `IsFabius F`.  The separate Gaunt and closed-form modules close the finite entry and total zero-row square expansions, but this values leaf supplies no named evaluation of the displayed `G_3` entries.  Signed `3j` phase, half-integer or nonzero magnetic indices, recoupling, Christoffel reconstruction, roots or quadrature, infinite Jacobi products/continued fractions, and asymptotics remain open. |
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
| Pairwise partition defects, sharp fixed-block bound, equality profiles, and first positive shell | `FabiusFunction.PartitionDefect` | Exhaustive public inventory: three definitions, `pairSum`, `blockPairDefect`, and `partitionDefect`, plus 33 theorems.  Unconditional group: `pairSum_nil`, `pairSum_cons`, `pairSum_one`, `pairSum_add`, `pairSum_congr`, `pairSum_map`, `choose_add_two`, `choose_list_sum_two`, `partitionDefect_nonneg`, `pairSum_add_eq`, `pairSum_map_add_eq`, `partitionDefect_eq_linear_add_pairwise_excess`, `pairSum_eq_zero_iff_pairwise`.  Positive-pair group: `blockPairDefect_eq_mul_sub_one`, `blockPairDefect_eq_zero_iff`, `sub_one_mul_sub_one_eq_zero_iff`, `add_sub_one_le_mul_of_pos`, `mul_eq_add_sub_one_iff`.  Positive-list group, assuming exactly `∀ x ∈ r, 0 < x`: `partitionDefect_eq_pairSum_mul_sub_one`, `choose_sum_two_eq_choose_length_add_sum_add_partitionDefect`, `partitionDefect_eq_choose_sum_sub_choose_length_sub_sum`, `length_le_sum_of_pos`, `sum_map_sub_one`, `partitionDefect_lower_bound`, `partitionDefect_eq_zero_iff`, `partitionDefect_eq_lower_bound_iff`.  `partitionDefect_fixed_block_bound` and `partitionDefect_fixed_block_eq_iff` additionally assume `r.sum = m` and `r.length = k`; `firstShell_le_fixedBlockProduct` and `fixedBlockProduct_eq_firstShell_iff` assume exactly `2 ≤ k` and `k < m`; `firstShell_le_partitionDefect` and `partitionDefect_eq_firstShell_iff` assume positivity, `r.sum = m`, and `2 ≤ r.length < m`; `partitionDefect_twoBlock_firstShell` assumes `3 ≤ m`.  The list statements concern arbitrary positive lists, not labelled set partitions; one private zero-sum helper is excluded. |
| Complete Bell and moment--cumulant transforms over commutative `ℚ`-algebras | `FabiusFunction.MomentCumulantAlgebra` | `factorialNormalize`, `completeBellPolynomial`, `momentCumulant`, `completeBellPolynomial_succ`, `completeBellPolynomial_momentCumulant`, `momentCumulant_completeBellPolynomial` |
| Euler product transform with natural multiplicities | `FabiusFunction.WeightedEulerTransform` | Exhaustive public surface: `summable_sigma_fin_iff`, `tprod_sigma_fin_eq_tprod_pow`, `tsum_sigma_fin_eq_tsum_nsmul`, `tprod_one_sub_pow_eq_cexp_powerSum`.  The base index is countable.  The summability equivalence assumes a nonnegative real family; the product and sum transfers assume the corresponding sigma-indexed family is multipliable or summable.  The Euler transform assumes `∀ i, ‖f i‖ < 1` and summability of `i ↦ (c i : ℝ) * ‖f i‖`; it is branch-free and asserts no logarithm-of-a-power or principal-log identity. |
| Natural-weight linearity and iterated shift--refinement of generalized Rvachev products | `FabiusFunction.WeightLinearityProducts` | Exhaustive public inventory: zero definitions and nine theorems, `summable_weight_natMul`, `summable_weight_add`, `summable_weight_linearCombination`, `generalizedRvachevProduct_natMul`, `generalizedRvachevProduct_linearCombination`, `shiftExponent_iterate`, `summable_shiftExponent_iterate`, `generalizedRvachevProduct_two_pow_mul`, and `generalizedRvachevProduct_shift_factorization`.  For every natural weight `a : ℕ → ℕ` satisfying exactly `Summable fun h : ℕ => (a h : ℝ) / 2 ^ h`, every `m : ℕ`, and every `z : ℂ`, the all-depth law is `Φ_a(2^m z) = (∏ h ∈ range m, complexSinc(π * (2^(m-h) * z))^(a h)) * Φ_(S^m a)(z)`, where `S^m a(h) = a(h+m)` and the shifted weight remains admissible.  The formula is global in `z`; at `m = 0` its prefix is the empty product and it reduces to reflexivity, so it also includes the zero-depth and zero-frequency boundaries without side conditions.  The linear-combination and finite-difference interfaces use natural coefficients and natural-valued admissible component weights satisfying the displayed Newton reconstruction: they turn every such nonnegative weight identity into a product identity, but do not claim a signed-exponent, analytic-germ, or pole-cancellation theorem. |
| Dyadic order-divisor identifiability for generalized Rvachev products | `FabiusFunction.GeneralizedRvachevIdentifiability` | Exhaustive public inventory: zero definitions and six theorems, `weightSequence_eq_of_weightedScaleMultiplicity_base_pow_eq`, `analyticOrderAt_generalizedRvachevProduct_two_pow`, `exponent_zero_eq_toNat_analyticOrderAt_generalizedRvachevProduct`, `exponent_succ_eq_toNat_analyticOrderAt_generalizedRvachevProduct`, `exponentSequence_eq_of_analyticOrderAt_two_pow_eq`, and `generalizedRvachevProduct_eq_iff`.  The arithmetic theorem works over every additive cancellative commutative weight monoid and every base `b > 1`: equality of weighted multiplicities at all powers `b^n` forces equality of the weight sequences.  For natural exponent sequences satisfying exactly `Summable fun h : ℕ => (a h : ℝ) / 2 ^ h`, the analytic order of `Φ_a` at `2^n` is the inclusive prefix through `n`; `a 0` is read from the order at `1`, later exponents are consecutive differences after `ENat.toNat`, equality of every dyadic order determines the sequence, and two admissible entire products are equal exactly when their exponent sequences are equal.  The identifying datum is the multiplicity/order divisor.  A bare zero set, or merely the product values at those zero points, is insufficient—for example, `a` and `2 • a` have the same zero set—and identifiability from spectral-zeta data, cumulant samples, or a generalized probability law remains open. |
| General-weight Euler--zeta expansion of the generalized sinc product | `FabiusFunction.GeneralizedSincZeta` | Exhaustive public surface: `weightedScaleSeries`, `summable_weightedScaleSeries_real`, `summable_weightedScaleSeries`, `tsum_weighted_div_two_pow_even_pow`, `weighted_sinc_pair_powerSum`, `generalizedRvachevProduct_eq_cexp`.  The series definition is total in the natural weight `a` and natural index `k`.  Every theorem assumes admissibility `Summable fun h : ℕ => (a h : ℝ) / 2 ^ h`; the two scale-series summability results and the weighted scale-collapse theorem additionally require `k ≠ 0`.  The pair power-sum theorem holds for every complex `z` and natural `r`, while the product expansion assumes exactly `‖z‖ < 1`.  This is an analytic exponential expansion, not a principal-log, characteristic-function, probabilistic-cumulant, or support theorem. |
| Alternating Newton Euler--zeta kernel | `FabiusFunction.AlternatingNewtonCumulantKernel` | Exhaustive public surface: `tsum_alternatingNewtonWeight_inv_four_pow`, `weightedScaleSeries_alternatingNewton`, `alternatingNewton_eq_cexp`.  The two kernel evaluations hold for every natural `d` and require `k ≠ 0`; the exponential theorem holds for every natural `d` under exactly `‖z‖ < 1`.  The natural weight exists for every `d`, but agreement with the source volume's signed generalized-binomial convention requires even `d`.  These are analytic identities only, with no characteristic-function, probabilistic-cumulant, or variance interpretation. |
| Nonmonic Hensel lifting and formal implicit roots | `FabiusFunction.ImplicitPowerSeries` | `FormalImplicitRoot.exists_isRoot_sub_mem`, `FormalImplicitRoot.eq_of_isRoot_of_sub_mem`, `FormalImplicitRoot.existsUnique_isRoot_sub_mem`, `PowerSeries.Implicit.existsUnique_isRoot_constantCoeff`, `PowerSeries.Implicit.existsUnique_zeroConstant_root`, `PowerSeries.Implicit.root`, `PowerSeries.Implicit.constantCoeff_root`, `PowerSeries.Implicit.eval_root`, `PowerSeries.Implicit.eq_root`; this is a generic formal-series root engine over complete adic commutative rings and arbitrary commutative coefficient rings, with no concrete inverse-Fabius germ, analytic convergence, plateau localization, flat-remainder, or quantile theorem |
| Quarter Catalan formal germ and dyadic-rescaling bridge | `FabiusFunction.QuarterCatalanGerm` | Exhaustive public surface (two definitions and thirteen theorems): `quarterCatalanCoefficient`, `quarterCatalanCoefficient_zero`, `quarterCatalanCoefficient_succ_eq_report`, `quarterCatalanGermSeries`, `quarterCatalanGermSeries_coeff`, `quarterCatalanGermSeries_coeff_succ`, `quarterCatalanGermSeries_constantCoeff`, `quarterCatalanGermSeries_equation`, `powerSeries_quadratic_injectiveOn_zeroConstant`, `eq_quarterCatalanGermSeries_of_equation`, `existsUnique_quarterCatalanGermSeries`, `dyadicGermTwo_functionalEquation`, `rescale_dyadicGermTwo_eq_quadraticInverse`, `dyadicGermTwo_eq_rescale_quadraticInverse`, `coeff_dyadicGermTwo_succ`.  The explicit Catalan coefficient sequence and its rational power series give the unique zero-constant solution of `D + 4D² = (4/9)X`.  Rescaling the dyadic parameter by `9/4` identifies the distinguished dyadic germ exactly with the Catalan inverse of `X + 4X²`, and every positive coefficient is `(4/9)^(m+1) (-4)^m C_m`.  This module is formal power-series algebra only; the downstream actual-jet bridge is supplied separately. |
| Actual quarter inverse Catalan jet | `FabiusFunction.FabiusInverseQuarterJet` | Exhaustive public surface: `iteratedDeriv_centeredFabiusInv_quarter_eq_quadraticInverse`, `iteratedDeriv_fabiusInv_five_seventy_two_succ`.  For every bounded Fabius solution, the full centered derivative jet at `5/72 = F(1/4)` equals the factorial-scaled coefficient sequence of `QuadraticInverse.inverse 4`; in particular `G^(m+1)(5/72) = (m+1)! (-4)^m C_m`.  This is equality of all jets, not local analytic equality: it neither erases the known nonanalytic flat defect nor proves that defect is nonzero by a named remainder theorem. |
| Finite polynomial integrals from raw moments and formal cumulants | `FabiusFunction.PolynomialExpectationCumulant` | `integral_eval₂_eq_sum_moment`, `integral_eval₂_eq_sum_completeBell_momentCumulant_with_mass_correction`, `integral_eval₂_eq_sum_completeBell_momentCumulant_of_moment_zero_eq_one`, `integral_eval₂_eq_sum_completeBell_momentCumulant` |
| Rvachev raw moments, centered Appell convolution, and triangular injective polynomial deconvolution | `FabiusFunction.RvachevMomentAppell` | Exhaustive public surface: six definitions and exactly 33 theorems, enumerated below in source order.  It packages rational raw and reciprocal moments, rational and real monic Appell families of exact degree, and coefficientwise deconvolution as an injective real linear map preserving the top coefficient, natural degree, and leading coefficient.  Smoothing recovers every polynomial in both the additive and centered `x-y` forms; positive-degree Appell polynomials have Rvachev mean zero.  It proves no analytic reciprocal-MGF or Appell generating-series identity, literal differential-operator expansion, parity theorem for the reciprocal/deconvolution families, or displayed low-coefficient table. |
| Exact shifted-up polynomial synthesis, including arbitrary-phase self-sampling | `FabiusFunction.RvachevPolynomialSynthesis` | Exhaustive public surface: zero definitions and exactly five theorems, `tsum_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`, `normalized_tsum_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`, `sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`, `normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`, and `normalized_tsum_shifted_rvachevDeconvolvedPolynomial_mul_rvachevUp`.  For every nonzero natural mesh `M` and `P.natDegree ≤ v₂(M)`, the first four give global and exact finite `k ∈ (-2M,2M)` synthesis on `[-1,1]`; the fifth reconstructs `P.eval x` for arbitrary real phase and real `x`.  At `M=2^N` this arbitrary-phase layer reaches every degree at most `N`; the adjacent parity-selected layer adds one degree at its selected phases. |
| Parity-selected one-extra-degree Rvachev quadrature and Appell synthesis | `FabiusFunction.RvachevSuperconvergentSynthesis` | Exhaustive public surface: one definition, `IsRvachevSuperconvergentPhase`, and exactly eight theorems, `isRvachevSuperconvergentPhase_two_pow_iff`, `tsum_quarter_monomial_eq_integral_of_even_deg`, `tsum_three_quarters_monomial_eq_integral_of_even_deg`, `tsum_shifted_monomial_eq_integral_superconvergent`, `tsum_shifted_polynomial_eq_integral_superconvergent`, `integral_polynomial_mul_rvachevUp_eq_normalized_tsum_superconvergent`, `normalized_tsum_shifted_rvachevDeconvolvedPolynomial_mul_rvachevUp_superconvergent`, and `normalized_tsum_shifted_rvachevAppellPolynomial_mul_rvachevUp_superconvergent`.  For every nonzero natural mesh `M`, the selected endpoint or quarter phases give exactness through degree `v₂(M)+1`, physical-coordinate quadrature, deconvolved-polynomial reconstruction, and the Appell monomial specialization.  On `M=2^N`, even `N` selects `0,1/2` and odd `N` selects `1/4,3/4`.  This generic-mesh theorem is stronger than the dyadic manuscript form.  The predicate records exact real representatives, not integer translates or a complete classification; no maximality, positivity, or rationality theorem is claimed. |
| Shifted dyadic polynomial comb exactness and normalized self-sampling quadrature | `FabiusFunction.PolynomialCombExactness` | Exhaustive public surface: zero definitions and exactly three theorems, `finite_support_comb`, `tsum_shifted_polynomial_eq_integral`, and `integral_polynomial_mul_rvachevUp_eq_dyadic_tsum`.  For every bounded Fabius solution, natural level `m`, real phase `theta`, and arbitrary real weight function `g`, the sampled product `g(theta+k) * up(2^-m * (theta+k))` has finite integer support.  Every real polynomial `P` with `P.natDegree <= m` therefore satisfies the corresponding whole-line shifted comb identity.  In physical coordinates, for every natural `N`, arbitrary real phase, and `P.natDegree <= N`, its integral against `up` equals `2^-N` times the integer sum over nodes `2^-N * (theta+k)` weighted by `up` at those same nodes.  The statements include level zero; the sums are finite by compact support, and no phase rationality, positivity, infinite-support convergence, or optimal-mesh claim is imposed. |
| Generic finite-node Lagrange--Rvachev decoder, cardinal biorthogonality, and exact interpolation loop | `FabiusFunction.LagrangeRvachevSynthesis` | Exhaustive public surface: two definitions, `lagrangeRvachevDecoder` and `lagrangeRvachevAtomCoefficient`; and seven theorems, `natDegree_lagrangeBasis_le_card_sub_one`, `natDegree_lagrangeInterpolate_le_card_sub_one`, `normalized_sum_Ioo_lagrangeRvachevDecoder_mul_shifted_rvachevUp`, `normalized_sum_Ioo_lagrangeRvachevDecoder_eval_node`, `lagrangeRvachevAtomCoefficient_eq_deconvolved_interpolate`, `sum_Ioo_lagrangeRvachevAtomCoefficient_mul_shifted_rvachevUp`, and `sum_lagrangeRvachevDecoder_eq_one`.  The degree bounds and polynomial reconstruction need no distinct-node hypothesis; componentwise Kronecker biorthogonality requires distinct nodes and evaluation inside `[-1,1]`, while the row-sum theorem additionally requires a nonempty node set.  This closes the reusable generic finite-node synthesis loop, not a geometric Gaussian closed-form decoder, bundled matrix/right-inverse wrapper, or optimal/minimum-variation decoder theorem. |
| Sharp universal composite-mesh exactness and least natural meshes | `FabiusFunction.CompositeMeshSharpness` | Exhaustive public surface: `exists_shift_tsum_shifted_monomial_ne_integral_nat_real`, `rvachevCombExactThrough`, `rvachevCombExactThrough_iff_padicValNat`, `rvachevCombExactThrough_iff_pow_two_dvd`, `rvachevCombExactThrough_two_pow`, `two_pow_le_of_rvachevCombExactThrough`, `isLeast_rvachevCombExactThrough`, `isLeast_rvachevCombExactThrough_even`.  The `IsLeast` results quantify over meshes exact for the whole real polynomial space through the stated degree; they do not assert minimality for an individual Legendre polynomial, a fixed Legendre partial sum, or a target-adapted mesh. |
| Universal endpoint-transfer polynomials and their formal exponential series | `FabiusFunction.EndpointTransferPolynomials` | `endpointTransferPolynomial_succ`, `endpointTransferPolynomial_eq_partitionExpSum`, `endpointTransferSeries_eq_exp_subst`, `aeval_endpointTransferPolynomial`, `map_endpointTransferSeries` |
| Finite base-`b` layer regrouping in multiplicative and additive form | `FabiusFunction.BaseLayerRegrouping` | `filter_dvd_eq_image`, `prod_multiples_eq_prod_filter`, `sum_multiples_eq_sum_filter`, `prod_layers_eq_prod_pow_card`, `sum_layers_eq_sum_nsmul_card`, `card_filter_pow_dvd`, `prod_layers_eq_prod_pow_multiplicity`, `sum_layers_eq_sum_nsmul_multiplicity` |
| Complete homogeneous evaluations, finite formal generating series, Bell/power-sum conversion, fixed-degree asymptotic bounds, denominator-free geometric principal specialization, and a second proof of Gaussian symmetry | `FabiusFunction.CompleteHomogeneous`, `FabiusFunction.CompleteHomogeneousGenerating`, `FabiusFunction.CompleteHomogeneousBell`, `FabiusFunction.CompleteHomogeneousAsymptotics`, `FabiusFunction.GeometricCompleteHomogeneous` | `CompleteHomogeneousBell` exhaustively exports `completeHomogeneousPowerSum`, `completeHomogeneousBellInput`, `completeHomogeneousEvalOn_insert_eq_sum`, `bellComplete_completeHomogeneousBellInput`, `factorialNormalize_completeBellPolynomial_completeHomogeneousBellInput`, and `completeHomogeneousEvalOn_eq_factorialNormalize_completeBellPolynomial`.  Its backbone is division-free over every commutative semiring: `Bell.complete κ n = n! * h_n`; only the normalized `h_n = B_n/n!` form uses a commutative `ℚ`-algebra.  Empty alphabets, repeated or zero entries, zero divisors, positive characteristic, and the zero ring are included.  `GeometricCompleteHomogeneous` exhaustively exports six theorems: `completeHomogeneousEval_geometric`, `completeHomogeneousEval_scaled_geometric`, `completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial`, `completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial_degree`, `gaussianBinomial_add_symm`, and `gaussianBinomial_symm_via_completeHomogeneous`.  The principal specializations and both symmetry proofs need no distinctness, division, cancellation, ordering, topology, or convergence assumptions; the separate generating identities are purely formal, while the asymptotic theorem transfers coordinatewise Big-O through every fixed homogeneous degree. |
| Infinite products at summable scales | `FabiusFunction.ScaledInfiniteProducts` | `summable_norm_scaled_sub_one`, `hasProdUniformlyOn_scaled`, `multipliableUniformlyOn_scaled`, `hasProdLocallyUniformly_scaled`, `multipliableLocallyUniformly_scaled`, `continuous_tprod_scaled`, `differentiable_tprod_scaled`, `differentiable_tprod_scaled_of_eq_one`, `tprod_scaled_ne_zero`, `tprod_scaled_eq_zero_iff`; pointwise deviation summability allows an arbitrary normed-ring target, the compact-uniform API assumes a continuous factor and a complete commutative normed-ring target with a normed unit, local uniformity adds local compactness, holomorphy uses a complete normed complex-algebra target, and zero detection adds a multiplicative norm but needs neither continuity nor local compactness |
| Geometric reciprocal-Gamma products and the dyadic Rvachev bridge | `FabiusFunction.GeometricReciprocalGamma` | Exhaustive public surface (six definitions and 23 theorems, 29 declarations): `shiftedReciprocalGamma`, `shiftedReciprocalGamma_zero`, `shiftedReciprocalGamma_differentiable`, `shiftedReciprocalGamma_sub_one_isBigO`, `shiftedReciprocalGamma_eq_zero_iff`, `shiftedReciprocalGamma_mul_neg`, `summable_norm_qpow`, `geometricReciprocalGamma`, `geometricReciprocalGammaFactors_multipliable`, `geometricReciprocalGamma_differentiable`, `geometricReciprocalGamma_zero`, `geometricReciprocalGamma_mahler`, `geometricReciprocalGamma_eq_zero_iff`, `geometricGamma`, `geometricGamma_meromorphic`, `geometricGamma_mahler`, `geometricSincProduct`, `hasProdLocallyUniformly_geometricSincProduct`, `geometricSincProductFactors_multipliable`, `hasProd_geometricSincProduct`, `geometricReciprocalGamma_mul_neg`, `geometricSincProduct_differentiable`, `dyadicReciprocalGamma`, `dyadicGamma`, `dyadicReciprocalGamma_differentiable`, `dyadicReciprocalGamma_zero`, `geometricSincProduct_inv_two`, `dyadicReciprocalGamma_mul_neg`, `rvachevFourierProduct_eq_one_div_dyadicGamma_mul`.  For complex `q` with `‖q‖ < 1`, including `q = 0`, the sinc factors now have a named locally uniform product, pointwise `Multipliable` and `HasProd` forms, and an entire `geometricSincProduct`; the reciprocal-Gamma product retains its Mahler, zero, meromorphic-inverse, reflection, and dyadic bridge laws.  Normalization at zero is unconditional.  `geometricGamma` and `dyadicGamma` are totalized pointwise inverses, not proved raw Gamma tprods away from poles. |
| Complex infinite `q`-Pochhammer convergence and global geometric-sinc spectral factorization | `FabiusFunction.RvachevPochhammerFactorization` | Exhaustive public surface (one definition and nine theorems): `complexQPochhammerInf`; `complexQPochhammerInf_eq_tprod`, `multipliable_one_sub_mul_pow_complex`, `hasProd_complexQPochhammerInf`, `tendsto_finiteQPochhammerIn_complex`, `summable_norm_sineTerm_qpow_pair`, `geometricSincProduct_eq_tprod_pair`, `geometricSincProduct_eq_tprod_complexQPochhammerInf`, `rvachevFourierProduct_eq_tprod_complexQPochhammerInf`, and `rvachevFourier_eq_tprod_complexQPochhammerInf`.  The symbol is a total complex `tprod`; its named multipliability, product, and finite-prefix convergence theorems require exactly `‖q‖ < 1` and impose no restriction on `a`.  For every complex strict contraction `q` and every `z`, absolute summability of the paired Euler perturbations justifies the scale/zero index exchange and proves `geometricSincProduct q z = ∏' k, complexQPochhammerInf (z^2 / (k+1)^2) (q^2)`, including `q = 0` and individual zero factors.  The last two theorems are the dyadic `q = 1/2`, nome-`1/4` specialization, with the Fourier-transform form assuming exactly a bounded Fabius witness and `IsFabius`.  The separate normal-convergence row supplies local uniformity of this outer product. |
| Locally uniform outer spectral `q`-Pochhammer product | `FabiusFunction.GeometricPochhammerNormalConvergence` | Exhaustive zero-definition/three-theorem surface: `hasProdLocallyUniformly_geometricSincProduct_complexQPochhammerInf`, `hasProdLocallyUniformly_rvachevFourierProduct_complexQPochhammerInf`, and `hasProdLocallyUniformly_rvachevFourier_complexQPochhammerInf`.  For every complex `q` with exactly `‖q‖ < 1`, the outer factors `z ↦ complexQPochhammerInf (z^2/(k+1)^2) (q^2)` have a locally uniform product on all of `ℂ` equal to `geometricSincProduct q`; no nonzero assumption is used, so `q=0` is included.  The last two theorems specialize to the nome `1/4` Rvachev product and to every bounded Fabius witness satisfying `IsFabius`.  This closes only the outer locally-uniform/normal-convergence clause: the compound `qF` spectral theorem remains partial because no declaration packages its centered characteristic-function/MGF form, outside-disk reciprocal formula, pole divisor, or zero--pole exchange. |
| Finite `q`-Pochhammer dissection by residue class | `FabiusFunction.QPochhammerDissection` | Exhaustive public surface (zero definitions and two theorems): `finiteQPochhammerIn_dissection` and `finiteQPochhammerIn_dissection_remainder`.  Over every commutative ring, with no condition on `q`, the first partitions `(a;q)_(r*n)` into the `r` shifted `q^r`-products.  The second treats length `r*n+u` for exactly `u ≤ r`, giving one extra factor to the first `u` residue classes; it includes both `u = 0` and `u = r`. |
| General infinite `q`-Pochhammer convergence, dissection, zero set, and explicit simple-zero derivatives | `FabiusFunction.QPochhammerInfinite` | Exhaustive public surface (one definition and 29 theorems): `qPochhammerInfIn`; `qPochhammerInfIn_eq_tprod`, `summable_norm_mul_pow`, `one_sub_ne_zero_of_norm_lt_one`, `norm_mul_pow_self_lt_one`, `finiteQPochhammerIn_self_ne_zero`, `multipliable_one_sub_mul_pow_of_norm_lt_one`, `hasProd_qPochhammerInfIn`, `tendsto_finiteQPochhammerIn_qPochhammerInfIn`, `qPochhammerInfIn_eq_finite_mul_shift`, `qPochhammerInfIn_succ_shift`, `qPochhammerInfIn_eq_factor_mul`, `qPochhammerInfIn_dissection`, `qPochhammerInfIn_ne_zero`, `qPochhammerInfIn_eq_zero_iff`, `qPochhammerInfIn_self_ne_zero`, `qPochhammerInfIn_eq_tprod_smul`, `summable_norm_pow_of_norm_lt_one`, `isBigO_one_sub_sub_one`, `differentiable_finiteQPochhammerIn`, `qPochhammerInfIn_eq_zero_iff_exists_inv_pow`, `hasProdLocallyUniformly_qPochhammerInfIn`, `continuous_qPochhammerInfIn`, `pow_sq_mul_finiteQPochhammerIn_inv_pow_self`, `differentiable_qPochhammerInfIn`, `hasDerivAt_qPochhammerInfIn_of_mul_pow_eq_one`, `hasDerivAt_qPochhammerInfIn_inv_pow`, `deriv_qPochhammerInfIn_inv_pow_ne_zero`, `deriv_qPochhammerInfIn_ne_zero_of_mul_pow_eq_one`, and `analyticOrderAt_qPochhammerInfIn_of_eq_zero`.  Convergence and concatenation hold in complete normed commutative rings with normalized unit for `‖q‖ < 1`; exact zero detection additionally uses a multiplicative norm.  Locally uniform parameter convergence is proved over complete locally compact normed fields, entireness, explicit nonzero derivatives at both reciprocal-power and raw factor zeros, and analytic order one at every zero over `ℂ`.  This generic symbol is distinct from the pre-existing `complexQPochhammerInf`; no named equality bridge between the two definitions or joint holomorphy in `(a,q)` is claimed. |
| Entire fixed-nome complex `q`-Pochhammer symbol, exact zero lattice, and simplicity | `FabiusFunction.QPochhammerEntire` | Exhaustive public surface (zero definitions and five theorems): `hasProdLocallyUniformly_complexQPochhammerInf`, `complexQPochhammerInf_differentiable`, `complexQPochhammerInf_eq_zero_iff`, `complexQPochhammerInf_eq_zero_iff_eq_inv_pow`, and `analyticOrderAt_complexQPochhammerInf_of_eq_zero`.  For every fixed complex `q` with exactly `‖q‖ < 1`, the factors `a ↦ 1 - a*q^j` have the named locally uniform product on all of `ℂ`, so `a ↦ complexQPochhammerInf a q` is entire.  It vanishes exactly when one displayed factor vanishes, in the division-free form `∃ j : ℕ, 1 - a*q^j = 0`, and every such zero has analytic order one.  If additionally `q ≠ 0`, the exact lattice spelling is `∃ j : ℕ, a = (q^j)⁻¹`.  The raw factor form deliberately includes `q = 0`: then only index zero can vanish, at `a = 1`, and that zero is simple.  The simplicity proof isolates the unique vanishing factor and shows the finite-prefix/tail cofactor is holomorphic and nonzero.  These are fixed-`q`, single-symbol results.  They do not assert joint holomorphy in `(a,q)`, a reciprocal outside-disk formula, or a centered characteristic-function/MGF package; outer local-uniform convergence is supplied separately by `GeometricPochhammerNormalConvergence`. |
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
| Central Gaussian reduction at squared base | `FabiusFunction.CentralQBinomialReduction` | Exhaustive zero-definition/six-theorem surface: `finiteQPochhammerIn_mul_neg`, `finiteQPochhammerIn_two_mul`, `finiteQPochhammerIn_map_ringHom`, `central_gaussianBinomial_sq_mul_int`, `central_gaussianBinomial_sq_mul`, and `central_gaussianBinomial_sq_div`.  The commutative-ring layer proves sign-pairing, even/odd dissection, naturality, the integral-polynomial certificate, and the division-free identity `[2k,k]_(q²)(q²;q²)_k=(q;q²)_k(-q;q)_(2k)`; the field quotient form assumes exactly its two displayed denominators are nonzero. |
| Cyclotomic factorization of finite q-products and Gaussian coefficients | `FabiusFunction.CyclotomicFactorization` | Exhaustive zero-definition/seven-theorem surface: `div_add_div_le_div`, `div_le_div_add_div_add_one`, `mem_range_and_mem_divisors_iff`, `finiteQPochhammerIn_X_eq_prod_cyclotomic`, `finiteQPochhammerIn_X_eq_gaussianBinomial_mul`, `prod_cyclotomic_pow_div_extend`, and `gaussianBinomial_X_eq_prod_cyclotomic`.  The first two bounds show every Gaussian cyclotomic exponent is zero or one; the commutative-ring layer factors `(X;X)_n` and supplies the factorial/product-extension identities, while the final exact Gaussian factorization assumes an integral domain. |
| Complete Gaussian block at a primitive root of unity | `FabiusFunction.PrimitiveRootBlock` | Exhaustive zero-definition/three-theorem surface: `gaussianBinomial_isPrimitiveRoot_eq_zero`, `neg_one_pow_mul_pow_choose_two`, and `finiteQPochhammerIn_isPrimitiveRoot`.  In a commutative integral domain, a primitive `d`-th root `ζ` makes `[d,k]_ζ = 0` for `0 < k < d`; when `0 < d`, the phase is `(-1)^d ζ^(choose d 2) = -1` and the complete block is `(y;ζ)_d = 1-y^d`. |
| The q-Lucas theorem at a primitive root | `FabiusFunction.QLucas` | Exhaustive zero-definition/seven-theorem surface: `add_mul_add_sub_one`, `choose_two_add`, `coeff_finiteQPochhammerIn_neg_X`, `finiteQPochhammerIn_neg_X_block`, `coeff_block_pow_mul`, `pow_choose_two_add_mul_eq`, and `gaussianBinomial_q_lucas`.  The first two are natural-number quadratic identities; the remaining coefficient, block, and phase lemmas prove `[a*d+b,r*d+s]_ζ = choose(a,r) * [b,s]_ζ` when `0 < d`, `ζ` is a primitive `d`-th root in a commutative integral domain, and `b,s < d`.  The shared `two_mul_choose_two` helper is private here because its public owner is `QChuVandermonde`. |
| Cyclotomic carry criterion and multiple-index primitive-root value | `FabiusFunction.CyclotomicDivisibility` | Exhaustive zero-definition/three-theorem surface: `cyclotomic_exponent_eq_one_iff`, `cyclotomic_dvd_gaussianBinomial_iff`, and `gaussianBinomial_mul_isPrimitiveRoot`.  For `k ≤ n` and `0 < d`, the Gaussian cyclotomic exponent is one exactly when `n % d < k % d`; over `ℚ[X]` this is exactly the divisibility criterion for `Φ_d`.  In a commutative integral domain, a primitive `n`-th root with `0 < n` gives `[a*n,b*n]_ζ = choose(a,b)`. |
| MacMahon's integral q-Catalan polynomial | `FabiusFunction.QCatalan` | Exhaustive one-definition/eleven-theorem surface: `qCatalan`; `map_qInt`, `qInt_X_monic`, `qInt_X_natDegree`, `X_sub_one_mul_qInt`, `qInt_X_eq_prod_cyclotomic`, `qInt_X_dvd_gaussianBinomial_rat`, `qInt_X_dvd_gaussianBinomial_int`, `qInt_X_mul_qCatalan`, `qCatalan_natDegree`, `qCatalan_eval_one_mul`, and `qCatalan_eval_one`.  The semiring naturality and commutative-ring q-integer identities lead to `[n+1]_X ∣ [2*n,n]_X` over both `ℚ[X]` and `ℤ[X]`; the integral quotient has degree `n*(n-1)`, satisfies `(n+1) C_n(1) = choose(2*n,n)`, and evaluates to the ordinary Catalan number. |
| Newton interpolation and geometric-grid divided differences | `FabiusFunction.NewtonInterpolation` | Exhaustive three-definition/nineteen-theorem field-valued surface.  Definitions: `newtonCoeff`, `nodeNewtonPoly`, and compatibility alias `newtonInterpolant`.  Theorems: `newtonCoeff_eq`, `newtonCoeff_zero`, `newtonCoeff_mul_prod`, `nodeNewtonPoly_succ`, `eval_nodeNewtonPoly`, `degree_nodeNewtonPoly_lt`, `nodeNewtonPoly_eq_interpolate`, `eq_nodeNewtonPoly_of_eval_eq`, `coeff_nodeNewtonPoly_self`, `newtonCoeff_eq_sum`, `nodal_range_pow`, `prod_erase_pow_sub_pow`, `newtonCoeff_pow_eq_sum`, plus compatibility forms `newtonPoly_succ`, `eval_newtonPoly`, `degree_newtonPoly_lt`, `newtonPoly_eq_interpolate`, `eq_newtonPoly_of_eval_eq`, and `coeff_newtonPoly_self`.  It proves triangular reconstruction, interpolation and uniqueness at distinct finite nodes, the divided-difference formula, and its geometric-grid specialization; the evaluation, injectivity, nonzero-product, `q ≠ 0`, and index hypotheses remain explicit.  The node-qualified family avoids the existing scalar `newtonPoly`; the compatibility family is definitionally identical. |
| Jackson q-beta integral | `FabiusFunction.QBetaIntegral` | Exhaustive one-definition/eight-theorem real surface.  Definition: `qBeta`.  Theorems: `qNumber_pos`, `qBeta_term_eq`, `qBeta_eq_prod`, `qBeta_eq_qGamma`, `qBeta_comm`, `qBeta_pos`, `qBeta_add_one_left`, `qBeta_add_one_right`.  For `0 < q < 1` it identifies the Jackson integral with its infinite-product and q-Gamma formulas and derives positivity, symmetry, and both recurrences under the displayed positive-argument hypotheses. |
| Generic Gaussian-polynomial degree, palindromicity, mean, and linear coefficient | `FabiusFunction.GaussianBinomialPalindromic` | Exhaustive public surface: zero definitions and fourteen theorems, `reflect_add_of_natDegree_le`, `reflect_one'`, `gaussianBinomial_natDegree_le`, `gaussianBinomial_zero_left`, `gaussianBinomial_diag'`, `reflect_gaussianBinomial`, `coeff_gaussianBinomial_reflect`, `coeff_gaussianBinomial_zero`, `coeff_gaussianBinomial_top`, `gaussianBinomial_natDegree`, `gaussianBinomial_monic`, `two_mul_derivative_gaussianBinomial_eval_one`, `coeff_gaussianBinomial_one_of_pos_of_lt`, and `coeff_gaussianBinomial_one`.  Over every commutative semiring it supplies the reflection helpers, the degree bound, zero/diagonal values, reflection in degree `k * (n - k)`, constant and top coefficients one, bounded-index coefficient reversal, and the division-free mean identity.  The new interior theorem gives coefficient one under exactly `0 < k` and `k < n`; the total theorem gives `if 0 < k ∧ k < n then 1 else 0`, explicitly covering `k = 0`, `k = n`, and `n < k`, with no nontriviality hypothesis.  Exact degree and monicity require only that the semiring be nontrivial. |
| Universal Gaussian-polynomial degree and palindromicity | `FabiusFunction.GaussianBinomialPolynomialStructure` | Exhaustive public surface: zero definitions and five theorems, `natDegree_gaussianBinomial_universal`, `gaussianBinomial_universal_monic`, `coeff_zero_gaussianBinomial_universal`, `gaussianBinomial_universal_reflect`, and `coeff_gaussianBinomial_universal_symm`.  For `k ≤ n`, the universal natural-coefficient polynomial `gaussianBinomial (X : ℕ[X]) n k` has exact natural degree `k * (n - k)`, is monic, has constant coefficient one, and is fixed by reflection in that degree; consequently its coefficients at `d` and `k * (n - k) - d` agree whenever `d ≤ k * (n - k)`.  The adjacent general-semiring theorem `coeff_gaussianBinomial_one` supplies the complete linear-coefficient classifier. |
| Gaussian coefficients and finite `q`-Pochhammer products at `q = -1` | `FabiusFunction.GaussianBinomialAtNegOne` | Exhaustive public surface: zero definitions and five theorems, `gaussianBinomial_neg_one_even_even`, `gaussianBinomial_neg_one_odd_even`, `gaussianBinomial_neg_one_odd_odd`, `finiteQPochhammerIn_neg_one_even`, and `finiteQPochhammerIn_neg_one_odd`.  All five are total over every `[CommRing R]`, with no domain, characteristic, cancellation, division, or nonvanishing assumption.  The three Gaussian identities include columns above the row, where both sides are zero; together with the pre-existing `gaussianBinomial_neg_one_even_odd_eq_zero` from `QBinomialReciprocity`, they give the complete four-parity table.  The two product identities are `(z;-1)_(2a) = (1-z^2)^a` and `(z;-1)_(2a+1) = (1-z^2)^a(1-z)`.  The derivative and root-multiplicity layer is listed separately in `GaussianBinomialAtNegOneDerivative`. |
| First Gaussian-polynomial jets and simple alternating roots at `q = -1` | `FabiusFunction.GaussianBinomialAtNegOneDerivative` | Exhaustive public surface: zero definitions and four theorems, `gaussianBinomial_derivative_eval_neg_one_of_even_degree`, `gaussianBinomial_derivative_eval_neg_one_even_odd`, `gaussianBinomial_even_odd_rootMultiplicity_int`, and `gaussianBinomial_even_odd_rootMultiplicity`.  Over every `[CommRing R]`, the first theorem gives `G'_(n,k)(-1) = -(k*(n-k)/2) G_(n,k)(-1)` whenever `k*(n-k)` is even, including degree zero and columns above the row, while the second gives `G'_(2a,2b+1)(-1) = (a-b) * choose(a,b)` for all natural `a,b`, with natural subtraction and binomial zero extension making it total.  If `b < a`, the last two theorems prove that this alternating zero has root multiplicity exactly one, first over `ℤ` and then over every `[CommRing K] [CharZero K]`.  No simplicity claim is made in arbitrary characteristic, outside the admissible range, or for all cyclotomic zeros. |
| Elementary finite `q`-Pochhammer reversal, termination, and adjacent Gaussian ratios | `FabiusFunction.QPochhammerElementaryIdentities` | Exhaustive public surface (13 theorems): `finiteQPochhammerIn_base_reversal_units`, `finiteQPochhammerIn_inv_base_reversal_units`, `finiteQPochhammerIn_base_reversal`, `finiteQPochhammerIn_inv_base_reversal`, `prod_pow_sub_pow_eq_finiteQPochhammerIn`, `pow_mul_finiteQPochhammerIn_inv_pow_eq`, `finiteQPochhammerIn_inv_pow_eq_self_div`, `finiteQPochhammerIn_inv_pow_eq_zero_of_lt`, `one_sub_mul_gaussianBinomial_one`, `gaussianBinomial_adjacent_mul`, `gaussianBinomial_row_adjacent_mul`, `gaussianBinomial_adjacent_div`, `gaussianBinomial_row_adjacent_div`.  The two unit reversals hold in every commutative ring.  The root-safe terminating numerator, first-column clearer, and both adjacent cross-multiplied identities also hold over every commutative ring, including roots of unity; the two cross identities are total in all `n,k`, with zero extension making both sides vanish on and above the row boundary.  The field reversal wrappers require exactly `a != 0` and `q != 0`; the cleared terminating formula and the `k > N` zero theorem require `q != 0`, while its displayed quotient additionally requires `(q;q)_(N-k) != 0`.  The two adjacent quotient theorems remain restricted to `k < n` and require exactly their displayed Gaussian and linear-factor denominators to be nonzero; they do not require `q != 0`. |
| Finite q-Cauchy convolutions and the q-Bernstein partition of unity | `FabiusFunction.QBinomialCauchy` | Exhaustive public surface: `finite_qCauchy_identity`, its compatibility spelling `finiteQPochhammerIn_mul_eq_sum_gaussianBinomial`, `finite_qCauchy_identity_reflected`, `qBernsteinBasis`, `sum_qBernsteinBasis`, and `finite_qCauchy_second_identity` (one definition and five theorems).  The primary identity is `(uv;q)_n = sum_(k=0)^n [n choose k]_q (u;q)_k v^k (v;q)_(n-k)`; its reflected strengthening uses `(v;q)_k v^(n-k) (u;q)_(n-k)`.  The specialization `u = 0` makes the denominator-free q-Bernstein row sum to one, and the second identity evaluates the two-product Cauchy convolution.  All parameters and degrees are arbitrary in every commutative ring, including `n = 0`, `q = 0`, roots of unity, positive characteristic, and zero divisors; no quotient, cancellation, or nonvanishing hypothesis is present. |
| Bit-position and weighted-subset forms of Gauss's finite theorem | `FabiusFunction.BitPositionQBinomial` | Exhaustive public surface: `prod_one_add_mul_pow_eq_gaussianBinomial`, `prod_one_add_pow_eq_sum_gaussianBinomial`, `sum_powersetCard_two_pow`, `sum_pow_bitPositionSum_filter_eq_gaussianBinomial`, `sum_pow_bitPositionSum_filter_eq_gaussianBinomial'`, `sum_pow_sum_powersetCard_eq_gaussianBinomial`, `sum_pow_sum_powersetCard_Icc_eq_gaussianBinomial`, `gaussianBinomial_one_eq_choose`.  The last two subset identities give respectively the zero-based `range N` weight `q^(choose r 2)` and the literal one-based interval `Icc 1 N` weight `q^(choose (r+1) 2)`; they are total in `N,r` over every commutative ring. |
| Reciprocal symmetry and the `q = -1` parity zero of Gaussian coefficients | `FabiusFunction.QBinomialReciprocity` | Exhaustive public surface (four theorems): `gaussianBinomial_reciprocity_units`, `gaussianBinomial_reciprocity`, `gaussianBinomial_neg_one_eq_zero_of_odd_degree`, and `gaussianBinomial_neg_one_even_odd_eq_zero`.  The total identity `q^(k*(n-k)) * [n choose k]_(q⁻¹) = [n choose k]_q` holds for a unit in every commutative semiring, including zero divisors, and has a nonzero-parameter wrapper over every semifield.  Over every commutative ring, odd polynomial degree forces vanishing at `q = -1`; hence every odd column of an even row vanishes there, including the above-diagonal zero-extension cases.  No quotient formula, cancellation of finite q-Pochhammer factors, domain hypothesis, or characteristic restriction is used. |
| Gaussian reciprocity and dimension-dominant bounds | `FabiusFunction.GaussianBinomialBounds` | Exhaustive zero-definition/six-theorem surface: `gaussianBinomial_inv`, `one_le_gaussianBinomial`, `finiteQPochhammerIn_pow_le_one`, `gaussianBinomial_le_inv_qPochhammerInfIn`, `pow_le_gaussianBinomial_of_one_lt`, and `gaussianBinomial_le_pow_div_of_one_lt`.  The module reuses the stronger ordered-field theorem `finiteQPochhammerIn_self_pos` from `GeneralQConditionNumber`.  Its field reciprocity theorem assumes `q != 0` and `k ≤ n`.  Over ordered fields, nonnegative `q` gives the lower bound one; over the reals, `0 ≤ q < 1` gives the uniform upper bound by `(q;q)_∞⁻¹`, and reciprocity transfers these to `Q > 1` as `Q^(k*(n-k)) ≤ [n choose k]_Q ≤ Q^(k*(n-k))/(Q⁻¹;Q⁻¹)_∞`.  The index and order hypotheses remain explicit. |
| Division-free Gaussian chains, alternating rows, and mutually inverse scalar kernels | `FabiusFunction.QBinomialInversion` | Exhaustive public surface: `gaussianBinomial_mul`, `sum_gaussianBinomial_alternating_mul_pow`, `sum_gaussianBinomial_alternating`, `gaussianBinomialKernel`, `gaussianBinomialInverseKernel`, `scaledGaussianBinomialKernel`, `scaledGaussianBinomialInverseKernel`, `gaussianBinomialKernel_left_orthogonality`, `gaussianBinomialKernel_right_orthogonality`, `scaledGaussianBinomialKernel_left_orthogonality`, `scaledGaussianBinomialKernel_right_orthogonality`.  The chain identity holds over every commutative semiring; the alternating sums and all four total-`Icc` orthogonality theorems hold over every commutative ring.  The scale `s` is independent of the Gaussian base and is arbitrary: neither it nor `q` is assumed nonzero or invertible. |
| Scaled and classical `q`-binomial transforms of module-valued sequences | `FabiusFunction.QBinomialTransform` | Exhaustive public surface (four definitions and four theorems): `scaledGaussianBinomialTransform`, `scaledGaussianBinomialInverseTransform`, `scaledGaussianBinomialInverseTransform_transform`, `scaledGaussianBinomialTransform_inverseTransform`, `scaledGaussianBinomial_inversion`, `gaussianBinomialTransform`, `gaussianBinomialInverseTransform`, `gaussianBinomial_inversion`.  The forward definitions need only `[Semiring R] [AddCommMonoid M] [Module R M]`, and the inverse definitions need only `[Ring R] [AddCommMonoid M] [Module R M]`.  For `[CommRing R] [AddCommMonoid M] [Module R M]`, both composition theorems are equalities of whole sequence functions and the two triangular relations are equivalent as whole-sequence equalities.  The proofs reuse `lowerTriangularTransform_comp`; the Gaussian coefficient zero-extends each scalar kernel above its row.  These finite algebraic maps require no topology, convergence, division, or invertibility; the unscaled theorem is classical `q`-binomial inversion. |
| Scaled Gaussian characteristic polynomials and exact `q`-difference annihilation | `FabiusFunction.QDifferenceAnnihilation` | Exhaustive public surface (four theorems): `sum_scaledGaussianBinomialInverseKernel_mul_pow`, `sum_gaussianBinomialInverseKernel_mul_geometric_pow`, `qDifference_sum_eval₂_eq_map_coeff_mul`, `qDifference_sum_eval₂_eq_zero_of_degree_lt`.  Over every commutative ring, `sum_(k=0)^n (-s)^(n-k) q^(choose (n-k) 2) [n choose k]_q z^k = prod_(j<n) (z-s q^j)`.  At `s = 1` and `z = q^d`, this gives every monomial moment `prod_(j<n) (q^d-q^j)`, hence zero for `d < n`.  More strongly, after any scalar extension `φ : A →+* R` from a semiring, the row applied to a polynomial of degree at most `n` is `φ(p.coeff n) * prod_(j<n) (q^n-q^j)`, and it annihilates every polynomial of degree strictly below `n`.  The statements include `n = 0` and the zero polynomial; nodes may collide and the surviving product may vanish.  No division, node distinctness, nonzero/invertible base, domain, characteristic, topology, or convergence hypothesis is used. |
| Exact q-Gaussian inversion specializations | `FabiusFunction.QBinomialInversionSpecializations` | Exhaustive public surface (two definitions and four theorems): `qGaussianResidualCoeff`, `qGaussianReconstructionCoeff`, `qGaussianResidualCoeff_eq`, `qGaussianReconstructionCoeff_eq`, `qGaussianReconstructionCoeff_residualCoeff_delta`, `qGaussianResidualCoeff_reconstructionCoeff_delta`.  The two definitions and their pointwise closed-form theorems require only `[Ring R]`, allowing a noncommutative coefficient ring.  At Gaussian base `q^2` and scale `-q`, the residual coefficient is `(-q)^(n-k) [n choose k]_(q^2)` and its reconstruction coefficient is `q^((n-k)^2) [n choose k]_(q^2)`.  Exactly the two total-`Icc` convolution-delta theorems require `[CommRing R]`. |
| Denominator-free `q`-Vandermonde and central convolutions | `FabiusFunction.QBinomialVandermonde` | Exhaustive public surface: `gaussianBinomial_add_vandermonde`, `gaussianBinomial_add_vandermonde'`, `gaussianBinomial_add_central`, `gaussianBinomial_add_central_min`, `gaussianBinomial_two_mul_add_shifted_central`, `gaussianBinomial_two_mul_sub_shifted_central`, `gaussianBinomial_two_mul_sub_shifted_central_Icc`, `gaussianBinomial_two_mul_int_shifted_central`, `gaussianBinomial_two_mul_int_shifted_central_finsum`.  All nine hold over an arbitrary commutative semiring without division, cancellation, or a restriction on `q`; the first seven are the natural-index forms, while the last two prove the report's single formula for every `k : ℤ`, first on the finite natural range `0,…,N` and then literally as a finite-support sum over `ℤ`. |
| Geometric Richardson filters, Gaussian coefficients, all residual moments, and finite conditioning | `FabiusFunction.GeometricQBinomialLagrange`, `FabiusFunction.GeometricRichardson`, `FabiusFunction.GeometricLagrangeWeights`, `FabiusFunction.GeometricLagrangeQBinomial`, `FabiusFunction.GeometricLagrangeQMoments` | `geometricQBinomialWeightNumerator_eq_scaledGaussianBinomialInverseKernel`, `reversed_finite_qBinomial_theorem`, `sum_geometricLagrangeWeight_mul_pow_eq_gaussianBinomial`, `geometricLagrangeWeightPolynomial_eq_forwardGeometricRichardsonPolynomial`, `geometricLagrangeQMoment_eq_residual_qBinomial`, `sum_abs_geometricLagrangeWeight_eq_prod`.  The first theorem, now owned by `GeometricQBinomialLagrange`, globally identifies the denominator-free geometric numerator with the inverse kernel at base and scale `q`, including indices above the diagonal and without `k ≤ n`; it is the `s = q` specialization of the scaled characteristic polynomial.  This does not weaken the separate `Field`/finite-node-`InjOn`/in-range assumptions of normalized quotient formulas.  The remaining rational closed forms use their stated nonzero-base and nonvanishing finite-denominator hypotheses, while sign and variation assume `0 < q < 1`. |
| Quotient-defined rational geometric moments and exact finite conditioning | `FabiusFunction.GeometricLagrangeQMoments` | Exhaustive public surface (one definition and 37 theorems): `geometricLagrangeQMoment`; `geometricLagrangeQMoment_eq_weightPolynomial_eval`, `geometricLagrangeQMoment_eq_forwardRichardson_eval`, `geometricRootPolynomial_inv_eval_pow_mul_signedPowers`, `geometricRootPolynomial_inv_eval_pow_mul_triangular`, `geometricRootPolynomial_inv_eval_one_mul_triangular`, `geometricLagrangeQMoment_eq_qPochhammer`, `geometricLagrangeQMoment_zero`, `geometricLagrangeQMoment_eq_zero`, `geometricRootPolynomial_inv_eval_pow_eq_qPochhammer_of_le`, `geometricLagrangeQMoment_eq_residual_qPochhammer`, `qPochhammer_self_add`, `qPochhammer_self_pos_of_pos_of_lt_one`, `qBinomial_pos_of_pos_of_lt_one`, `gaussianBinomial_eq_qBinomial_of_pos_of_lt_one`, `qPochhammer_pow_pos_of_pos_of_lt_one`, `qPochhammer_tail_div_self_eq_qBinomial`, `geometricLagrangeQMoment_eq_residual_qBinomial`, `geometricLagrangeQMoment_firstUncancelled`, `negOnePow_mul_geometricLagrangeQMoment_eq_positiveResidual`, `negOnePow_mul_geometricLagrangeQMoment_pos`, `qPochhammer_self_succ`, `qBinomial_succ_succ_of_pos_of_lt_one'`, `qBinomial_succ_succ_of_pos_of_lt_one`, `qBinomial_theorem_of_pos_of_lt_one`, `sum_qBinomial_triangular_succ_eq_neg_qPochhammer`, `abs_geometricLagrangeWeight_eq_qBinomial`, `abs_geometricLagrangeWeight_eq_sign_mul`, `abs_geometricLagrangeWeight_complement_eq_qBinomial`, `sum_abs_geometricLagrangeWeight_eq_qPochhammer_ratio`, `neg_qPochhammer_div_self_eq_prod`, `sum_abs_geometricLagrangeWeight_eq_prod`, `quarterGeometricLagrangeQMoment_eq_qPochhammer`, `quarterGeometricLagrangeQMoment_eq_zero`, `quarterGeometricLagrangeQMoment_eq_residual_qPochhammer`, `quarterGeometricLagrangeQMoment_eq_residual_qBinomial`, `quarterGeometricLagrangeQMoment_firstUncancelled`, and `sum_abs_quarterGeometricLagrangeWeight_eq_qPochhammer_ratio`.  These are finite rational identities.  The quotient and injectivity forms retain their explicit nonzero-denominator hypotheses; positivity, sign, and absolute-value formulas retain `0 < q < 1`; no analytic convergence or error estimate is asserted. |
| Euler generating function of the geometric Richardson triangle | `FabiusFunction.GeometricRichardsonGenerating` | Exhaustive public surface (three definitions and seven theorems): `geometricRichardsonKernel`, `qPochhammerNormalizedDataSeries`, `geometricRichardsonTransform`; `coeff_rescale_qPochhammerSeries_eq_geometricRichardsonKernel`, `coeff_qPochhammerNormalizedDataSeries`, `geometricRichardsonTransform_generating`, `geometricRichardsonTransform_eq_sum_lagrange`, `geometricLagrangeRichardson_generating`, `hasSum_geometricRichardsonTransform_mul_pow`, and `hasSum_geometricLagrangeRichardson_mul_pow`.  The formal convolution and factorization hold over every commutative ring, without topology or a regularity assumption on `q`, using `Ring.inverse` at possibly nonunit finite q-Pochhammer factors.  Over a field, `q ≠ 0` identifies the convolution with the canonical totalized Lagrange row and proves the report's `gq:thm:richardson-generating` claim exactly.  No root-of-unity exclusion is needed for that algebraic equality, but colliding nodes are not thereby genuine interpolation weights; `q = 0` is excluded from the Lagrange identification and its closed formula already fails once repeated nodes occur.  The two analytic theorems assume a complete normed field, `‖q‖ < 1`, and norm-summability of the normalized data at `z`; the report-facing Lagrange form additionally assumes `q ≠ 0` and concludes `HasSum`, not a general evaluation theorem for formal power series. |
| Report-facing geometric complete-homogeneous bridges | `FabiusFunction.GeometricLagrangeCompleteHomogeneous` | Exhaustive five-theorem surface: `completeHomogeneousEvalOn_geometric_range`, `sum_geometricLagrangeWeight_mul_pow_succ_add_eq_gaussianBinomial`, `geometricLagrangeQMoment_eq_residual_gaussianBinomial`, `completeHomogeneousEvalOn_geometric_range_eq_qBinomial`, and `geometricLagrangeQMoment_eq_residual_qBinomial_via_completeHomogeneous`.  The semiring principal-specialization alias is denominator-free; the field residual uses finite-node injectivity; the rational quotient bridges retain their stated nonzero-Pochhammer or `0 < q < 1` hypotheses. |
| Exact finite polynomial filters | `FabiusFunction.FinitePolynomialFilterExactness` | Exhaustive five-theorem surface: `polynomialFilter_response_eq`, `polynomialFilter_exact`, `normalizedGeometricRootPolynomial_filter_exact`, `forwardGeometricRichardsonPolynomial_filter_exact`, and `forwardGeometricRichardsonPolynomial_filter_firstUncancelled`.  The first two are arbitrary commutative-semiring response and mass-one/root-cancellation laws.  The geometric field specializations preserve the baseline, cancel the prescribed inverse or forward modes, and evaluate the first surviving forward mode as `(-1)^n q^(choose (n+1) 2)` under their explicit nonzero-base and normalization-denominator hypotheses. |
| Formal geometric Richardson filters and the quarter Catalan--Gaussian specialization | `FabiusFunction.QuarterCatalanRichardson` | Exhaustive public surface (three definitions and 15 theorems): `finiteRescaleFilter`, `geometricRichardsonPowerSeriesFilter`, `quarterCatalanRichardsonFilter`; `finiteRescaleFilter_coeff`, `geometricRichardsonPowerSeriesFilter_coeff`, `geometricRichardsonPowerSeriesFilter_coeff_zero`, `geometricRichardsonPowerSeriesFilter_coeff_eq_zero`, `geometricRichardsonPowerSeriesFilter_coeff_eq_qPochhammer`, `geometricRichardsonPowerSeriesFilter_coeff_eq_qBinomial`, `geometricRichardsonPowerSeriesFilter_firstUncancelled_coeff_of_nonzero`, `geometricRichardsonPowerSeriesFilter_firstUncancelled_coeff`, `quarterCatalanRichardsonFilter_coeff`, `quarterCatalanRichardsonFilter_coeff_zero`, `quarterCatalanRichardsonFilter_coeff_eq_zero`, `quarterCatalanRichardsonFilter_coeff_eq_zero_of_le`, `quarterCatalanRichardsonFilter_coeff_eq_qBinomial`, `quarterCatalanRichardsonFilter_coeff_succ_eq_qBinomial`, and `quarterCatalanRichardsonFilter_firstUncancelled_coeff`.  These are coefficientwise formal-power-series identities: the generic row diagonalizes rescaling, preserves degree zero, cancels degrees `1,…,p`, and exposes every residual and the first survivor; the quarter specialization multiplies those factors by the exact Catalan coefficients.  No convergence, real-function error sign, remainder bound, or analytic acceleration is asserted. |
| Exact lower-Lambert phase locking, reciprocal-grid Richardson moments, Bell/generalized-harmonic residuals, fixed-order growing-row bounds, and analytic extraction of the periodic Fabius endpoint term | `FabiusFunction.LambertPhaseLockedRichardson`, `FabiusFunction.LambertPhaseLockedBell`, `FabiusFunction.LambertReciprocalAsymptotics`, `FabiusFunction.FabiusLambertPhaseLockedPullback`, `FabiusFunction.FabiusLambertPhaseExtraction`, `FabiusFunction.FabiusLambertPhaseExtractionBell` | The phase-locking and analytic chain exposes `fabiusLambertPhase_phaseLockedNode`, `Periodic.apply_fabiusLambertPhase_phaseLockedNode`, `shiftedReciprocalLagrangeWeight_eq_choose`, `sum_shiftedReciprocalLagrangeWeight_mul_periodicPhaseLocked`, `sum_shiftedReciprocalLagrangeWeight_mul_invPow_card_add`, `sum_shiftedReciprocalLagrangeWeight_mul_invPow_eq_completeHomogeneous`, `sum_shiftedReciprocalLagrangeWeight_residual`, `shiftedReciprocalLagrangeWeight_mul_invPow_isBigO_atTop`, `tendsto_lambertPhaseLockedNode_smallArgument`, `log_fabius_phaseLockedNode_sub_WikipediaLambertExpansion_isBigO`, `fabiusPhaseLockedPeriodicEstimator_sub_residual_isBigO`, `fabiusPhaseLockedPeriodicEstimator_sub_firstOmitted_isBigO`, and `fabiusPhaseLockedPeriodicEstimator_tendsto_periodicAlong`.  The Bell leaf exhaustively adds `shiftedReciprocalPowerSum`, `shiftedReciprocalBellInput`, `shiftedReciprocalPowerSum_eq_sum`, `shiftedReciprocalBellInput_zero`, `shiftedReciprocalBellInput_succ`, `completeHomogeneousEvalOn_shiftedReciprocal_eq_bell`, `sum_shiftedReciprocalLagrangeWeight_mul_invPow_card_add_eq_bell`, `sum_shiftedReciprocalLagrangeWeight_mul_invPow_eq_bell`, `fabiusPhaseLockedResidualTerm_eq_bell`, and `fabiusPhaseLockedResidualPartialSum_eq_sum_bell`.  The normalized Bell specialization is stated over a field with rational-algebra structure, and the weighted moment forms assume characteristic zero.  Within that setting the definitions are total and require no positivity or nonzero-shift hypothesis.  For every fixed row order `r` and residual depth `S`, subtracting the first `S` exact residual terms leaves `O(lambda⁻¹^(r+1+S))`, and integer phase rays converge to the corresponding value of `negativeLaplacePsi`.  No convergence of an infinite residual series, exponentiated Bell relative-error hierarchy, higher derivative extractor, residual sign/bracketing theorem, or uniformity for growing `r` or `S` is asserted. |
| Infinite `q`-Pochhammer symbols and the limiting general-`q` row condition number | `FabiusFunction.LimitConditionNumber` | `qPochhammerInf`, `multipliable_one_sub_mul_pow`, `tendsto_finiteQPochhammerIn`, `qPochhammerInf_self_pos`, `qConditionNumberLimit`, `tendsto_sum_abs_qToeplitzWeight`, `one_div_one_sub_le_qConditionNumberLimit`, `tendsto_qConditionNumberLimit_atTop_at_one_left`, `one_lt_qConditionNumberLimit`, `qConditionNumberLimit_zero`, `thousand_le_qConditionNumberLimit`; for `0 ≤ q < 1` the finite row variation converges to `(-q;q)_∞ / (q;q)_∞`, whose denominator is strictly positive and whose value is at least `1 / (1-q)`; consequently the limit tends to `+∞` as `q → 1⁻`, so no uniform-in-`q` bound exists |
| Closed real Lambert branches, endpoint continuity, and the principal small-argument equivalent | `FabiusFunction.LowerLambertW`, `FabiusFunction.PrincipalLambertW` | The new lower-branch continuity surface is `lowerLambertW_continuousWithinAt_branchPoint`, `lowerLambertW_continuousAt`, `lowerLambertW_continuousOn`, and `lowerLambertW_continuousOn_Ico`: it gives continuity on the full natural domain `[-exp(-1),0)`, including the finite branch point but not zero.  The principal companion exposes `principalLambertArg`, `principalLambertW`, `principalLambertW_mul_exp`, `neg_one_le_principalLambertW`, `principalLambertW_unique`, `principalLambertW_branchPoint`, `principalLambertW_zero`, `principalLambertW_exp_one`, `mul_exp_strictMonoOn`, `principalLambertW_strictMonoOn`, `principalLambertW_nonpos`, `neg_one_lt_principalLambertW`, `principalLambertW_image_Ioi`, `principalLambertW_image_Icc`, `principalLambertW_continuousWithinAt_branchPoint`, `principalLambertW_continuousAt`, `principalLambertW_continuousOn`, `principalLambertW_continuousOn_Ici`, `principalLambertW_hasDerivAt`, `deriv_principalLambertW_pos`, `deriv_principalLambertW_zero`, and `principalLambertW_isEquivalent_zero`.  Thus `W₀` is continuous on `[-exp(-1),∞)`, its derivative claims are only above the branch point, and `W₀(z) ~ z` at zero.  The raw branch-point derivative/secant limits and leading square-root laws are recorded in the dedicated modules below; no finite endpoint derivative is asserted. |
| Exact real-branch pairing, gap bijection, and symmetric identities | `FabiusFunction.LambertWBranchPairing`, `FabiusFunction.LambertWGapBijection`, `FabiusFunction.LambertWBranchSymmetry` | Exhaustive module counts are respectively 0+7, 4+16, and 0+9, hence four definitions and 32 theorems (36 public declarations) in their union.  `LambertWBranchPairing` exports `principalLambertW_sub_lowerLambertW_pos`, `lowerLambertW_eq_principalLambertW_mul_exp_gap`, `principalLambertW_eq_neg_gap_div`, `lowerLambertW_eq_neg_gap_mul_exp_div`, `lowerLambertW_eq_neg_gap_div_one_sub_exp_neg`, `eq_neg_gap_div_mul_exp`, and `principalLambertW_lowerLambertW_eq_of_exp_gap`.  `LambertWGapBijection` defines `gapPrincipal`, `gapLower`, `gapArg`, and `branchGap`, and proves `gap_denominator_pos`, `gapPrincipal_mem_Ioo`, `gapLower_eq_mul_exp`, `gapLower_eq_sub`, `gapLower_lt_neg_one`, `gapLower_mul_exp`, `gapArg_mem_Ioo`, `principalLambertW_gapArg`, `lowerLambertW_gapArg`, `branchGap_gapArg`, `gapArg_branchGap`, `branchGap_invOn`, `branchGap_bijOn`, `principalLambertW_gapArg_log`, `lowerLambertW_gapArg_log`, and `gapArg_log`.  `LambertWBranchSymmetry` exports `lowerLambertW_div_principalLambertW_eq_exp_branchGap`, `principalLambertW_add_lowerLambertW_eq_exp_branchGap`, `principalLambertW_add_lowerLambertW_eq_cosh_div_sinh_branchGap`, `principalLambertW_mul_lowerLambertW_eq_exp_branchGap`, `principalLambertW_mul_lowerLambertW_eq_sinh_sq_branchGap`, `principalLambertW_add_lowerLambertW_lt_neg_two`, `principalLambertW_mul_lowerLambertW_pos`, `principalLambertW_mul_lowerLambertW_lt_one`, and `principalLambertW_mul_lowerLambertW_mem_Ioo`.  On the strict common domain `x ∈ (-exp(-1),0)`, the positive gap `Δ=W₀(x)-W₋₁(x)` gives both branches and their argument by exact exponential-rational formulas; conversely `gapArg` and `branchGap` are two-sided inverses between that domain and `Δ ∈ (0,∞)`.  For `t>1`, the three explicit `t=exp Δ` formulas recover `W₀`, `W₋₁`, and the common argument.  The symmetric leaf proves the exact ratio, exponential and hyperbolic sum/product forms, `W₀+W₋₁<-2`, and `0<W₀W₋₁<1`.  All endpoints are deliberately excluded.  These three finite exact modules neither supply a Bernoulli-number expansion of the gap formulas nor assert convergence, remainders, or branch-point/small-input asymptotics. |
| Exact second derivatives and curvature of the real Lambert branches | `FabiusFunction.LambertWCurvature` | Exhaustive public surface: `deriv_principalLambertW`, `deriv_principalLambertW_hasDerivAt`, `deriv_deriv_principalLambertW`, `deriv_deriv_principalLambertW_zero`, `deriv_deriv_principalLambertW_neg`, `strictConcaveOn_principalLambertW`, `deriv_lowerLambertW_hasDerivAt`, `deriv_deriv_lowerLambertW`, `deriv_deriv_lowerLambertW_pos_iff`, `deriv_deriv_lowerLambertW_neg_iff`, `deriv_deriv_lowerLambertW_eq_zero_iff`, `strictConvexOn_lowerLambertW_left`, and `strictConcaveOn_lowerLambertW_right`.  The nonsingular formula `W'' = -exp(-2W)(W+2)/(W+1)^3` is proved for the principal branch exactly when `z > -exp(-1)` and for the lower branch exactly when `-exp(-1) < z < 0`; in particular `W₀''(0) = -2`.  The principal branch is strictly concave on its full closed domain.  The lower branch has its unique smooth-domain inflection at `-2 exp(-2)`, is strictly convex from the branch point through that input, and strictly concave thereafter toward zero.  The shape package includes the finite branch point and the shared inflection endpoint, while the lower natural domain remains open at zero; it does not assert derivative limits at the branch point or a Puiseux law. |
| One-sided vertical tangents and failure of finite branch-point differentiability | `FabiusFunction.LambertWBranchPointGeometry` | Exhaustive public surface (eight theorems): `tendsto_deriv_principalLambertW_branchPoint_atTop`, `tendsto_deriv_lowerLambertW_branchPoint_atBot`, `tendsto_principalLambertW_secantSlope_branchPoint_atTop`, `tendsto_lowerLambertW_secantSlope_branchPoint_atBot`, `principalLambertW_not_differentiableWithinAt_branchPoint`, `lowerLambertW_not_differentiableWithinAt_branchPoint`, `principalLambertW_not_differentiableAt_branchPoint`, and `lowerLambertW_not_differentiableAt_branchPoint`.  As `z` approaches `-exp(-1)` from the right, the principal derivative and endpoint secant slope `(W₀(z)+1)/(z+exp(-1))` tend to `+∞`, while their lower-branch counterparts tend to `-∞`.  Consequently neither branch has a finite right derivative there, and neither totalized branch is differentiable at the branch point.  These statements require no square-root or Puiseux expansion. |
| Leading signed square-root asymptotics at the real branch point | `FabiusFunction.LambertWBranchPointAsymptotics` | Exhaustive public surface (one definition and eight theorems): `lambertWBranchPointScale`, `lambertWBranchPointScale_pos`, `lambertWBranchPointScale_sq`, `tendsto_principalLambertW_add_one_sq_div_branchPoint`, `tendsto_lowerLambertW_add_one_sq_div_branchPoint`, `principalLambertW_add_one_sq_isEquivalent_branchPoint`, `lowerLambertW_add_one_sq_isEquivalent_branchPoint`, `principalLambertW_add_one_isEquivalent_branchPoint`, and `lowerLambertW_add_one_isEquivalent_branchPoint`.  The scale is `sqrt(2 exp(1) (z+exp(-1)))`, is positive strictly to the right of the branch point, and has square exactly `2 exp(1) (z+exp(-1))`.  For each branch, `(W(z)+1)^2/(z+exp(-1)) → 2 exp(1)`, equivalently the squared displacement is asymptotic to that linear normalization.  The signed leading laws are `W₀(z)+1 ~ scale(z)` and `W₋₁(z)+1 ~ -scale(z)` from the right.  No `O(z+exp(-1))` remainder, convergent Puiseux expansion, or higher coefficient is asserted, and named generic/Fabius phase wrappers for these raw endpoint laws remain open. |
| Two real Lambert inverses of scaled power--exponential saddles, exact root classification, full phase continuity, and small-input asymptotics | `FabiusFunction.PowerExponentialLambert`, `FabiusFunction.PowerExponentialLambertCalculus`, `FabiusFunction.PowerExponentialLambertInverse`, `FabiusFunction.PowerExponentialLambertAsymptotics`, `FabiusFunction.PowerExponentialLambertFabius` | `powerExponentialSaddle`, `powerExponentialPeak`, `powerExponentialLambertArgument`, `principalPowerExponentialPhase`, `lowerPowerExponentialPhase`, the three `powerExponentialLambertArgument_mem_*` domain theorems, both branch solve laws and endpoint values, `principalPowerExponentialPhase_mem_Icc`, `lowerPowerExponentialPhase_mem_Ici`, `powerExponentialLambertArgument_strictAntiOn`, `principalPowerExponentialPhase_strictMonoOn`, `lowerPowerExponentialPhase_strictAntiOn`, both branch `HasDerivAt`/`deriv`/derivative-sign and interior-continuity pairs, `principalPowerExponentialPhase_continuousOn_Icc`, `lowerPowerExponentialPhase_continuousOn_Ioc`, `powerExponentialLambertArgument_image_Icc`, `powerExponentialLambertArgument_image_Ioc`, `principalPowerExponentialPhase_image_Icc`, `lowerPowerExponentialPhase_image_Ioc`, both branch `LeftInvOn`/`RightInvOn`/`InvOn` packages, `powerExponentialSaddle_eq_iff_eq_principal_or_eq_lower`, and `principalPowerExponentialPhase_ne_lowerPowerExponentialPhase`.  All of these generic branch results assume `m ≠ 0`, `A > 0`, and `beta > 0`; the root iff additionally assumes `x ∈ (0,peak]` and `lambda ≥ 0` (the restriction is essential for even `m`), while distinctness holds only for `x ∈ (0,peak)`.  The principal phase is continuous on `[0,peak]`, the lower phase on `(0,peak]`, and derivatives remain restricted to `(0,peak)`.  The small-input surface is `powerExponentialLambertEpsilon`, `powerExponentialLambertArgument_eq_neg_epsilon`, `powerExponentialLambertEpsilon_pos`, `tendsto_powerExponentialLambertEpsilon_nhdsGT_zero`, `principalPowerExponentialPhase_isEquivalent_rpow`, `tendsto_lowerPowerExponentialPhase_nhdsGT_zero_atTop`, `lowerPowerExponentialPhaseIntrinsicMain`, and `lowerPowerExponentialPhase_sub_intrinsicMain_tendsto_zero`: along `x ↓ 0`, the principal root is equivalent to `(x/A)^(1/m)`, while the lower root diverges and has only the proved intrinsic `epsilon`-coordinate two-term remainder.  The bridges are `lowerPowerExponentialPhase_rate_one`, `generalizedLambertCoordinate_argument_mem_Ioo`, `generalizedLambertCoordinate_argument_mem_Ico`, `generalizedLambertCoordinate_solves_saddle_of_mem`, `powerExponentialSaddle_one_one_log_two`, `powerExponentialPeak_one_one_log_two`, `lowerPowerExponentialPhase_one_one_log_two`, `fabiusPrincipalLambertPhase`, `fabiusSaddle_eq_iff_eq_principal_or_eq_lower`, `fabiusPrincipalLambertPhase_ne_fabiusLambertPhase`, `fabiusPrincipalLambertPhase_continuousOn_Icc`, `fabiusLambertPhase_continuousOn_Ioc`, and `fabiusPrincipalLambertPhase_isEquivalent_id`; their root/continuity domains specialize respectively to `(0,exp(-1)/log 2]`, `(0,exp(-1)/log 2)`, `[0,exp(-1)/log 2]`, and `(0,exp(-1)/log 2]`.  No cleaned `L = log(A/x)` form, branch-point Puiseux law, or generic complete asymptotic series is claimed. |
| Second derivatives of scaled Lambert phases and exact Fabius phase curvature | `FabiusFunction.PowerExponentialLambertCurvature`, `FabiusFunction.PowerExponentialLambertFabiusCurvature` | The generic module exposes `deriv_principalPowerExponentialPhase_hasDerivAt`, `deriv_deriv_principalPowerExponentialPhase`, `deriv_lowerPowerExponentialPhase_hasDerivAt`, and `deriv_deriv_lowerPowerExponentialPhase`: for `m : ℕ` with `m ≠ 0`, `A > 0`, and `beta > 0`, both branches satisfy `lambda'' = lambda * (m - (m - beta*lambda)^2) / (x^2 * (m - beta*lambda)^3)` on `(0,peak)`.  It deliberately does not assert the generic square-root threshold or global shape classification.  The Fabius leaf exhaustively adds `fabiusLambertInflectionInput`, `fabiusLambertInflectionInput_mem_Ioo`, `fabiusLambertPhase_inflectionInput`, `deriv_deriv_fabiusLambertPhase`, `deriv_deriv_fabiusLambertPhase_pos_iff`, `deriv_deriv_fabiusLambertPhase_neg_iff`, `deriv_deriv_fabiusLambertPhase_eq_zero_iff`, `deriv_deriv_fabiusLambertPhase_inflectionInput`, `strictConvexOn_fabiusLambertPhase_left`, `strictConcaveOn_fabiusLambertPhase_right`, `fabiusPrincipalLambertPhase_eq_principalLambertW`, `fabiusPrincipalLambertPhase_continuousOn_Iic`, `fabiusPrincipalLambertPhase_hasDerivAt`, `deriv_fabiusPrincipalLambertPhase`, `deriv_fabiusPrincipalLambertPhase_hasDerivAt`, `deriv_deriv_fabiusPrincipalLambertPhase`, `deriv_deriv_fabiusPrincipalLambertPhase_pos`, `deriv_deriv_fabiusPrincipalLambertPhase_zero`, and `strictConvexOn_fabiusPrincipalLambertPhase`.  The lower phase has its unique inflection at `x* = 2 exp(-2)/log 2`, is strictly convex on `(0,x*]` and strictly concave on `[x*,peak]`; the principal phase is strictly convex on the whole closed half-line `(-∞,peak]`, with second derivative `2 log 2` at zero.  Neither module proves a branch-point vertical-tangent limit or Puiseux expansion. |
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
| Fixed-length Fabius increments and exact inverse modulus | `FabiusFunction.InverseModulus` | Exhaustive public surface (one definition and 31 theorems): `fabiusIntervalMass`; `fabiusIntervalMass_reflect`, `fabiusIntervalMass_eq_zero_of_add_nonpos`, `fabiusIntervalMass_eq_zero_of_one_le`, `monotoneOn_fabiusIntervalMass_firstHalf`, `antitoneOn_fabiusIntervalMass_secondHalf`, `strictMonoOn_fabiusIntervalMass_firstHalf`, `strictAntiOn_fabiusIntervalMass_secondHalf`, `fabiusReal_sub_le_sub`, `fabiusReal_lt_fabiusIntervalMass_of_mem_Ioo`, `fabiusIntervalMass_eq_fabiusReal_iff`, `fabiusReal_sub_lt_sub`, `fabiusReal_sub_eq_sub_iff`, `fabiusReal_add_le`, `fabiusReal_add_eq_iff`, `fabiusInv_sub_le_sub_of_mem_Icc`, `fabiusInv_sub_eq_sub_iff_of_mem_Icc`, `fabiusInv_sub_le_sub_of_le`, `fabiusInv_sub_le_sub`, `fabiusInv_add_le`, `abs_fabiusInv_sub_le`, `abs_fabiusInv_sub_eq_iff_of_mem_Icc`, `dist_fabiusInv_le`, `fabiusInv_min_one`, `isGreatest_abs_fabiusInv_sub`, `sSup_abs_fabiusInv_sub_eq`, `isGreatest_abs_fabiusInv_sub_Icc`, `sSup_abs_fabiusInv_sub_Icc_eq`, `abs_fabiusInv_sub_lt_of_abs_sub_lt_fabiusReal`, `abs_fabiusInv_sub_le_of_abs_sub_le_fabiusReal`, `fabiusReal_le_abs_sub_of_le_abs_fabiusInv_sub`, `forall_abs_fabiusInv_sub_lt_iff`.  Nonnegative increments are reflection-invariant, vanish on the two constant tails, and have global weak shape; for `0 < h <= 1` they are strictly monotone on the maximal branches `[-h,(1-h)/2]` and `[(1-h)/2,1]`.  Inside `[0,1]`, the endpoint intervals are the only nondegenerate least-mass intervals, which gives the exact equality cases for constrained forward superadditivity and for the ordered and absolute inverse-gap bounds.  Those inverse equality classifications deliberately remain unit-interval statements, because clamping creates additional global cases.  The clamped inverse also has global gap bounds and subadditivity, absolute and metric self-moduli, saturation at one, attained exact `IsGreatest`/`sSup` moduli at every nonnegative radius over both all real inputs and unit-interval inputs, and the final four effective-injectivity statements.  This structural module alone does not construct an explicit recursive denominator; that effective layer is supplied by `FabiusInverseEffectiveContinuity` below. |
| Effective dyadic continuity of the totalized inverse | `FabiusFunction.FabiusInverseEffectiveContinuity` | Exhaustive public surface (two definitions and 12 theorems): `inverseFabiusFactorialDenominator`, `inverseFabiusDeltaDenominator`; `inverseFabiusFactorialDenominator_eq`, `inverseFabiusFactorialDenominator_primrec`, `inverseFabiusDeltaDenominator_primrec`, `fabiusReal_inverse_two_pow_one_term_lower_bound`, `inv_inverseFabiusFactorialDenominator_le_fabiusReal`, `inverseFabiusFactorialDenominator_le_deltaDenominator`, `inv_inverseFabiusDeltaDenominator_le_fabiusReal`, `abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_factorialDenominator`, `abs_fabiusInv_sub_le_inverse_two_pow_of_le_factorialDenominator`, `abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_deltaDenominator`, `abs_fabiusInv_sub_le_inverse_two_pow_of_le_deltaDenominator`, and `fabiusInv_effectivelyUniformContinuous`.  For `r > 0`, the positive zeroth recurrence term gives `1 / (2^(r.choose 2) * (r+1)! * (2^r-1)) ≤ F(2^-r)`.  Hence the stronger factorial denominator `D!(r)=2^((r+1).choose 2)*(r+1)!` and the report denominator `DDelta(r)=2^((r+1).choose 2)*(r+1)^(r+1)` satisfy `1/D!(r) ≤ F(2^-r)` and `1/DDelta(r) ≤ F(2^-r)`, with `D!(r) ≤ DDelta(r)`.  Both natural-valued denominators are primitive recursive.  For either denominator, a strict input bound gives the strict inverse-output bound `< 2^-r`, while the corresponding closed input bound gives `≤ 2^-r`.  Taking `r=n` certifies `EffectivelyUniformContinuous (fabiusInv F hF)`.  This module itself does not construct the downstream sequential realizer or combined `IsComputableRealFunction` theorem; those are supplied by `EffectiveMonotoneInverse` and `FabiusInverseComputable`.  It also does not prove the logarithmic selector `r(n)`, an exact least/ceiling denominator, or an input-bit complexity bound. |
| Logarithmic reciprocal modulus for the totalized inverse | `FabiusFunction.FabiusInverseLogarithmicModulus` | Exhaustive public surface (three definitions and 15 theorems): `inverseFabiusLogarithmicOrder`, `inverseFabiusLogarithmicFactorialDenominator`, `inverseFabiusLogarithmicDeltaDenominator`; `inverseFabiusLogarithmicOrder_eq_succ_log2`, `inverseFabiusLogarithmicOrder_primrec`, `inverseFabiusLogarithmicOrder_isLeast`, `inverseFabiusLogarithmicOrder_le_self`, `inverseFabiusLogarithmicFactorialDenominator_of_pos`, `inverseFabiusLogarithmicDeltaDenominator_of_pos`, `inverseFabiusLogarithmicFactorialDenominator_primrec`, `inverseFabiusLogarithmicDeltaDenominator_primrec`, `inverseFabiusLogarithmicFactorialDenominator_le_deltaDenominator`, `abs_fabiusInv_sub_lt_inv_nat_of_lt_logarithmicFactorialDenominator`, `abs_fabiusInv_sub_lt_inv_nat_of_le_logarithmicFactorialDenominator`, `abs_fabiusInv_sub_lt_inv_nat_of_lt_logarithmicDeltaDenominator`, `abs_fabiusInv_sub_lt_inv_nat_of_le_logarithmicDeltaDenominator`, `fabiusInv_effectivelyUniformContinuous_logarithmic`, and `fabiusInv_effectivelyUniformContinuous_logarithmicDelta`.  The primitive-recursive selector is exactly `r(n)=Nat.log2 n+1`; for `n>0` it is the least natural `r` satisfying `n<2^r` and obeys `r(n)≤n`.  Both logarithmic denominators use value `1` at zero and, at positive `n`, compose their dyadic predecessor with `r(n)`; both are primitive recursive, and the factorial denominator is no larger than the Delta denominator.  For either denominator, both strict and closed input thresholds imply the strict reciprocal output bound `<1/n`, because `2^-r(n)<1/n`.  Each denominator separately witnesses `EffectivelyUniformContinuous (fabiusInv F hF)`.  The tolerant-bisection realizer, `SequentiallyComputable` inverse, and combined `IsComputableRealFunction` theorem are supplied downstream by `EffectiveMonotoneInverse` and `FabiusInverseComputable`; the exact endpoint-mass ceiling denominator and input-bit asymptotics remain outside Lean. |
| Generic tolerant monotone inversion on the unit interval | `FabiusFunction.EffectiveMonotoneInverse` | Exhaustive public surface (two definitions and six theorems): `Fabius.SequentiallyComputableOn`, `Fabius.unitClamp`; `Fabius.unitClamp_sequentiallyComputable`, `Fabius.tolerantDifference_error`, `Fabius.tolerantDifference_safe_updates`, `Fabius.tolerantDifference_inconclusive`, `Fabius.tolerantBisection_correct`, and `Fabius.effectiveInversionOn_Icc`.  At requested precision `p`, the natural-number realizer performs exactly `p` dyadic halvings, carrying a bracket index and an optional accepted numerator.  Exact signed-code comparisons take the left branch when `U+4<L`, the right branch when `L+4<U`, and otherwise certify that the midpoint already has inverse error `<2^-p`; an accepted numerator is doubled through the remaining depths so the final code always has denominator `2^p`.  The final bracket endpoint covers the no-hit case, yielding a uniform `Computable₂` name with error `≤2^-p`.  `effectiveInversionOn_Icc` consumes a supplied computable positive reciprocal inverse modulus; the adjacent gap module constructs one from rational gap lower bounds. |
| Effective inversion from computable positive rational dyadic gaps | `FabiusFunction.EffectiveGapInverse` | Exhaustive 4+4 public surface: `Fabius.EffectivelyUniformContinuousOn`, the structure `Fabius.ComputablePositiveRationalSequence`, `Fabius.ComputablePositiveRationalSequence.value`, `Fabius.ComputablePositiveRationalSequence.reciprocalDenominator`, `Fabius.ComputablePositiveRationalSequence.reciprocalDenominator_spec`, `Fabius.inverseModulus_of_positiveRationalGap`, `Fabius.effectiveInversionOn_Icc_of_computablePositiveRationalGap`, and `Fabius.clampedEffectiveInversion_of_computablePositiveRationalGap`.  A sequence packages computable positive natural numerators and denominators; `denominator p / numerator p + 1` is computable, positive, and has reciprocal strictly below its encoded rational value.  For a strict increasing inverse pair on `[0,1]`, a lower bound `α.value p ≤ f (x + 2^-p) - f x` for every `x ∈ [0,1-2^-p]` yields the inverse modulus.  Adding a computable dyadic oracle and both interval maps gives sequential computability and effective uniform continuity of `g` on `[0,1]`.  The total theorem certifies exactly `x ↦ g (unitClamp x)`; it agrees with `g` on `[0,1]` but makes no claim about the un-clamped values of `g` outside that interval.  Together with `EffectiveMonotoneInverse` 2+6 and `FabiusInverseComputable` 0+1, the effective-inverse union is three modules and seventeen declarations. |
| Total computability of the inverse Fabius function | `FabiusFunction.FabiusInverseComputable` | Exhaustive public surface (zero definitions and one theorem): `Fabius.fabiusInv_isComputableRealFunction`.  It instantiates generic tolerant inversion with the centered-spline dyadic oracle for `fabiusReal` and `inverseFabiusDeltaDenominator`, uses `unitClamp` to turn arbitrary input names into unit-interval names without changing the totalized inverse, and combines the resulting total `SequentiallyComputable` realizer with the logarithmic-Delta `EffectivelyUniformContinuous` witness.  This is a computability certificate, not a practical running-time or input-bit complexity bound. |
| Elementary functions and non-elementarity | `FabiusFunction.ElementaryFunction`, `FabiusFunction.AlgebraicBranch`, `FabiusFunction.InverseBranch`, `FabiusFunction.NotElementary`, `FabiusFunction.InverseNotElementary` | `IsElementary`, `IsElementary.comp`, `IsElementary.rpow_of_ne_zero`, `IsElementary.dense_analyticLocus`, `analyticDenseOn_of_algebraic`, `canonical_fabius_not_isElementary_on_Ioo`, `canonical_fabius_not_isElementary`, `canonical_fabius_not_algebraicBranch_on_Ioo`, `IsElementaryOrInverse`, `fabiusInv_not_analyticAt`, `canonical_fabiusInv_not_isElementary_on_Ioo`, `canonical_fabiusInv_not_isElementaryOrInverse_on_Ioo` |
| Computable-real-function theorems | `FabiusFunction.FabiusComputableSpline` | `fabiusSplineApproxPR_computable`, `extendedFabiusSplineApproxPR_computable`, `fabius_isComputableRealFunction`, `globalFabius_isComputableRealFunction` |
| Gaussian-polynomial continuity and the finite-product quotient bridge | `FabiusFunction.GaussianBinomialContinuity` | Retained 0+3 theorem inventory: `continuous_gaussianBinomial`, `tendsto_gaussianBinomial_nhds_one`, and `gaussianBinomial_eq_finiteQPochhammerIn_div`. |
| Jacobi triple product and Euler pentagonal sums | `FabiusFunction.JacobiTripleProduct` | Retained 2-definition/25-theorem inventory: finite triple-product polynomial and field forms, the bilateral Jacobi `HasSum` identities, and pentagonal and paired-pentagonal `HasSum` corollaries. |
| Infinite q-binomial and reciprocal Euler theorems | `FabiusFunction.QBinomialTheoremInfinite` | Retained 1-definition/22-theorem q-facing inventory: comparison and norm bounds, the fixed-column Gaussian limit, Euler product, analytic q-binomial theorem, and reciprocal Euler `HasSum`; the shared finite zero-left identity is imported from `GaussianBinomialAtOne`. |
| Weighted q-Pascal summation | `FabiusFunction.QPascalSummation` | Retained 0+4 theorem inventory: `sum_gaussianBinomial_succ_mul`, `sum_gaussianBinomial_succ_mul'`, `Commute.gaussianBinomial_left`, and `Commute.gaussianBinomial_right`. |
| Quantum-plane binomial expansion | `FabiusFunction.QuantumBinomial` | Retained 0+2 theorem inventory: `quantumPlane_mul_pow` and `quantum_binomial`. |
| Rogers--Szegő recurrences and generating series | `FabiusFunction.RogersSzegoPolynomial` | Retained 1-definition/9-theorem inventory: the zero, row-sum, successor, dilation, and three-term laws, the Gaussian successor factor identity, summability and Euler antidiagonal convolution, and `hasSum_rogersSzego_generating`. |
| Latest q-calculus closure: bounds, Heine/q-Gauss, complex order, basic hypergeometric series, and q-multinomials | `FabiusFunction.QPochhammerInfiniteBounds`, `FabiusFunction.HeineTransformation`, `FabiusFunction.QGaussSummation`, `FabiusFunction.QPochhammerComplexOrder`, `FabiusFunction.BasicHypergeometricSeries`, `FabiusFunction.QMultinomial` | Exhaustive module counts are respectively 0+5, 2+5, 0+2, 1+4, 2+5, and 1+9: six definitions and thirty theorems.  The APIs preserve their explicit strict-contraction, nonvanishing, and denominator hypotheses; the q-multinomial recursion and cleared product identity are division-free, while quotient statements remain conditional. |
| Gaussian palindromicity, q-exponentials, Jackson integration, and theta quasi-periodicity | `FabiusFunction.GaussianBinomialPalindromic`, `FabiusFunction.QExponential`, `FabiusFunction.JacksonIntegral`, `FabiusFunction.ThetaQuasiPeriodicity` | Exhaustive module counts are 0+14, 3+8, 1+7, and 1+6: five definitions and thirty-five theorems.  They give the degree, monicity, coefficient reversal, mean identity, and total linear-coefficient classifier for Gaussian polynomials; the two q-exponentials and their q-derivative laws; Jackson's fundamental theorem and integration by parts; and the bilateral-theta product, quasi-periodicity, and exact zero criterion.  The analytic statements retain their explicit strict-contraction, nonzero-variable, convergence, and nonvanishing hypotheses. |
| Universal Gaussian structure, q-Pochhammer derivatives, and Jacobi's cubic identity | `FabiusFunction.GaussianBinomialPolynomialStructure`, `FabiusFunction.QPochhammerLogDerivative`, `FabiusFunction.QPochhammerOrderDerivative`, `FabiusFunction.JacobiCubic` | Exhaustive module counts are 0+5, 0+10, 0+3, and 0+2: twenty theorems and no definitions.  They give universal Gaussian degree, monicity, constant coefficient, and reflection symmetry over `ℕ[X]`; derivative and Lambert-series formulas for the infinite q-Pochhammer product on the unit disc; the complex-order derivative under a nonzero nome and `‖a*q^α‖ < 1`; and Jacobi's cubic identity for `‖q‖ < 1`. |
| Cyclotomic factorization and central Gaussian reduction | `FabiusFunction.CyclotomicFactorization`, `FabiusFunction.CentralQBinomialReduction` | Exhaustive module counts are 0+7 and 0+6: thirteen theorems and no definitions.  The first factors `(X;X)_n` and `[n,k]_X` into cyclotomic polynomials, with the Gaussian factorization stated over an integral domain.  The second proves finite-symbol sign pairing, even--odd dissection, ring-hom naturality, and the division-free central identity `[2k,k]_(q²)(q²;q²)_k=(q;q²)_k(-q;q)_(2k)` over every commutative ring; its quotient corollary assumes both denominators are nonzero. |
| Root-of-unity Gaussian arithmetic, q-Lucas, and MacMahon q-Catalan | `FabiusFunction.CyclotomicDivisibility`, `FabiusFunction.PrimitiveRootBlock`, `FabiusFunction.QCatalan`, `FabiusFunction.QLucas` | Exhaustive counts are 0+3, 0+3, 1+11, and 0+7: one definition and twenty-four theorems.  The tranche proves the cyclotomic carry criterion, Gaussian values and complete q-Pochhammer blocks at primitive roots, the q-Lucas theorem over integral domains, and the integral q-Catalan polynomial with degree `n(n-1)` and Catalan specialization at `q=1`. |
| Newton interpolation and the Jackson q-beta integral | `FabiusFunction.NewtonInterpolation`, `FabiusFunction.QBetaIntegral` | Exhaustive counts are 3+19 and 1+8: four definitions and twenty-seven theorems.  The Newton module constructs triangular coefficients and node-qualified interpolants, proves evaluation, uniqueness, divided differences, and the explicit geometric-grid denominator formula, and retains the seven-name `newtonInterpolant` compatibility API.  The q-beta module defines the Jackson integral, proves its infinite-product and q-gamma evaluations for `0<q<1` and positive arguments, and derives symmetry, positivity, and both successor recurrences. |
| Integer/complex upper Gaussian coefficients and q-Pfaff--Saalschütz | `FabiusFunction.GaussianBinomialInteger`, `FabiusFunction.GaussianBinomialComplexOrder`, `FabiusFunction.QPfaffSaalschutz` | Exhaustive counts are 1+10, 1+5, and 0+3: two definitions and eighteen theorems.  The first module extends Gaussian coefficients to integer upper indices, proves both q-Pascal laws and negative-index reflection, and derives the reciprocal finite q-binomial series.  The second uses principal complex powers to package complex upper indices and the generalized reciprocal and finite q-binomial series.  The third proves the terminating balanced `₃φ₂` summation algebraically over a field.  All nonzero-nome, strict-contraction, and displayed denominator hypotheses remain explicit. |
| Terminating `₂φ₁` reversal | `FabiusFunction.TwoPhiOneReversal` | Exhaustive count: two definitions and twelve theorems.  Definitions: `twoPhiOneFinite`, `twoPhiOneReflection`.  Theorems: `choose_two_add_succ_choose_two`, `finiteQPochhammerIn_sub_eq`, `finiteQPochhammerIn_reversal_ne_zero`, `finiteQPochhammerIn_inv_pow_self`, `twoPhiOneReflection_involutive`, `twoPhiOneFinite_reversal`, `twoPhiOneFinite_reversal_twice`, `twoPhiOneFinite_eq_sum_twoPhiOneTerm`, `twoPhiOne_eq_twoPhiOneFinite_inv_pow`, `twoPhiOne_reversal`, `twoPhiOne_reversal_twice`, `twoPhiOne_one_eq_twoPhiOneFinite_zero`.  The monograph label `lem:2phi1-reversal` is **Exact**: the public result is stated for the actual `twoPhiOne` tsum, the terminating-series bridge needs no analytic convergence bounds, the reflected parameter map is involutive, and the two displayed prefactors cancel on a second application.  The reversal itself retains exactly `q,a,c,z ≠ 0` and the three displayed finite-product nonvanishing assumptions; its separate `n=0` bridge includes `q=0`. |
| The two q-Chu--Vandermonde sums | `FabiusFunction.QChuVandermonde` | Exhaustive count: zero definitions and ten theorems: `two_mul_choose_two`, `mul_sub_one_eq_mul_sub_add`, `finiteQPochhammerIn_div_eq_sum_chu`, `q_chu_vandermonde_first`, `finiteQPochhammerIn_div_eq_sum_chu_second`, `twoPhiOneFinite_mul_finiteQPochhammerIn_eq_chu_second`, `q_chu_vandermonde_second`, `q_chu_vandermonde_second_by_reversal`, `twoPhiOne_q_chu_vandermonde_first`, and `twoPhiOne_q_chu_vandermonde_second`.  The monograph label `cor:q-chu` is **Exact**: its two formulas have actual-`twoPhiOne` wrappers on the full displayed rational domain `q ≠ 0`, `A ≠ 0`, `(q;q)_n ≠ 0`, `(C;q)_n ≠ 0`; in particular the second formula assumes neither `C ≠ 0` nor `(A;q)_n ≠ 0`.  The label `prop:qchu2-by-reversal` is **Partial**: `q_chu_vandermonde_second_by_reversal` records that proof only on the additional locus `C ≠ 0` and `(A;q)_n ≠ 0`, while the stronger full-domain finite and actual-tsum theorems use a direct denominator-cleared q-Cauchy proof.  Rational continuation and the cleared commutative-ring extension asserted in the prose remain unformalized. |
| Noncommutative q-multinomial theorem | `FabiusFunction.QuantumMultinomial` | Exhaustive count: zero definitions and five theorems.  Over an arbitrary semiring, pairwise relations `x_j*x_i = q*(x_i*x_j)` for `i<j`, together with commutation of `q` with every `x_i`, expand a power of the finite sum into ordered monomials weighted by `qMultinomial`.  The supporting API decomposes tuple antidiagonals, transports Gaussian symmetry to semirings, and proves coefficient commutation.  The result is finite and division-free; it makes no convergence claim. |
| Gaussian reciprocity and dimension-dominant bounds | `FabiusFunction.GaussianBinomialBounds` | Exhaustive count: zero definitions and six theorems.  `gaussianBinomial_inv` evaluates reciprocity over a field under `q ≠ 0` and `k ≤ n`; `one_le_gaussianBinomial`, `finiteQPochhammerIn_pow_le_one`, and `gaussianBinomial_le_inv_qPochhammerInfIn` give the nonnegative strict-contraction bounds; `pow_le_gaussianBinomial_of_one_lt` and `gaussianBinomial_le_pow_div_of_one_lt` transfer them to two-sided real bounds for `Q > 1`. |

The frontier-facing focused imports above expose exact finite or formal
algebra, and their names should not be read as stronger analytic conclusions.
The quarter-cell theorems concern the finite spline `reportFiniteFabiusApproximant`,
not a constructed finite inverse `G_n`; the Catalan--Gaussian filter is an
identity in `ℚ[[Q]]`, without convergence or an error bound.  The centered
Thue--Morse shell concerns the standalone sinc-product model, while the odd
DFT module is finite character algebra and does not prove a half-integer
aliasing formula or alias-error estimate.  Likewise, the geometric principal
specialization proves finite residual moments, not spectral-tail convergence.
The Lambert tranche goes further: it proves Bell/generalized-harmonic closed
forms for every finite residual, fixed-order phase extraction, and weighted
residual Big-O estimates, but no convergence of the literal infinite residual
series or uniformity as the row order or residual depth grows.  The full-order
centered parity API is coefficientwise formal
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

`EffectiveMonotoneInverse.lean` supplies the generic inverse realizer without
ever deciding equality of computable reals.  For an output precision `p`, it
runs a fixed-depth dyadic bisection for exactly `p` steps.  At each midpoint,
forward and target dyadic approximations are compared by natural-number
arithmetic with three outcomes: a certified positive difference moves the
right endpoint, a certified negative difference moves the left endpoint, and
an inconclusive comparison is already a successful inverse approximation by
the supplied reciprocal inverse modulus.  The optional accepted numerator is
doubled through later frozen steps, so both the successful and no-hit paths
finish at denominator `2^p` with error at most `2^-p`.

`EffectiveGapInverse.lean` closes the generic gap-to-modulus step.  It packages
computable positive rational lower bounds for every dyadic forward gap,
constructs the computable reciprocal denominator, derives the inverse modulus,
and proves sequential computability plus effective uniform continuity on the
unit interval.  Its total result is precisely the clamped extension
`fun x => g (unitClamp x)`; it does not assert that an arbitrary inverse `g`
has the same behavior outside `[0,1]`.

`FabiusInverseComputable.lean` applies the fixed-depth construction to `fabiusReal`, its
centered-spline dyadic oracle, and `inverseFabiusDeltaDenominator`.  Computable
unit clamping extends the unit-interval realizer to arbitrary input names, and
the logarithmic-Delta continuity theorem supplies the other clause of
`Fabius.fabiusInv_isComputableRealFunction`.  The generic Lean theorem assumes
the computable positive reciprocal inverse modulus as input.  The adjacent
generic gap module derives such a modulus from a supplied computable positive
rational gap lower-bound sequence; constructing a particular sequence remains
an explicit hypothesis of that interface.

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

In the current compiled tree,
`RvachevMomentAppell.lean` exports six public definitions:
`Fabius.rvachevRawMomentRat`, `Fabius.rvachevReciprocalMomentRat`,
`Fabius.rvachevAppellPolynomialRat`, `Fabius.rvachevAppellPolynomial`, and
`Fabius.rvachevDeconvolvedPolynomial`, together with the linear-map package
`Fabius.rvachevDeconvolutionLinearMap`.  Its thirty-three public theorems are
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
`Fabius.rvachevDeconvolvedPolynomial_injective`,
`Fabius.integral_eval_rvachevDeconvolvedPolynomial_add_mul_rvachev`,
`Fabius.integral_eval_rvachevDeconvolvedPolynomial_sub_mul_rvachev`,
`Fabius.integral_eval_rvachevAppellPolynomial_sub_mul_rvachev`, and
`Fabius.integral_eval_rvachevAppellPolynomial_mul_rvachev_eq_zero`.  They
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
`up` recovers the original polynomial.  Reflection invariance of the even
Rvachev density also turns this additive smoothing into the centered
`x - y` convolution for every real polynomial; the corresponding centered
Appell identity recovers `x ^ n`, and every positive-degree Appell polynomial
has Rvachev mean zero.  These statements do not supply an analytic reciprocal
MGF or Appell generating series, a literal differential-operator expansion,
reciprocal/deconvolution parity, or the displayed low reciprocal coefficients.

In the current compiled tree,
`RvachevPolynomialSynthesis.lean` exports no public definitions and exactly
five public theorems:
`Fabius.tsum_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`,
`Fabius.normalized_tsum_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`,
`Fabius.sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`,
`Fabius.normalized_sum_Ioo_rvachevDeconvolvedPolynomial_mul_shifted_rvachevUp`,
and
`Fabius.normalized_tsum_shifted_rvachevDeconvolvedPolynomial_mul_rvachevUp`.
For every nonzero natural mesh `M` and polynomial of degree at most `v₂(M)`,
they give both global `tsum` synthesis and, on `[-1,1]`, its exact finite
`k ∈ (-2M,2M)` form with the `1/M` normalization.  The fifth theorem holds
for arbitrary real phase `θ` and real `x`: it samples `up` at
`M⁻¹ * (θ + k)`, evaluates the deconvolved polynomial at
`x - M⁻¹ * (θ + k)`, and reconstructs `P.eval x`.  Taking
`M = 2 ^ N` formalizes arbitrary-phase polynomial reproduction through every
degree `n ≤ N`.

The compiled `RvachevSuperconvergentSynthesis.lean` extension exports exactly
one public definition and eight public theorems.  Its definition
`Fabius.IsRvachevSuperconvergentPhase` selects `0,1/2` when `v₂(M)+1` is odd
and `1/4,3/4` when it is even.  The theorem
`Fabius.isRvachevSuperconvergentPhase_two_pow_iff` rewrites this at
`M=2^N` as endpoint phases for even `N` and quarter phases for odd `N`.
The remaining seven theorems are
`Fabius.tsum_quarter_monomial_eq_integral_of_even_deg`,
`Fabius.tsum_three_quarters_monomial_eq_integral_of_even_deg`,
`Fabius.tsum_shifted_monomial_eq_integral_superconvergent`,
`Fabius.tsum_shifted_polynomial_eq_integral_superconvergent`,
`Fabius.integral_polynomial_mul_rvachevUp_eq_normalized_tsum_superconvergent`,
`Fabius.normalized_tsum_shifted_rvachevDeconvolvedPolynomial_mul_rvachevUp_superconvergent`,
and
`Fabius.normalized_tsum_shifted_rvachevAppellPolynomial_mul_rvachevUp_superconvergent`.
For every nonzero natural mesh they prove exactness through degree
`v₂(M)+1`, including physical-coordinate quadrature, deconvolved-polynomial
reconstruction, and the explicit Appell specialization.  This arbitrary-`M`
result is stronger than the dyadic-only manuscript claim.  The selected
phases are exact representatives rather than a modulo-integer wrapper or a
classification, and the module proves neither maximality nor positivity or
rationality of the quadrature.

The current-tree module `LagrangeRvachevSynthesis.lean` exports exactly two
public definitions, `Fabius.lagrangeRvachevDecoder` and
`Fabius.lagrangeRvachevAtomCoefficient`, and exactly seven public theorems:
`Fabius.natDegree_lagrangeBasis_le_card_sub_one`,
`Fabius.natDegree_lagrangeInterpolate_le_card_sub_one`,
`Fabius.normalized_sum_Ioo_lagrangeRvachevDecoder_mul_shifted_rvachevUp`,
`Fabius.normalized_sum_Ioo_lagrangeRvachevDecoder_eval_node`,
`Fabius.lagrangeRvachevAtomCoefficient_eq_deconvolved_interpolate`,
`Fabius.sum_Ioo_lagrangeRvachevAtomCoefficient_mul_shifted_rvachevUp`, and
`Fabius.sum_lagrangeRvachevDecoder_eq_one`.  For any finite real node family,
the first two bound the basis and interpolant degrees by one less than the
node count without requiring distinctness.  A nonzero mesh whose two-adic
valuation reaches that bound gives exact cardinal and full-interpolant
synthesis on `[-1,1]`; distinct nodes turn the cardinal formula into the
componentwise Kronecker-delta identity, and distinct nonempty nodes make each
fixed lattice-sample decoder row sum to one.  Thus the generic finite-node
dictionary, its linear data-to-atom coefficients, componentwise
biorthogonality, and exact finite interpolation loop are formalized.  No
theorem here gives the geometric-node Gaussian q-binomial/q-Pochhammer or
elementary-symmetric closed form for the decoder entries, packages the
componentwise identity as a matrix/right-inverse equation, or proves an
optimal or minimum-variation decoder.

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

The seven modules in this tranche have respectively `6/33`, `0/5`, `1/8`,
`2/7`, `1/7`, `6/7`, and `5/25` public definition/theorem inventories, for
exactly 113 public declarations in total.  The added `1/8` inventory is
`RvachevSuperconvergentSynthesis`.  Universal whole-space mesh sharpness is now proved,
but target-specific minimality for an individual Legendre polynomial or
partial sum is not.  The modules also do not assert an
analytic reciprocal-MGF or Appell generating-series realization of
deconvolution, a literal differential-operator expansion, the displayed low
reciprocal coefficients, reciprocal/deconvolution parity or the displayed closed
formulas for the deconvolved Legendre family,
coefficient rationality for the atom rows, equality of the fixed-scale and
separately scaled coefficient vectors, a geometric closed-form or bundled
matrix form of the finite-node decoder, decoder optimality, an unconditional
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
