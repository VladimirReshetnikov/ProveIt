import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Surreal.HahnSeries.RootQuadrature

/-!
# Fejér densities: nonclosure with a fixed Haar leading coefficient

This file proves `herg:thm:fejer` of `docs/surcomplex/hahn-herglotz-positivity/article.tex`: the
nonclosedness of the positive coefficientwise Hahn-probability cone of `herg:thm:quadrature`
persists when the leading coefficient is exactly Haar measure `m` throughout and every
approximating coefficient measure is absolutely continuous with respect to `m`.

## Setting

As in `Surreal.HahnSeries.RootQuadrature`, the ordinary circle is `AddCircle T` for any
`T > 0`, its point `x` is `ζ = toCircle x`, `ζ^k` is `fourier k x`, the point `0` is `ζ = 1`,
`m` is the normalized `haarAddCircle`, and `δ_1` is the Dirac mass at `0`. With `ε = t^η`,
`0 < η`, in any linearly ordered exponent set with a zero, a coefficientwise Hahn measure is a
family of finite signed measures on a well-ordered support, its set function is
`Surreal.NullIdeal.coefSeries`, and coefficientwise weak-* convergence is
`Surreal.RootQuadrature.CoefWeakStarTendsto`. The ring form of `ρ_N` and the Hahn lower bound
of its density use an ordered abelian group of exponents.

## Main results

* The Fejér kernel `F_N(ζ) = |∑_{j=0}^N ζ^j|² / (N + 1)` (`fejerKernel`) satisfies
  `0 ≤ F_N ≤ N + 1` (`fejerKernel_nonneg`, `fejerKernel_le`) and has the Fourier expansion
  `F_N(ζ) = ∑_{|k| ≤ N} (1 - |k|/(N + 1)) ζ^k` (`fejerKernel_eq_sum_fourier`,
  `fejerCoeff_of_natAbs_le`); the coefficient count is `card_filter_sub_eq`.
* `F_N m` (`fejerMeasure`, the measure with density `F_N` with respect to `m`) is a probability
  measure whose Fourier coefficients are `(1 - |n|/(N + 1))_+` (`moment_fejerMeasure`), and
  `F_N m → δ_1` weak-* (`tendsto_integral_fejerMeasure`, `tendsto_fejerProbabilityMeasure`).
* `herg:thm:fejer`: `ρ_N = (1 + ε - ε F_N) m = m + t^η (m - F_N m)` is the coefficient family
  `fejerFamily N` on the fixed support `{0, η}`. It is a positive coefficientwise Hahn
  probability measure (`fejerFamily_nonneg`, via the two-scale criterion `herg:cor:twoscale`,
  and `coefSeries_fejerFamily_univ`); its exponent-`0` coefficient is exactly `m`
  (`fejerFamily_zero`, `coeff_zero_coefSeries_fejerFamily`); its exponent-`η` coefficient is
  `m - F_N m = (1 - F_N) m` (`fejerFamily_eq_withDensityᵥ`), so every coefficient measure is
  absolutely continuous with respect to `m` (`fejerFamily_absolutelyContinuous`), and so is
  every negative part (`negPart_fejerFamily_absolutelyContinuous`); the coefficient variations
  are at most `1` and `2` (`totalVariation_fejerFamily_zero_le`, `totalVariation_fejerFamily_le`),
  the first being exactly `1` (`totalVariation_fejerFamily_zero`).
  For an ordered abelian group of exponents, `ρ_N(A) = (1 + ε) m(A) - ε ∫_A F_N dm`
  (`coefSeries_fejerFamily_eq`) and the Hahn density satisfies
  `1 + ε - ε F_N(ζ) ≥ 1 - N ε > 0` in `Lex ℝ((t^Γ))` (`one_sub_le_fejerHahnDensity`,
  `one_sub_natCast_mul_pos`). As `N → ∞`, `ρ_N` converges coefficientwise weak-* to
  `m + t^η (m - δ_1)` (`coefWeakStarTendsto_fejerFamily`), whose exponent-`0` coefficient is
  still `m`, which is not positive (`Surreal.NegativeAtomMeasure.negAtomFamily_not_positive`),
  and whose exponent-`η` negative part is not absolutely continuous with respect to `m`
  (`negPart_negAtomFamily_not_absolutelyContinuous`): the null-ideal condition is lost in the
  limit. The package is `fejer`, and the nonclosedness statement is
  `not_closed_positive_cone_haar`.

## Scope

The weak-* convergence `F_N m → δ_1` is proved from the convergence of the Fourier coefficients
`(1 - |n|/(N + 1))_+ → 1` through `Surreal.RootQuadrature.tendsto_integral_of_tendsto_moment`,
not from the pointwise kernel bound `F_N(ζ) ≤ 4/((N + 1)|1 - ζ|²)` used in the source's proof;
that bound is not formalized. No Hahn-valued integral `∫_A (1 + ε - ε F_N) dm` is formed: the
Hahn lower bound of the density is a pointwise inequality, linked to `ρ_N` only through
`fejerFamily_eq_withDensityᵥ` and `coefSeries_fejerFamily_eq`, and positivity of `ρ_N` is proved
instead through the two-scale criterion `herg:cor:twoscale` (`fejerFamily_nonneg`). As in
`Surreal.HahnSeries.RootQuadrature`, no topology on the space of coefficientwise measures is
constructed, and nonclosedness is the existence of a convergent sequence of positive
probabilities with a nonpositive limit. The closing remark on the classical Fejér reconstruction
of Toeplitz-positive sequences over `ℂ` is not formalized.
-/

namespace Surreal.FejerNonclosure

open MeasureTheory AddCircle Filter Topology _root_.HahnSeries Surreal.NullIdeal
  Surreal.NegativeAtomMeasure Surreal.RootQuadrature
open scoped ComplexConjugate

noncomputable section

section Count

/-- The number of pairs `(j, l)` with `0 ≤ j, l ≤ N` and `j - l = k` is `N + 1 - |k|`, with
truncated subtraction, so that it is `0` for `|k| > N`. -/
theorem card_filter_sub_eq (N : ℕ) (k : ℤ) :
    ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
      fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = k).card = N + 1 - k.natAbs := by
  rw [← Finset.card_range (N + 1 - k.natAbs)]
  rcases Int.natAbs_eq k with hk | hk <;> generalize k.natAbs = m at hk ⊢ <;> subst hk
  · refine Finset.card_nbij' (fun p => p.2) (fun l => (l + m, l)) ?_ ?_ ?_ ?_
    · rintro ⟨a, b⟩ hp
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
        Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio] at hp ⊢
      omega
    · intro l hl
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
        Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio] at hl ⊢
      push_cast
      omega
    · rintro ⟨a, b⟩ hp
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
        Set.mem_setOf_eq] at hp
      simp only [Prod.mk.injEq, and_true]
      omega
    · intro l _
      rfl
  · refine Finset.card_nbij' (fun p => p.1) (fun l => (l, l + m)) ?_ ?_ ?_ ?_
    · rintro ⟨a, b⟩ hp
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
        Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio] at hp ⊢
      omega
    · intro l hl
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
        Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio] at hl ⊢
      push_cast
      omega
    · rintro ⟨a, b⟩ hp
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range,
        Set.mem_setOf_eq] at hp
      simp only [Prod.mk.injEq, true_and]
      omega
    · intro l _
      rfl

end Count

section Kernel

variable {T : ℝ}

/-- The geometric sum `∑_{j=0}^N ζ^j` as a continuous function on the circle. -/
def fejerSum (N : ℕ) : C(AddCircle T, ℂ) :=
  ∑ j ∈ Finset.range (N + 1), fourier (j : ℤ)

theorem fejerSum_apply (N : ℕ) (x : AddCircle T) :
    fejerSum N x = ∑ j ∈ Finset.range (N + 1), fourier (j : ℤ) x := by
  simp [fejerSum]

/-- The Fejér kernel `F_N(ζ) = |∑_{j=0}^N ζ^j|² / (N + 1)` of `herg:thm:fejer`. -/
def fejerKernel (N : ℕ) : C(AddCircle T, ℝ) :=
  ⟨fun x => ‖fejerSum N x‖ ^ 2 / (N + 1),
    ((continuous_norm.comp (fejerSum N).continuous).pow 2).div_const _⟩

theorem fejerKernel_apply (N : ℕ) (x : AddCircle T) :
    fejerKernel N x = ‖fejerSum N x‖ ^ 2 / (N + 1) :=
  rfl

/-- `herg:thm:fejer`: `0 ≤ F_N`. -/
theorem fejerKernel_nonneg (N : ℕ) (x : AddCircle T) : 0 ≤ fejerKernel N x :=
  div_nonneg (sq_nonneg _) (by positivity)

theorem norm_fejerSum_le (N : ℕ) (x : AddCircle T) : ‖fejerSum N x‖ ≤ N + 1 := by
  rw [fejerSum_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp

/-- `herg:thm:fejer`: `F_N ≤ N + 1`. -/
theorem fejerKernel_le (N : ℕ) (x : AddCircle T) : fejerKernel N x ≤ N + 1 := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  rw [fejerKernel_apply, div_le_iff₀ hN]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_fejerSum_le N x) 2
  nlinarith

/-- `F_N = (N + 1)⁻¹ ∑_{j, l ≤ N} ζ^{j - l}`, from `|s|² = s s̄` and `ζ̄^l = ζ^{-l}`. -/
theorem fejerKernel_eq_sum_sum (N : ℕ) (x : AddCircle T) :
    (fejerKernel N x : ℂ) = ((N : ℂ) + 1)⁻¹ *
      ∑ j ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (N + 1), fourier ((j : ℤ) - l) x := by
  have h : ((‖fejerSum N x‖ : ℝ) : ℂ) ^ 2 =
      ∑ j ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (N + 1), fourier ((j : ℤ) - l) x := by
    rw [← Complex.mul_conj', fejerSum_apply, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← fourier_neg, ← fourier_add, sub_eq_add_neg]
  rw [fejerKernel_apply, Complex.ofReal_div, Complex.ofReal_pow, h, div_eq_inv_mul]
  push_cast
  rfl

/-- The Fejér coefficient `(1 - |k|/(N + 1))_+`, written with truncated subtraction as
`(N + 1 - |k|)/(N + 1)`. -/
def fejerCoeff (N : ℕ) (k : ℤ) : ℝ :=
  ((N + 1 - k.natAbs : ℕ) : ℝ) / (N + 1)

theorem fejerCoeff_of_natAbs_le {N : ℕ} {k : ℤ} (hk : k.natAbs ≤ N) :
    fejerCoeff N k = 1 - |(k : ℝ)| / (N + 1) := by
  have hN : (N : ℝ) + 1 ≠ 0 := by positivity
  have habs : (k.natAbs : ℝ) = |(k : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [fejerCoeff, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one, sub_div, div_self hN,
    habs]

theorem fejerCoeff_of_lt {N : ℕ} {k : ℤ} (hk : N < k.natAbs) : fejerCoeff N k = 0 := by
  rw [fejerCoeff, Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero, zero_div]

theorem fejerCoeff_zero (N : ℕ) : fejerCoeff N 0 = 1 := by
  rw [fejerCoeff_of_natAbs_le (by simp)]
  simp

/-- `herg:thm:fejer`, the Fourier expansion of the Fejér kernel:
`F_N(ζ) = ∑_{|k| ≤ N} (1 - |k|/(N + 1)) ζ^k` (`fejerCoeff_of_natAbs_le`). -/
theorem fejerKernel_eq_sum_fourier (N : ℕ) (x : AddCircle T) :
    (fejerKernel N x : ℂ) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N, (fejerCoeff N k : ℂ) * fourier k x := by
  have hmaps : ∀ p ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
      (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2) p ∈ Finset.Icc (-(N : ℤ)) N := by
    rintro ⟨j, l⟩ hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_Icc]
    omega
  rw [fejerKernel_eq_sum_sum, ← Finset.sum_product',
    ← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hfib : ∀ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
      (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = k), fourier ((p.1 : ℤ) - p.2) x = fourier k x :=
    fun p hp => by rw [(Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, card_filter_sub_eq, nsmul_eq_mul,
    fejerCoeff]
  push_cast
  ring

end Kernel

section Measure

variable {T : ℝ} [Fact (0 < T)]

/-- The measure `F_N m`, with the Fejér kernel as density with respect to Haar measure. -/
def fejerMeasure (N : ℕ) : Measure (AddCircle T) :=
  haarAddCircle.withDensity fun x => ENNReal.ofReal (fejerKernel N x)

theorem integrable_fejerKernel (N : ℕ) :
    Integrable (fejerKernel (T := T) N) haarAddCircle :=
  (BoundedContinuousFunction.mkOfCompact (fejerKernel N)).integrable _

instance isFiniteMeasure_fejerMeasure (N : ℕ) : IsFiniteMeasure (fejerMeasure (T := T) N) :=
  isFiniteMeasure_withDensity_ofReal (integrable_fejerKernel N).hasFiniteIntegral

/-- Integrals against `F_N m` are integrals of `F_N f` against Haar measure. -/
theorem integral_fejerMeasure (N : ℕ) (f : AddCircle T → ℂ) :
    ∫ x, f x ∂fejerMeasure N = ∫ x, (fejerKernel N x : ℂ) * f x ∂haarAddCircle := by
  rw [fejerMeasure, integral_withDensity_eq_integral_toReal_smul
    (fejerKernel N).continuous.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [ENNReal.toReal_ofReal (fejerKernel_nonneg N x), Complex.real_smul]

/-- `(F_N m)(A) = ∫_A F_N dm`. -/
theorem fejerMeasure_real_apply (N : ℕ) {A : Set (AddCircle T)} (hA : MeasurableSet A) :
    (fejerMeasure N).real A = ∫ x in A, fejerKernel N x ∂haarAddCircle := by
  rw [measureReal_def, fejerMeasure, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_fejerKernel N).integrableOn
      (ae_of_all _ fun x => fejerKernel_nonneg N x),
    ENNReal.toReal_ofReal (setIntegral_nonneg hA fun x _ => fejerKernel_nonneg N x)]

/-- `∫ ζ^k dm = δ_{k0}`. -/
theorem integral_fourier_haarAddCircle (k : ℤ) :
    ∫ x, fourier k x ∂haarAddCircle (T := T) = if k = 0 then 1 else 0 := by
  have h := moment_haarAddCircle (T := T) (-k)
  rw [moment, neg_neg] at h
  rw [h]
  simp only [neg_eq_zero]

/-- The Fourier coefficients of `F_N m` are the Fejér coefficients:
`∫ ζ^{-n} F_N dm = (1 - |n|/(N + 1))_+`. -/
theorem moment_fejerMeasure (N : ℕ) (n : ℤ) :
    moment (fejerMeasure (T := T) N) n = fejerCoeff N n := by
  rw [moment, integral_fejerMeasure]
  simp_rw [fejerKernel_eq_sum_fourier, Finset.sum_mul, mul_assoc, ← fourier_add]
  rw [integral_finsetSum _ fun k _ =>
    (integrable_continuousMap haarAddCircle (fourier (k + -n))).const_mul _]
  simp_rw [integral_const_mul, integral_fourier_haarAddCircle, mul_ite, mul_one, mul_zero,
    add_neg_eq_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [fejerCoeff_of_lt, Complex.ofReal_zero]
    simp only [Finset.mem_Icc, not_and_or, not_le] at h
    omega

instance isProbabilityMeasure_fejerMeasure (N : ℕ) :
    IsProbabilityMeasure (fejerMeasure (T := T) N) := by
  constructor
  have h := moment_fejerMeasure (T := T) N 0
  rw [moment_zero_eq_mass, fejerCoeff_zero, Complex.ofReal_one] at h
  have h' : (fejerMeasure (T := T) N).real Set.univ = 1 := by exact_mod_cast h
  rwa [measureReal_def, ENNReal.toReal_eq_one_iff] at h'

/-- The Fejér coefficients tend to `1`. -/
theorem tendsto_fejerCoeff (n : ℤ) : Tendsto (fun N => fejerCoeff N n) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => 1 - |(n : ℝ)| * (1 / ((N : ℝ) + 1))) atTop
      (𝓝 (1 - |(n : ℝ)| * 0)) :=
    tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _)
  rw [mul_zero, sub_zero] at h
  refine h.congr' ((eventually_ge_atTop n.natAbs).mono fun N hN => ?_)
  dsimp only
  rw [fejerCoeff_of_natAbs_le hN, mul_one_div]

theorem tendsto_moment_fejerMeasure (n : ℤ) :
    Tendsto (fun N => moment (fejerMeasure (T := T) N) n) atTop
      (𝓝 (moment (Measure.dirac (0 : AddCircle T)) n)) := by
  simp_rw [moment_fejerMeasure, moment_dirac_zero]
  have h := (Complex.continuous_ofReal.tendsto 1).comp (tendsto_fejerCoeff n)
  rwa [Complex.ofReal_one] at h

/-- `herg:thm:fejer`: the probability measures `F_N m` converge weak-* to `δ_1`:
`∫ f F_N dm → f(1)` for every continuous `f` on the circle. -/
theorem tendsto_integral_fejerMeasure (f : C(AddCircle T, ℂ)) :
    Tendsto (fun N => ∫ x, f x ∂fejerMeasure (T := T) N) atTop (𝓝 (f 0)) := by
  have h := tendsto_integral_of_tendsto_moment tendsto_moment_fejerMeasure f
  rwa [integral_dirac] at h

/-- `F_N m` as a probability measure. -/
def fejerProbabilityMeasure (N : ℕ) : ProbabilityMeasure (AddCircle T) :=
  ⟨fejerMeasure N, inferInstance⟩

/-- The weak-* convergence `F_N m → δ_1`, in the topology of weak convergence of probability
measures. -/
theorem tendsto_fejerProbabilityMeasure :
    Tendsto (fejerProbabilityMeasure (T := T)) atTop
      (𝓝 ⟨Measure.dirac (0 : AddCircle T), inferInstance⟩) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  intro f
  have h := tendsto_integral_fejerMeasure (T := T) f.toContinuousMap
  rw [← integral_dirac (fun x => f.toContinuousMap x) (0 : AddCircle T)] at h
  exact h

end Measure

section Family

variable {T : ℝ} [Fact (0 < T)] {Γ : Type*} [LinearOrder Γ] [Zero Γ] {η : Γ}

/-- The coefficient family of `ρ_N = (1 + ε - ε F_N) m = m + t^η (m - F_N m)` of
`herg:thm:fejer`. The exponent-`0` coefficient is `m`; every other exponent carries
`m - F_N m`, but only the support `{0, η}` is used. -/
def fejerFamily (N : ℕ) (γ : Γ) : SignedMeasure (AddCircle T) :=
  if γ = 0 then (haarAddCircle (T := T)).toSignedMeasure
  else (haarAddCircle (T := T)).toSignedMeasure - (fejerMeasure (T := T) N).toSignedMeasure

/-- `herg:thm:fejer`: the leading coefficient of `ρ_N` is exactly `m`. -/
theorem fejerFamily_zero (N : ℕ) :
    fejerFamily (T := T) N (0 : Γ) = (haarAddCircle (T := T)).toSignedMeasure :=
  if_pos rfl

theorem fejerFamily_of_ne (N : ℕ) {γ : Γ} (hγ : γ ≠ 0) :
    fejerFamily (T := T) N γ =
      (haarAddCircle (T := T)).toSignedMeasure - (fejerMeasure (T := T) N).toSignedMeasure :=
  if_neg hγ

/-- `ρ_N(A) = m(A) + t^η (m(A) - (F_N m)(A))` on measurable sets. -/
theorem coefSeries_fejerFamily (hη : 0 < η) (N : ℕ) {A : Set (AddCircle T)}
    (hA : MeasurableSet A) :
    coefSeries {0, η} (isWF_pair η) (fejerFamily (T := T) N) A =
      single 0 ((haarAddCircle (T := T)).real A) +
        single η ((haarAddCircle (T := T)).real A - (fejerMeasure (T := T) N).real A) := by
  ext γ
  rw [coeff_coefSeries, coeff_add]
  by_cases h0 : γ = 0
  · subst h0
    simp [fejerFamily, hη.ne, Measure.toSignedMeasure_apply_measurable hA]
  · by_cases h1 : γ = η
    · subst h1
      simp [fejerFamily, h0, Measure.toSignedMeasure_apply_measurable hA]
    · simp [h0, h1]

/-- `herg:thm:fejer`: the exponent-`0` coefficient of `ρ_N(A)` is `m(A)`. -/
theorem coeff_zero_coefSeries_fejerFamily (hη : 0 < η) (N : ℕ) {A : Set (AddCircle T)}
    (hA : MeasurableSet A) :
    (coefSeries {0, η} (isWF_pair η) (fejerFamily (T := T) N) A).coeff 0 =
      (haarAddCircle (T := T)).real A := by
  rw [coefSeries_fejerFamily hη N hA]
  simp [hη.ne]

/-- The density of the coefficient measure of `ρ_N` at exponent `γ` with respect to `m`: `1` at
`γ = 0` and `1 - F_N` otherwise. -/
def fejerDensity (N : ℕ) (γ : Γ) (x : AddCircle T) : ℝ :=
  if γ = 0 then 1 else 1 - fejerKernel N x

omit [Fact (0 < T)] in
theorem fejerDensity_zero (N : ℕ) : fejerDensity (T := T) N (0 : Γ) = fun _ => 1 :=
  funext fun _ => if_pos rfl

omit [Fact (0 < T)] in
theorem fejerDensity_of_ne (N : ℕ) {γ : Γ} (hγ : γ ≠ 0) :
    fejerDensity (T := T) N γ = fun x => 1 - fejerKernel N x :=
  funext fun _ => if_neg hγ

/-- `herg:thm:fejer`: every coefficient measure of `ρ_N` has a density with respect to `m`:
`m` itself at exponent `0` and `m - F_N m = (1 - F_N) m` at every other exponent. -/
theorem fejerFamily_eq_withDensityᵥ (N : ℕ) (γ : Γ) :
    fejerFamily (T := T) N γ = (haarAddCircle (T := T)).withDensityᵥ (fejerDensity N γ) := by
  refine VectorMeasure.ext fun A hA => ?_
  by_cases h : γ = 0
  · subst h
    rw [fejerDensity_zero, fejerFamily_zero, withDensityᵥ_apply (integrable_const 1) hA,
      Measure.toSignedMeasure_apply_measurable hA, setIntegral_const, smul_eq_mul, mul_one]
  · rw [fejerDensity_of_ne N h, fejerFamily_of_ne N h,
      withDensityᵥ_apply (f := fun x => 1 - fejerKernel N x)
        (by exact (integrable_const 1).sub (integrable_fejerKernel N)) hA,
      Measure.toSignedMeasure_sub_apply hA, integral_sub (integrable_const 1).integrableOn
        (integrable_fejerKernel N).integrableOn, setIntegral_const, smul_eq_mul, mul_one,
      fejerMeasure_real_apply N hA]

/-- `herg:thm:fejer`: every coefficient measure of `ρ_N` is absolutely continuous with respect
to `m`. -/
theorem fejerFamily_absolutelyContinuous (N : ℕ) (γ : Γ) :
    fejerFamily (T := T) N γ ≪ᵥ (haarAddCircle (T := T)).toENNRealVectorMeasure := by
  rw [fejerFamily_eq_withDensityᵥ]
  exact Measure.withDensityᵥ_absolutelyContinuous _ _

/-- `herg:thm:fejer`: every negative part of a coefficient measure of `ρ_N` is absolutely
continuous with respect to the same first coefficient `m`. -/
theorem negPart_fejerFamily_absolutelyContinuous (N : ℕ) (γ : Γ) :
    (fejerFamily (T := T) N γ).toJordanDecomposition.negPart ≪ haarAddCircle := by
  by_cases h : γ = 0
  · rw [fejerFamily, if_pos h,
      (nonneg_iff_negPart_eq_zero _).mp (Measure.zero_le_toSignedMeasure _)]
    exact Measure.AbsolutelyContinuous.zero _
  · rw [fejerFamily_of_ne N h, Measure.toJordanDecomposition_toSignedMeasure_sub,
      Measure.jordanDecompositionOfToSignedMeasureSub_negPart]
    exact (Measure.absolutelyContinuous_of_le Measure.sub_le).trans
      (withDensity_absolutelyContinuous _ _)

/-- `herg:thm:fejer`, positivity: `ρ_N` is a positive coefficientwise Hahn measure. By the
two-scale criterion `herg:cor:twoscale`, this is `(m - F_N m)⁻ ≪ m`, and
`(m - F_N m)⁻ = F_N m - m ≤ F_N m ≪ m`. -/
theorem fejerFamily_nonneg (hη : 0 < η) (N : ℕ) (A : Set (AddCircle T))
    (hA : MeasurableSet A) :
    0 ≤ toLex (coefSeries {0, η} (isWF_pair η) (fejerFamily (T := T) N) A) := by
  have h := (twoScale_measure hη (haarAddCircle (T := T))
    ((haarAddCircle (T := T)).toSignedMeasure -
      (fejerMeasure (T := T) N).toSignedMeasure)).mpr ?_
  · rw [coefSeries_fejerFamily hη N hA]
    have := h A hA
    rwa [Measure.toSignedMeasure_sub_apply hA] at this
  · rw [← fejerFamily_of_ne N hη.ne']
    exact negPart_fejerFamily_absolutelyContinuous N η

/-- `herg:thm:fejer`: `ρ_N` is a Hahn probability, `ρ_N(X) = 1`. -/
theorem coefSeries_fejerFamily_univ (hη : 0 < η) (N : ℕ) :
    coefSeries {0, η} (isWF_pair η) (fejerFamily (T := T) N) Set.univ = 1 := by
  rw [coefSeries_fejerFamily hη N MeasurableSet.univ, probReal_univ, probReal_univ, sub_self,
    single_eq_zero, add_zero, single_zero_one]

/-- The exponent-`0` coefficient measure `m` of `ρ_N` has total variation exactly `1`. -/
theorem totalVariation_fejerFamily_zero (N : ℕ) :
    (fejerFamily (T := T) N (0 : Γ)).totalVariation Set.univ = 1 := by
  rw [fejerFamily_zero, totalVariation_toSignedMeasure, measure_univ]

/-- `herg:thm:fejer`: the exponent-`0` coefficient measure `m` of `ρ_N` has total variation at
most `1` (in fact exactly `1`, `totalVariation_fejerFamily_zero`). -/
theorem totalVariation_fejerFamily_zero_le (N : ℕ) :
    (fejerFamily (T := T) N (0 : Γ)).totalVariation Set.univ ≤ 1 :=
  (totalVariation_fejerFamily_zero N).le

/-- `herg:thm:fejer`: every coefficient measure of `ρ_N` has total variation at most `2`. -/
theorem totalVariation_fejerFamily_le (N : ℕ) (γ : Γ) :
    (fejerFamily (T := T) N γ).totalVariation Set.univ ≤ 2 := by
  by_cases h : γ = 0
  · subst h
    exact (totalVariation_fejerFamily_zero_le N).trans one_le_two
  · rw [fejerFamily_of_ne N h, SignedMeasure.totalVariation,
      Measure.toJordanDecomposition_toSignedMeasure_sub,
      Measure.jordanDecompositionOfToSignedMeasureSub_posPart,
      Measure.jordanDecompositionOfToSignedMeasureSub_negPart, Measure.add_apply]
    have e1 := Measure.le_iff'.mp
      (Measure.sub_le (μ := haarAddCircle (T := T)) (ν := fejerMeasure N)) Set.univ
    have e2 := Measure.le_iff'.mp
      (Measure.sub_le (μ := fejerMeasure (T := T) N) (ν := haarAddCircle)) Set.univ
    calc _ ≤ haarAddCircle (T := T) Set.univ + fejerMeasure (T := T) N Set.univ :=
          add_le_add e1 e2
      _ = 1 + 1 := by rw [measure_univ, measure_univ]
      _ = 2 := one_add_one_eq_two

theorem signedIntegral_fejerFamily_zero (N : ℕ) (f : C(AddCircle T, ℂ)) :
    signedIntegral (fejerFamily (T := T) N (0 : Γ)) f = ∫ x, f x ∂haarAddCircle (T := T) := by
  rw [fejerFamily_zero, signedIntegral_toSignedMeasure]

/-- The coefficient at every exponent `γ ≠ 0`, in particular `η`:
`∫ f d(m - F_N m) = ∫ f dm - ∫ f F_N dm`. -/
theorem signedIntegral_fejerFamily_of_ne (N : ℕ) {γ : Γ} (hγ : γ ≠ 0) (f : C(AddCircle T, ℂ)) :
    signedIntegral (fejerFamily (T := T) N γ) f =
      ∫ x, f x ∂haarAddCircle (T := T) - ∫ x, f x ∂fejerMeasure (T := T) N := by
  rw [fejerFamily_of_ne N hγ, signedIntegral_sub]

/-- `herg:thm:fejer`: each coefficient of `ρ_N` converges weak-* to the corresponding coefficient
of `m + t^η (m - δ_1)`: `m → m` and `m - F_N m → m - δ_1`. -/
theorem tendsto_signedIntegral_fejerFamily (γ : Γ) (f : C(AddCircle T, ℂ)) :
    Tendsto (fun N => signedIntegral (fejerFamily (T := T) N γ) f) atTop
      (𝓝 (signedIntegral (negAtomFamily (T := T) γ) f)) := by
  by_cases h : γ = 0
  · subst h
    simp only [signedIntegral_fejerFamily_zero]
    rw [negAtomFamily, if_pos rfl, signedIntegral_toSignedMeasure]
    exact tendsto_const_nhds
  · simp only [signedIntegral_fejerFamily_of_ne _ h]
    rw [negAtomFamily, if_neg h, signedIntegral_sub, integral_dirac]
    exact tendsto_const_nhds.sub (tendsto_integral_fejerMeasure f)

/-- `herg:thm:fejer`: `ρ_N` converges coefficientwise weak-* to `m + t^η (m - δ_1)` as
`N → ∞`. -/
theorem coefWeakStarTendsto_fejerFamily (η : Γ) :
    CoefWeakStarTendsto atTop {0, η} (isWF_pair η) (fejerFamily (T := T))
      (negAtomFamily (T := T)) := by
  intro f γ
  simp only [coeff_coefIntegral]
  split_ifs
  · exact tendsto_signedIntegral_fejerFamily γ f
  · exact tendsto_const_nhds

/-- The limit `m + t^η (m - δ_1)` still has leading coefficient `m`. -/
theorem negAtomFamily_zero :
    negAtomFamily (T := T) (0 : Γ) = (haarAddCircle (T := T)).toSignedMeasure :=
  if_pos rfl

/-- `herg:thm:fejer`: the exponent-`η` negative part of the limit `m + t^η (m - δ_1)` is not
absolutely continuous with respect to `m`; by `herg:cor:twoscale` this is exactly the failure
of positivity of the limit. -/
theorem negPart_negAtomFamily_not_absolutelyContinuous (hη : 0 < η) :
    ¬ (negAtomFamily (T := T) η).toJordanDecomposition.negPart ≪ haarAddCircle := by
  intro h
  refine negAtomFamily_not_positive (T := T) hη fun A hA => ?_
  have := (twoScale_measure hη (haarAddCircle (T := T)) (negAtomFamily (T := T) η)).mpr h A hA
  rw [coefSeries_negAtomFamily hη hA]
  rwa [negAtomFamily, if_neg hη.ne', Measure.toSignedMeasure_sub_apply hA] at this

/-- `herg:thm:fejer`, for `ε = t^η` with `0 < η` in any linearly ordered exponent set: for every
`N`, `ρ_N = m + t^η (m - F_N m)` is a positive coefficientwise Hahn probability measure whose
exponent-`0` coefficient is exactly `m`, whose exponent-`η` coefficient is `(1 - F_N) m`, whose
coefficient measures and their negative parts are absolutely continuous with respect to `m`, and
whose coefficient variations are at most `1` and `2`; `F_N m → δ_1` weak-*; `ρ_N` converges
coefficientwise weak-* to `m + t^η (m - δ_1)`, which has leading coefficient `m` but is not
positive, and whose exponent-`η` negative part is not absolutely continuous with respect to
`m`. -/
theorem fejer (hη : 0 < η) :
    (∀ N : ℕ,
      (∀ A, MeasurableSet A →
        0 ≤ toLex (coefSeries {0, η} (isWF_pair η) (fejerFamily (T := T) N) A)) ∧
      coefSeries {0, η} (isWF_pair η) (fejerFamily (T := T) N) Set.univ = 1 ∧
      fejerFamily (T := T) N (0 : Γ) = (haarAddCircle (T := T)).toSignedMeasure ∧
      fejerFamily (T := T) N η =
        (haarAddCircle (T := T)).withDensityᵥ (fun x => 1 - fejerKernel N x) ∧
      (∀ γ : Γ, fejerFamily (T := T) N γ ≪ᵥ (haarAddCircle (T := T)).toENNRealVectorMeasure) ∧
      (∀ γ : Γ, (fejerFamily (T := T) N γ).toJordanDecomposition.negPart ≪ haarAddCircle) ∧
      (fejerFamily (T := T) N (0 : Γ)).totalVariation Set.univ ≤ 1 ∧
      (fejerFamily (T := T) N η).totalVariation Set.univ ≤ 2) ∧
    (∀ f : C(AddCircle T, ℂ),
      Tendsto (fun N => ∫ x, f x ∂fejerMeasure (T := T) N) atTop (𝓝 (f 0))) ∧
    CoefWeakStarTendsto atTop {0, η} (isWF_pair η) (fejerFamily (T := T))
      (negAtomFamily (T := T)) ∧
    negAtomFamily (T := T) (0 : Γ) = (haarAddCircle (T := T)).toSignedMeasure ∧
    (¬ ∀ A, MeasurableSet A →
      0 ≤ toLex (coefSeries {0, η} (isWF_pair η) (negAtomFamily (T := T)) A)) ∧
    ¬ (negAtomFamily (T := T) η).toJordanDecomposition.negPart ≪ haarAddCircle :=
  ⟨fun N => ⟨fejerFamily_nonneg hη N, coefSeries_fejerFamily_univ hη N, fejerFamily_zero N,
      (fejerFamily_eq_withDensityᵥ N η).trans (by rw [fejerDensity_of_ne N hη.ne']),
      fejerFamily_absolutelyContinuous N, negPart_fejerFamily_absolutelyContinuous N,
      totalVariation_fejerFamily_zero_le N, totalVariation_fejerFamily_le N η⟩,
    tendsto_integral_fejerMeasure, coefWeakStarTendsto_fejerFamily η, negAtomFamily_zero,
    negAtomFamily_not_positive hη, negPart_negAtomFamily_not_absolutelyContinuous hη⟩

/-- `herg:thm:fejer`, nonclosedness: the positive coefficientwise Hahn-probability cone on the
circle is not closed under coefficientwise weak-* convergence, even with one fixed two-element
support `{0, η}`, with the leading coefficient exactly `m` throughout (and in the limit), with
every approximating coefficient measure absolutely continuous with respect to `m`, and with
uniformly bounded coefficient total variations. -/
theorem not_closed_positive_cone_haar (hη : 0 < η) :
    ∃ (ν : ℕ → Γ → SignedMeasure (AddCircle T)) (ν' : Γ → SignedMeasure (AddCircle T)),
      (∀ k, (∀ A, MeasurableSet A → 0 ≤ toLex (coefSeries {0, η} (isWF_pair η) (ν k) A)) ∧
        coefSeries {0, η} (isWF_pair η) (ν k) Set.univ = 1 ∧
        ν k 0 = (haarAddCircle (T := T)).toSignedMeasure ∧
        (∀ γ, ν k γ ≪ᵥ (haarAddCircle (T := T)).toENNRealVectorMeasure) ∧
        ∀ γ, (ν k γ).totalVariation Set.univ ≤ 2) ∧
      CoefWeakStarTendsto atTop {0, η} (isWF_pair η) ν ν' ∧
      ν' 0 = (haarAddCircle (T := T)).toSignedMeasure ∧
      ¬ ∀ A, MeasurableSet A → 0 ≤ toLex (coefSeries {0, η} (isWF_pair η) ν' A) :=
  ⟨fejerFamily, negAtomFamily,
    fun k => ⟨fejerFamily_nonneg hη k, coefSeries_fejerFamily_univ hη k, fejerFamily_zero k,
      fejerFamily_absolutelyContinuous k, totalVariation_fejerFamily_le k⟩,
    coefWeakStarTendsto_fejerFamily η, negAtomFamily_zero, negAtomFamily_not_positive hη⟩

end Family

section OrderedGroup

variable {T : ℝ} {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] {η : Γ}

/-- `herg:thm:fejer`: the Hahn density `1 + ε - ε F_N(ζ)` of `ρ_N`, with `ε = t^η`, is bounded
below by `1 - N ε`, because `F_N ≤ N + 1`. This is a pointwise inequality in `Lex ℝ((t^Γ))`; it
is the Hahn density of `ρ_N` through the coefficient densities `1` and `1 - F_N` of
`fejerFamily_eq_withDensityᵥ` and the ring form `coefSeries_fejerFamily_eq`, and no Hahn-valued
integral is formed. Positivity of `ρ_N` itself is `fejerFamily_nonneg`. -/
theorem one_sub_le_fejerHahnDensity (N : ℕ) (x : AddCircle T) :
    toLex (1 - (N : ℝ⟦Γ⟧) * single η 1) ≤
      toLex (1 + single η 1 - single η 1 * C (fejerKernel N x)) := by
  have e : (1 + single η 1 - single η 1 * C (fejerKernel N x)) -
      (1 - (N : ℝ⟦Γ⟧) * single η (1 : ℝ)) = single η ((N : ℝ) + 1 - fejerKernel N x) := by
    rw [← map_natCast (C : ℝ →+* ℝ⟦Γ⟧) N, C_apply, C_apply, single_mul_single,
      single_mul_single, add_zero, zero_add, one_mul, mul_one, single_sub, single_add]
    abel
  rw [← sub_nonneg]
  change 0 ≤ toLex ((1 + single η 1 - single η 1 * C (fejerKernel N x)) -
    (1 - (N : ℝ⟦Γ⟧) * single η (1 : ℝ)))
  rw [e, ← leadingCoeff_nonneg_iff, ofLex_toLex, leadingCoeff_of_single]
  linarith [fejerKernel_le N x]

/-- `herg:thm:fejer`: `1 - N t^η > 0` for every ordinary `N`, so the Hahn density of `ρ_N` is
positive. -/
theorem one_sub_natCast_mul_pos (hη : 0 < η) (N : ℕ) :
    0 < toLex (1 - (N : ℝ⟦Γ⟧) * single η 1) :=
  sub_pos.mpr (HerglotzHierarchy.natCast_mul_toLex_single_lt_one hη N)

variable [Fact (0 < T)]

/-- `herg:thm:fejer`, ring form of `ρ_N = (1 + ε - ε F_N) m`: `ρ_N(A) = (1 + ε) m(A) - ε ∫_A F_N dm`
in `ℝ((t^Γ))`, with `ε = t^η`. -/
theorem coefSeries_fejerFamily_eq (hη : 0 < η) (N : ℕ) {A : Set (AddCircle T)}
    (hA : MeasurableSet A) :
    coefSeries {0, η} (isWF_pair η) (fejerFamily (T := T) N) A =
      (1 + single η 1) * C ((haarAddCircle (T := T)).real A) -
        single η 1 * C (∫ x in A, fejerKernel N x ∂haarAddCircle (T := T)) := by
  rw [coefSeries_fejerFamily hη N hA, ← fejerMeasure_real_apply N hA, add_mul, one_mul, C_apply,
    C_apply, single_mul_single, single_mul_single, add_zero, one_mul, one_mul, single_sub,
    add_sub_assoc]

end OrderedGroup

end

end Surreal.FejerNonclosure
