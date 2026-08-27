import FabiusFunction.MartingaleOrthogonality

/-!
# Covariance halving of the doubling cocycle: `c₁ = c₀/2`

The counterpart of `MartingaleOrthogonality` for the cocycle
`ψ(t) = log (2 sin πt)` itself: `ψ` is a `𝒫`-eigenfunction with
eigenvalue `1/2` (`DoublingCocycleIdentities.log_two_sin_half_add`),
so pairing it with its own doubling pullback *halves* instead of
annihilating:

`∫₀^½ ψ(t)·ψ(2t) dt + ∫_½^1 ψ(t)·ψ(2t−1) dt = ½·∫₀¹ ψ²`,

i.e. `c₁ = c₀/2` in branchwise form.  Iterating the same identity
gives the audit's exact geometric covariance decay `c_r = c₀/2^r`,
which feeds the closed variance form of `VarianceBookkeeping`.

* `measurable_log_two_sin_pi_mul`, `intervalIntegrable_sq_log_two_sin_pi_mul`
  — `ψ` is measurable and in `L²`.
* `intervalIntegrable_sq_log_two_sin_half`, `…_shift` — branch squares.
* `intervalIntegrable_branch_product_cocycle_left`, `…_right` — branch
  products.
* `integral_mul_comp_doubling_of_halving_ae` — the abstract a.e.
  halving lemma.
* `integral_log_two_sin_mul_comp_doubling` — **`c₁ = c₀/2`**.
-/

set_option autoImplicit false

open intervalIntegral Real MeasureTheory

namespace Fabius

/-- The doubling cocycle `ψ = log (2 sin π·)` is measurable. -/
theorem measurable_log_two_sin_pi_mul :
    Measurable fun t : ℝ => Real.log (2 * Real.sin (π * t)) :=
  Real.measurable_log.comp
    ((Real.measurable_sin.comp (measurable_const_mul π)).const_mul 2)

/-- The doubling cocycle is square-integrable on `[0,1]`. -/
theorem intervalIntegrable_sq_log_two_sin_pi_mul :
    IntervalIntegrable (fun t => Real.log (2 * Real.sin (π * t)) ^ 2)
      MeasureTheory.volume 0 1 := by
  have hdom : IntervalIntegrable
      (fun t : ℝ => 2 * Real.log 2 ^ 2 +
        2 * Real.log (Real.sin (π * t)) ^ 2)
      MeasureTheory.volume 0 1 :=
    intervalIntegrable_const.add
      (intervalIntegrable_sq_log_sin_pi_mul.const_mul 2)
  apply hdom.mono_fun
  · exact (measurable_log_two_sin_pi_mul.pow_const 2).aestronglyMeasurable
  · have h1ae : ∀ᵐ t : ℝ, t ≠ (1:ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [MeasureTheory.ae_restrict_of_ae h1ae,
      MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht1 hmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hmem
    have hs : 0 < Real.sin (π * t) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · have := hmem.1
        positivity
      · nlinarith [Real.pi_pos, hmem.1,
          lt_of_le_of_ne hmem.2 ht1]
    have hsplit : Real.log (2 * Real.sin (π * t)) =
        Real.log 2 + Real.log (Real.sin (π * t)) :=
      Real.log_mul two_ne_zero (ne_of_gt hs)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.log 2 ^ 2 +
        2 * Real.log (Real.sin (π * t)) ^ 2), hsplit]
    nlinarith [sq_nonneg (Real.log 2 - Real.log (Real.sin (π * t)))]

/-- The left branch square `u ↦ ψ(u/2)²` is integrable on `[0,1]`. -/
theorem intervalIntegrable_sq_log_two_sin_half :
    IntervalIntegrable
      (fun u => Real.log (2 * Real.sin (π * (u / 2))) ^ 2)
      MeasureTheory.volume 0 1 := by
  have hbase : IntervalIntegrable
      (fun t => Real.log (2 * Real.sin (π * t)) ^ 2)
      MeasureTheory.volume 0 (1 / 2) := by
    refine intervalIntegrable_sq_log_two_sin_pi_mul.mono_set ?_
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1 / 2),
      Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc le_rfl (by norm_num)
  have h : IntervalIntegrable
      (fun u => Real.log (2 * Real.sin (π * (u * (1 / 2)))) ^ 2)
      MeasureTheory.volume (0 / (1 / 2)) ((1 / 2) / (1 / 2)) :=
    hbase.comp_mul_right
  have heq : (fun u => Real.log (2 * Real.sin (π * (u * (1 / 2)))) ^ 2) =
      fun u => Real.log (2 * Real.sin (π * (u / 2))) ^ 2 := by
    funext u
    rw [show π * (u * (1 / 2)) = π * (u / 2) by ring]
  rw [heq] at h
  convert h using 2 <;> norm_num

/-- The right branch square `u ↦ ψ((u+1)/2)²` is integrable on
`[0,1]`. -/
theorem intervalIntegrable_sq_log_two_sin_shift :
    IntervalIntegrable
      (fun u => Real.log (2 * Real.sin (π * ((u + 1) / 2))) ^ 2)
      MeasureTheory.volume 0 1 := by
  have hbase : IntervalIntegrable
      (fun t => Real.log (2 * Real.sin (π * t)) ^ 2)
      MeasureTheory.volume (1 / 2) 1 := by
    refine intervalIntegrable_sq_log_two_sin_pi_mul.mono_set ?_
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) / 2 ≤ 1),
      Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc (by norm_num) le_rfl
  have h1 : IntervalIntegrable
      (fun u => Real.log (2 * Real.sin (π * (u * (1 / 2)))) ^ 2)
      MeasureTheory.volume ((1 / 2) / (1 / 2)) (1 / (1 / 2)) :=
    hbase.comp_mul_right
  have heq1 : (fun u => Real.log (2 * Real.sin (π * (u * (1 / 2)))) ^ 2) =
      fun u => Real.log (2 * Real.sin (π * (u / 2))) ^ 2 := by
    funext u
    rw [show π * (u * (1 / 2)) = π * (u / 2) by ring]
  rw [heq1] at h1
  have h2 : IntervalIntegrable
      (fun u => Real.log (2 * Real.sin (π * ((u + 1) / 2))) ^ 2)
      MeasureTheory.volume ((1 / 2) / (1 / 2) - 1) (1 / (1 / 2) - 1) :=
    h1.comp_add_right 1
  convert h2 using 2 <;> norm_num

/-- The left branch product `u ↦ ψ(u/2)·ψ(u)` is integrable. -/
theorem intervalIntegrable_branch_product_cocycle_left :
    IntervalIntegrable
      (fun u => Real.log (2 * Real.sin (π * (u / 2))) *
        Real.log (2 * Real.sin (π * u))) MeasureTheory.volume 0 1 := by
  have hdom : IntervalIntegrable
      (fun u => (1 / 2 : ℝ) *
        (Real.log (2 * Real.sin (π * (u / 2))) ^ 2 +
          Real.log (2 * Real.sin (π * u)) ^ 2))
      MeasureTheory.volume 0 1 :=
    (intervalIntegrable_sq_log_two_sin_half.add
      intervalIntegrable_sq_log_two_sin_pi_mul).const_mul (1 / 2)
  apply hdom.mono_fun
  · exact ((measurable_log_two_sin_pi_mul.comp
      (measurable_id.div_const 2)).mul
      measurable_log_two_sin_pi_mul).aestronglyMeasurable
  · filter_upwards with u
    set A := Real.log (2 * Real.sin (π * (u / 2)))
    set B := Real.log (2 * Real.sin (π * u))
    simp only [Real.norm_eq_abs]
    rw [abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / 2 * (A ^ 2 + B ^ 2))]
    nlinarith [sq_nonneg (|A| - |B|), sq_abs A, sq_abs B,
      abs_nonneg A, abs_nonneg B]

/-- The right branch product `u ↦ ψ((u+1)/2)·ψ(u)` is integrable. -/
theorem intervalIntegrable_branch_product_cocycle_right :
    IntervalIntegrable
      (fun u => Real.log (2 * Real.sin (π * ((u + 1) / 2))) *
        Real.log (2 * Real.sin (π * u))) MeasureTheory.volume 0 1 := by
  have hdom : IntervalIntegrable
      (fun u => (1 / 2 : ℝ) *
        (Real.log (2 * Real.sin (π * ((u + 1) / 2))) ^ 2 +
          Real.log (2 * Real.sin (π * u)) ^ 2))
      MeasureTheory.volume 0 1 :=
    (intervalIntegrable_sq_log_two_sin_shift.add
      intervalIntegrable_sq_log_two_sin_pi_mul).const_mul (1 / 2)
  apply hdom.mono_fun
  · exact ((measurable_log_two_sin_pi_mul.comp
      ((measurable_id.add_const 1).div_const 2)).mul
      measurable_log_two_sin_pi_mul).aestronglyMeasurable
  · filter_upwards with u
    set A := Real.log (2 * Real.sin (π * ((u + 1) / 2)))
    set B := Real.log (2 * Real.sin (π * u))
    simp only [Real.norm_eq_abs]
    rw [abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / 2 * (A ^ 2 + B ^ 2))]
    nlinarith [sq_nonneg (|A| - |B|), sq_abs A, sq_abs B,
      abs_nonneg A, abs_nonneg B]

/-- **Abstract a.e. halving**: if the Perron average of `f` returns
`f` a.e. on the fundamental interval (`𝒫f = f/2` in operator form),
the pairing of `f` with any pullback `g ∘ T` is half the plain
pairing. -/
theorem integral_mul_comp_doubling_of_halving_ae (f g : ℝ → ℝ)
    (hint1 : IntervalIntegrable (fun u => f (u / 2) * g u)
      MeasureTheory.volume 0 1)
    (hint2 : IntervalIntegrable (fun u => f ((u + 1) / 2) * g u)
      MeasureTheory.volume 0 1)
    (hhalf : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIoc (0:ℝ) 1 → f (t / 2) + f ((t + 1) / 2) = f t) :
    ((∫ t in (0:ℝ)..(1/2:ℝ), f t * g (2 * t)) +
      ∫ t in (1/2:ℝ)..1, f t * g (2 * t - 1)) =
    (1 / 2) * ∫ t in (0:ℝ)..1, f t * g t := by
  rw [integral_mul_comp_doubling' f g hint1 hint2]
  have hcongr : ∫ t in (0:ℝ)..1,
      (f (t / 2) + f ((t + 1) / 2)) / 2 * g t =
      ∫ t in (0:ℝ)..1, (1 / 2 : ℝ) * (f t * g t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hhalf] with t ht hmem
    rw [ht hmem]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul]

/-- **Covariance halving of the doubling cocycle, `c₁ = c₀/2`**:

`∫₀^½ ψ(t)·ψ(2t) dt + ∫_½^1 ψ(t)·ψ(2t−1) dt = ½·∫₀¹ ψ(t)² dt`

for `ψ = log (2 sin π·)` — pairing the cocycle with its own doubling
pullback halves its `L²` mass, the first step of the audit's exact
geometric covariance decay `c_r = c₀/2^r`. -/
theorem integral_log_two_sin_mul_comp_doubling :
    ((∫ t in (0:ℝ)..(1/2:ℝ), Real.log (2 * Real.sin (π * t)) *
        Real.log (2 * Real.sin (π * (2 * t)))) +
      ∫ t in (1/2:ℝ)..1, Real.log (2 * Real.sin (π * t)) *
        Real.log (2 * Real.sin (π * (2 * t - 1)))) =
    (1 / 2) * ∫ t in (0:ℝ)..1, Real.log (2 * Real.sin (π * t)) ^ 2 := by
  have h := integral_mul_comp_doubling_of_halving_ae
    (fun t => Real.log (2 * Real.sin (π * t)))
    (fun t => Real.log (2 * Real.sin (π * t)))
    intervalIntegrable_branch_product_cocycle_left
    intervalIntegrable_branch_product_cocycle_right ?_
  · rw [h]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    show Real.log (2 * Real.sin (π * t)) * Real.log (2 * Real.sin (π * t)) =
      Real.log (2 * Real.sin (π * t)) ^ 2
    ring
  · have h1ae : ∀ᵐ t : ℝ, t ≠ (1:ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [h1ae] with t ht1 hmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hmem
    have hs : Real.sin (π * t) ≠ 0 := by
      have h : 0 < Real.sin (π * t) := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · have := hmem.1
          positivity
        · nlinarith [Real.pi_pos, hmem.1, lt_of_le_of_ne hmem.2 ht1]
      exact ne_of_gt h
    have hkey := log_two_sin_half_add t hs
    show Real.log (2 * Real.sin (π * (t / 2))) +
      Real.log (2 * Real.sin (π * ((t + 1) / 2))) =
      Real.log (2 * Real.sin (π * t))
    rw [show π * (t / 2) = π * t / 2 by ring,
      show π * ((t + 1) / 2) = π * (t + 1) / 2 by ring]
    exact hkey

end Fabius
