import FabiusFunction.SubgraphFubini
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Lower-CDF layer-cake identities

This module specializes the weighted closed-supergraph Fubini theorem to the
identity height on the real line.  For a finite measure `μ` and a
Banach-valued kernel `k`, it identifies the integral of `k` against the
lower-cumulative mass `t ↦ μ.real (Iic t)` with the expected terminal
primitive of `k`.

The basic theorem needs no support assumption: the starting point is clamped
to the integration interval.  Measures supported on that interval give the
familiar partial and full lower-CDF formulas as corollaries.  All inequalities
in the measure fibers are non-strict, so atoms are preserved exactly.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace Fabius

/-- **Lower-CDF layer cake without a support hypothesis.**  For a finite
measure `μ`, an interval-integrable Banach-valued kernel `k`, and `a ≤ b`,

`∫ₐᵇ μ.real (Iic t) • k t dt
  = ∫ z, ∫_{min (max z a) b}ᵇ k t dt dμ(z)`.

Thus mass below `a` contributes the full terminal primitive, mass in `[a,b]`
starts at its location, and mass above `b` contributes zero.  The use of the
closed lower ray `Iic t` agrees exactly with the closed-supergraph convention
in `integral_smul_setIntegral_supergraph`. -/
theorem intervalIntegral_cdf_smul_eq_integral_clamp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (hab : a ≤ b)
    (k : ℝ → E) (hk : IntervalIntegrable k volume a b) :
    (∫ t in a..b, μ.real (Iic t) • k t) =
      ∫ z : ℝ, (∫ t in min (max z a) b..b, k t) ∂μ := by
  have hkOn : IntegrableOn k (Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hk
  have hsection (z : ℝ) :
      Ici z ∩ Icc a b = Icc (max z a) b := by
    ext t
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨hzt, hat, htb⟩
      exact ⟨max_le hzt hat, htb⟩
    · rintro ⟨hmax, htb⟩
      exact ⟨(le_max_left z a).trans hmax,
        (le_max_right z a).trans hmax, htb⟩
  have hinner (z : ℝ) :
      (∫ t in Ici z ∩ Icc a b, k t) =
        ∫ t in min (max z a) b..b, k t := by
    by_cases hzb : max z a ≤ b
    · rw [hsection z, min_eq_left hzb, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hzb]
    · have hbz : b < max z a := lt_of_not_ge hzb
      rw [hsection z, Icc_eq_empty hzb, setIntegral_empty,
        min_eq_right hbz.le]
      simp
  have hcore :
      (∫ z : ℝ, (∫ t in Ici z ∩ Icc a b, k t ∂volume) ∂μ) =
        ∫ t in Icc a b, μ.real (Iic t) • k t := by
    simpa only [one_smul, Set.preimage_id', setIntegral_const,
      smul_eq_mul, mul_one] using
      (integral_smul_setIntegral_supergraph
        (μ := μ) (ν := volume)
        (Q := fun z : ℝ => z) (hQ := measurable_id)
        (w := fun _ : ℝ => (1 : ℝ)) (hw := integrable_const (1 : ℝ))
        (k := k) (s := Icc a b) (hk := hkOn))
  calc
    (∫ t in a..b, μ.real (Iic t) • k t) =
        ∫ t in Icc a b, μ.real (Iic t) • k t := by
      rw [intervalIntegral.integral_of_le hab,
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ z : ℝ, (∫ t in Ici z ∩ Icc a b, k t ∂volume) ∂μ :=
      hcore.symm
    _ = ∫ z : ℝ, (∫ t in min (max z a) b..b, k t) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hinner)

/-- **Partial lower-CDF layer cake under a one-sided support bound.**  If
`μ` is almost surely supported to the left of `b` and `c ≤ b`, then

`∫ᶜᵇ μ.real (Iic t) • k t dt
  = ∫ z, ∫_{max z c}ᵇ k t dt dμ(z)`.

No lower support bound is needed.  This is the terminal-primitive form of
the lower-CDF identity. -/
theorem intervalIntegral_cdf_smul_eq_integral_max_of_ae_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {b c : ℝ} (hcb : c ≤ b) (hμ : ∀ᵐ z ∂μ, z ≤ b)
    (k : ℝ → E) (hk : IntervalIntegrable k volume c b) :
    (∫ t in c..b, μ.real (Iic t) • k t) =
      ∫ z : ℝ, (∫ t in max z c..b, k t) ∂μ := by
  calc
    (∫ t in c..b, μ.real (Iic t) • k t) =
        ∫ z : ℝ, (∫ t in min (max z c) b..b, k t) ∂μ :=
      intervalIntegral_cdf_smul_eq_integral_clamp μ hcb k hk
    _ = ∫ z : ℝ, (∫ t in max z c..b, k t) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hμ] with z hz
      rw [min_eq_left (max_le hz hcb)]

/-- **Partial lower-CDF layer cake for an interval-supported measure.**  If
`μ` is almost surely supported on `[a,b]` and `c ∈ [a,b]`, then

`∫ᶜᵇ μ.real (Iic t) • k t dt
  = ∫ z, ∫_{max z c}ᵇ k t dt dμ(z)`. -/
theorem intervalIntegral_cdf_smul_eq_integral_max_of_ae_mem_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b c : ℝ} (hc : c ∈ Icc a b)
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc a b)
    (k : ℝ → E) (hk : IntervalIntegrable k volume c b) :
    (∫ t in c..b, μ.real (Iic t) • k t) =
      ∫ z : ℝ, (∫ t in max z c..b, k t) ∂μ :=
  intervalIntegral_cdf_smul_eq_integral_max_of_ae_le
    μ hc.2 (hμ.mono fun _ hz => hz.2) k hk

/-- **Full lower-CDF layer cake for an interval-supported measure.**  If
`μ` is almost surely supported on `[a,b]`, then

`∫ₐᵇ μ.real (Iic t) • k t dt = ∫ z, ∫_zᵇ k t dt dμ(z)`.

This is the Banach-valued expectation identity
`∫ k(t) P(X ≤ t) dt = E[∫ₓᵇ k(t) dt]`.  The non-strict event retains
atoms, and no positivity assumption on `k` is needed. -/
theorem intervalIntegral_cdf_smul_eq_integral_of_ae_mem_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (hab : a ≤ b)
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc a b)
    (k : ℝ → E) (hk : IntervalIntegrable k volume a b) :
    (∫ t in a..b, μ.real (Iic t) • k t) =
      ∫ z : ℝ, (∫ t in z..b, k t) ∂μ := by
  calc
    (∫ t in a..b, μ.real (Iic t) • k t) =
        ∫ z : ℝ, (∫ t in max z a..b, k t) ∂μ :=
      intervalIntegral_cdf_smul_eq_integral_max_of_ae_mem_Icc
        μ ⟨le_rfl, hab⟩ hμ k hk
    _ = ∫ z : ℝ, (∫ t in z..b, k t) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hμ] with z hz
      rw [max_eq_left hz.1]

end Fabius
