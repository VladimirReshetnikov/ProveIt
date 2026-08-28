import FabiusFunction.SubgraphFubini
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Survival layer-cake identities

This module specializes the weighted subgraph Fubini theorem to the identity
height on the real line.  For a finite measure `μ` and a Banach-valued kernel
`k`, it identifies the integral of `k` against the strict survival function
`t ↦ μ.real (Ioi t)` with the expected primitive of `k`.

No support assumption is needed for the basic theorem: the stopping point is
clamped to the integration interval.  Measures supported on that interval
give the familiar partial and full survival-kernel formulas as corollaries.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace Fabius

/-- **Survival layer cake without a support hypothesis.**  For a finite
measure `μ`, an interval-integrable Banach-valued kernel `k`, and `a ≤ b`,

`∫ₐᵇ μ.real (Ioi t) • k t dt
  = ∫ z, ∫ₐ^{min (max z a) b} k t dt dμ(z)`.

Thus mass below `a` contributes the zero primitive, mass in `[a,b]` is
stopped at its location, and mass above `b` contributes the full primitive.
The use of the strict upper ray `Ioi t` agrees exactly with the strict
subgraph convention in `integral_smul_setIntegral_subgraph`. -/
theorem intervalIntegral_survival_smul_eq_integral_clamp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (hab : a ≤ b)
    (k : ℝ → E) (hk : IntervalIntegrable k volume a b) :
    (∫ t in a..b, μ.real (Ioi t) • k t) =
      ∫ z : ℝ, (∫ t in a..min (max z a) b, k t) ∂μ := by
  have hkOn : IntegrableOn k (Ioo a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hk
  have hsection (z : ℝ) :
      Iio z ∩ Ioo a b = Ioo a (min (max z a) b) := by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    constructor
    · rintro ⟨htz, hat, htb⟩
      exact ⟨hat, lt_min (lt_max_of_lt_left htz) htb⟩
    · rintro ⟨hat, htclamp⟩
      have htmax : t < max z a :=
        htclamp.trans_le (min_le_left (max z a) b)
      have htb : t < b := htclamp.trans_le (min_le_right (max z a) b)
      have htz : t < z := by
        rcases (lt_max_iff.mp htmax) with htz | hta
        · exact htz
        · exact (not_lt_of_ge hat.le hta).elim
      exact ⟨htz, hat, htb⟩
  have hclamp (z : ℝ) : a ≤ min (max z a) b :=
    le_min (le_max_right z a) hab
  have hinner (z : ℝ) :
      (∫ t in Iio z ∩ Ioo a b, k t) =
        ∫ t in a..min (max z a) b, k t := by
    rw [hsection z, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (hclamp z)]
  have hcore :
      (∫ z : ℝ, (∫ t in Iio z ∩ Ioo a b, k t ∂volume) ∂μ) =
        ∫ t in Ioo a b, μ.real (Ioi t) • k t := by
    simpa only [one_smul, Set.preimage_id', setIntegral_const,
      smul_eq_mul, mul_one] using
      (integral_smul_setIntegral_subgraph
        (μ := μ) (ν := volume)
        (Q := fun z : ℝ => z) (hQ := measurable_id)
        (w := fun _ : ℝ => (1 : ℝ)) (hw := integrable_const (1 : ℝ))
        (k := k) (s := Ioo a b) (hk := hkOn))
  calc
    (∫ t in a..b, μ.real (Ioi t) • k t) =
        ∫ t in Ioo a b, μ.real (Ioi t) • k t := by
      rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    _ = ∫ z : ℝ, (∫ t in Iio z ∩ Ioo a b, k t ∂volume) ∂μ := hcore.symm
    _ = ∫ z : ℝ, (∫ t in a..min (max z a) b, k t) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hinner)

/-- **Partial survival layer cake for an interval-supported measure.**  If
`μ` is almost surely supported on `[a,b]` and `c ∈ [a,b]`, then

`∫ₐᶜ μ.real (Ioi t) • k t dt
  = ∫ z, ∫ₐ^{min z c} k t dt dμ(z)`.

This is the stopped-primitive form of the survival-kernel identity. -/
theorem intervalIntegral_survival_smul_eq_integral_min_of_ae_mem_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b c : ℝ} (hc : c ∈ Icc a b)
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc a b)
    (k : ℝ → E) (hk : IntervalIntegrable k volume a c) :
    (∫ t in a..c, μ.real (Ioi t) • k t) =
      ∫ z : ℝ, (∫ t in a..min z c, k t) ∂μ := by
  calc
    (∫ t in a..c, μ.real (Ioi t) • k t) =
        ∫ z : ℝ, (∫ t in a..min (max z a) c, k t) ∂μ :=
      intervalIntegral_survival_smul_eq_integral_clamp μ hc.1 k hk
    _ = ∫ z : ℝ, (∫ t in a..min z c, k t) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hμ] with z hz
      rw [max_eq_left hz.1]

/-- **Full survival layer cake for an interval-supported measure.**  If
`μ` is almost surely supported on `[a,b]`, then

`∫ₐᵇ μ.real (Ioi t) • k t dt = ∫ z, ∫ₐᶻ k t dt dμ(z)`.

This is the Banach-valued expectation identity `∫ k(t) P(X > t) dt =
E[∫ₐˣ k(t) dt]`, with no positivity assumption on `k`. -/
theorem intervalIntegral_survival_smul_eq_integral_of_ae_mem_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (hab : a ≤ b)
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc a b)
    (k : ℝ → E) (hk : IntervalIntegrable k volume a b) :
    (∫ t in a..b, μ.real (Ioi t) • k t) =
      ∫ z : ℝ, (∫ t in a..z, k t) ∂μ := by
  calc
    (∫ t in a..b, μ.real (Ioi t) • k t) =
        ∫ z : ℝ, (∫ t in a..min z b, k t) ∂μ :=
      intervalIntegral_survival_smul_eq_integral_min_of_ae_mem_Icc
        μ ⟨hab, le_rfl⟩ hμ k hk
    _ = ∫ z : ℝ, (∫ t in a..z, k t) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hμ] with z hz
      rw [min_eq_left hz.2]

end Fabius
