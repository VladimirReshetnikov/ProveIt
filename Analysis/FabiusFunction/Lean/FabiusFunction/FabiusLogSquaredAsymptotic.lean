import FabiusFunction.FabiusLogScale
import FabiusFunction.FabiusDyadicLogBounds

/-!
# Quadratic logarithmic asymptotic of the Fabius function

This module promotes the natural-index estimate from `FabiusDyadicLogBounds` to the
full real logarithmic scale.  The proof uses monotonicity of
`fabiusLogProfile F t = -log (F (2⁻ᵗ))` and squeezes a real `t` between its natural floor
and the next integer.

No periodic-remainder ansatz is used.  The resulting rigorous leading asymptotic is

`fabiusLogProfile F t / t ^ 2 → log 2 / 2`

as `t → ∞`.
-/

set_option autoImplicit false

open Filter Asymptotics
open scoped Topology

namespace Fabius

/-- The negative-log profile increases with the logarithmic scale. -/
theorem fabiusLogProfile_monotone (F : BoundedFabius) (hF : IsFabius F) :
    Monotone (fabiusLogProfile F) := by
  intro s t hst
  have harg : fabiusLogArgument t ≤ fabiusLogArgument s := by
    unfold fabiusLogArgument
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
  have hphi := fabius_monotone F hF harg
  change fabiusLogPhi F t ≤ fabiusLogPhi F s at hphi
  have hlog := Real.log_le_log (fabiusLogPhi_pos F hF t) hphi
  unfold fabiusLogProfile
  exact neg_le_neg hlog

/-- At a natural scale, the real-power argument agrees with the inverse natural power. -/
lemma fabiusLogArgument_natCast (n : ℕ) :
    fabiusLogArgument (n : ℝ) = ((2 : ℝ) ^ n)⁻¹ := by
  unfold fabiusLogArgument
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

lemma fabiusLogProfile_natCast (F : BoundedFabius) (n : ℕ) :
    fabiusLogProfile F (n : ℝ) =
      -Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) := by
  simp [fabiusLogProfile, fabiusLogPhi, fabiusLogArgument_natCast]

private theorem monotone_normalized_nat_to_real
    (g : ℝ → ℝ) (c : ℝ) (hmono : Monotone g) (hnonneg : ∀ t, 0 ≤ g t)
    (hseq : Tendsto (fun n : ℕ => g (n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 c)) :
    Tendsto (fun t : ℝ => g t / t ^ 2) atTop (𝓝 c) := by
  have hfloorNat : Tendsto (fun t : ℝ => ⌊t⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop
  have hsuccNat : Tendsto (fun t : ℝ => ⌊t⌋₊ + 1) atTop atTop :=
    (Filter.tendsto_add_atTop_nat 1).comp hfloorNat
  have hfloorCast : Tendsto (fun t : ℝ => (⌊t⌋₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hfloorNat
  have hsuccCast : Tendsto (fun t : ℝ => ((⌊t⌋₊ + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsuccNat
  have hfloorRatio :
      Tendsto (fun t : ℝ => (⌊t⌋₊ : ℝ) / ((⌊t⌋₊ + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    have hraw :
        Tendsto (fun t : ℝ => (1 : ℝ) - 1 / ((⌊t⌋₊ + 1 : ℕ) : ℝ))
          atTop (𝓝 ((1 : ℝ) - 0)) :=
      tendsto_const_nhds.sub (hsuccCast.const_div_atTop (1 : ℝ))
    have hraw' : Tendsto (fun t : ℝ => (1 : ℝ) - 1 / ((⌊t⌋₊ + 1 : ℕ) : ℝ))
        atTop (𝓝 1) := by simpa using hraw
    apply hraw'.congr'
    filter_upwards with t
    have hpos : (0 : ℝ) < ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by positivity
    field_simp
    push_cast
    ring
  have hsuccRatio :
      Tendsto (fun t : ℝ => ((⌊t⌋₊ + 1 : ℕ) : ℝ) / (⌊t⌋₊ : ℝ)) atTop (𝓝 1) := by
    have hraw : Tendsto (fun t : ℝ => (1 : ℝ) + 1 / (⌊t⌋₊ : ℝ))
        atTop (𝓝 ((1 : ℝ) + 0)) :=
      tendsto_const_nhds.add (hfloorCast.const_div_atTop (1 : ℝ))
    have hraw' : Tendsto (fun t : ℝ => (1 : ℝ) + 1 / (⌊t⌋₊ : ℝ))
        atTop (𝓝 1) := by simpa using hraw
    apply hraw'.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have hnpos : 0 < ⌊t⌋₊ := Nat.floor_pos.mpr ht.le
    have hn0 : (⌊t⌋₊ : ℝ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  have hlower :
      Tendsto
        (fun t : ℝ => g (⌊t⌋₊ : ℝ) / ((⌊t⌋₊ + 1 : ℕ) : ℝ) ^ 2)
        atTop (𝓝 c) := by
    have hraw := (hseq.comp hfloorNat).mul (hfloorRatio.pow 2)
    have hraw' : Tendsto
        (fun t : ℝ =>
          ((fun n : ℕ => g (n : ℝ) / (n : ℝ) ^ 2) ∘ fun t : ℝ => ⌊t⌋₊) t *
            ((⌊t⌋₊ : ℝ) / ((⌊t⌋₊ + 1 : ℕ) : ℝ)) ^ 2)
        atTop (𝓝 c) := by simpa using hraw
    apply hraw'.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have hnpos : 0 < ⌊t⌋₊ := Nat.floor_pos.mpr ht.le
    have hn0 : (⌊t⌋₊ : ℝ) ≠ 0 := by positivity
    simp only [Function.comp_apply]
    field_simp
  have hupper :
      Tendsto
        (fun t : ℝ => g ((⌊t⌋₊ + 1 : ℕ) : ℝ) / (⌊t⌋₊ : ℝ) ^ 2)
        atTop (𝓝 c) := by
    have hraw := (hseq.comp hsuccNat).mul (hsuccRatio.pow 2)
    have hraw' : Tendsto
        (fun t : ℝ =>
          ((fun n : ℕ => g (n : ℝ) / (n : ℝ) ^ 2) ∘
              fun t : ℝ => ⌊t⌋₊ + 1) t *
            (((⌊t⌋₊ + 1 : ℕ) : ℝ) / (⌊t⌋₊ : ℝ)) ^ 2)
        atTop (𝓝 c) := by simpa using hraw
    apply hraw'.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have hnpos : 0 < ⌊t⌋₊ := Nat.floor_pos.mpr ht.le
    have hn0 : (⌊t⌋₊ : ℝ) ≠ 0 := by positivity
    simp only [Function.comp_apply]
    field_simp
  apply hlower.squeeze' hupper
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : 0 ≤ t := (zero_lt_one.trans ht).le
    have htpos : 0 < t := zero_lt_one.trans ht
    have hnle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
    have htlt : t < ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by
      simpa using Nat.lt_floor_add_one t
    have hmonoLower := hmono hnle
    calc
      g (⌊t⌋₊ : ℝ) / ((⌊t⌋₊ + 1 : ℕ) : ℝ) ^ 2 ≤
          g (⌊t⌋₊ : ℝ) / t ^ 2 :=
        div_le_div_of_nonneg_left (hnonneg _) (sq_pos_of_pos htpos) (by nlinarith)
      _ ≤ g t / t ^ 2 := div_le_div_of_nonneg_right hmonoLower (sq_nonneg t)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : 0 ≤ t := (zero_lt_one.trans ht).le
    have hnle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
    have htlt : t < ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by
      simpa using Nat.lt_floor_add_one t
    have hnpos : 0 < ⌊t⌋₊ := Nat.floor_pos.mpr ht.le
    have hncastpos : (0 : ℝ) < (⌊t⌋₊ : ℝ) := by positivity
    have hmonoUpper := hmono htlt.le
    calc
      g t / t ^ 2 ≤ g ((⌊t⌋₊ + 1 : ℕ) : ℝ) / t ^ 2 :=
        div_le_div_of_nonneg_right hmonoUpper (sq_nonneg t)
      _ ≤ g ((⌊t⌋₊ + 1 : ℕ) : ℝ) / (⌊t⌋₊ : ℝ) ^ 2 :=
        div_le_div_of_nonneg_left (hnonneg _) (sq_pos_of_pos hncastpos) (by nlinarith)

/-- The full real logarithmic profile has quadratic leading coefficient `log 2 / 2`. -/
theorem fabiusLogProfile_normalized_tendsto
    (F : BoundedFabius) (hF : IsFabius F) :
    Tendsto (fun t : ℝ => fabiusLogProfile F t / t ^ 2) atTop
      (𝓝 (Real.log 2 / 2)) := by
  have hseq :
      Tendsto (fun n : ℕ => fabiusLogProfile F (n : ℝ) / (n : ℝ) ^ 2)
        atTop (𝓝 (Real.log 2 / 2)) := by
    have h := (normalized_log_fabius_inverse_two_pow_tendsto F hF).neg
    convert h using 1
    · funext n
      rw [fabiusLogProfile_natCast]
      ring
    · ring_nf
  apply monotone_normalized_nat_to_real (fabiusLogProfile F)
    (Real.log 2 / 2) (fabiusLogProfile_monotone F hF) ?_ hseq
  intro t
  unfold fabiusLogProfile fabiusLogPhi
  exact neg_nonneg.mpr (Real.log_nonpos (fabiusReal_nonneg F _)
    (fabiusReal_le_one F _))

end Fabius
