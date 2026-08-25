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

/-- At a natural scale `n`, the negative-log profile of `F` is
`-log (F ((2 ^ n)⁻¹))`, the inverse natural power replacing the real power
`2 ^ (-n)`.  No `IsFabius` hypothesis is needed.  Used in this file by
`fabiusLogProfile_normalized_tendsto` and
`fabiusLogProfile_natCast_error_le`. -/
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

/-- The dyadic logarithmic error bound, stated for the negative-log profile. -/
lemma fabiusLogProfile_natCast_error_le
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (hn : 1 ≤ n) :
    |fabiusLogProfile F (n : ℝ) - Real.log 2 / 2 * (n : ℝ) ^ 2| ≤
      3 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) := by
  have h := abs_dyadicLogError_le F hF n hn
  rw [fabiusLogProfile_natCast]
  convert h using 1
  rw [← abs_neg]
  congr 1
  ring

/-- A concrete full-real-scale version of the coarse error estimate. -/
theorem eventually_abs_fabiusLogProfile_sub_quadratic_le
    (F : BoundedFabius) (hF : IsFabius F) :
    ∀ᶠ t : ℝ in atTop,
      |fabiusLogProfile F t - Real.log 2 / 2 * t ^ 2| ≤
        16 * (t * Real.log t) := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
  let n : ℕ := ⌊t⌋₊
  have ht0 : 0 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hlogtwo_le : Real.log 2 ≤ Real.log t :=
    Real.log_le_log (by norm_num) ht
  have hnle : (n : ℝ) ≤ t := by
    dsimp [n]
    exact Nat.floor_le ht0
  have htlt : t < ((n + 1 : ℕ) : ℝ) := by
    dsimp [n]
    simpa using Nat.lt_floor_add_one t
  have hn_one : 1 ≤ n := by
    apply Nat.le_floor
    norm_num
    linarith
  have hnsucc_one : 1 ≤ n + 1 := by omega
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hnsucc0 : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hn1pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hn2pos : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
  have hmono := fabiusLogProfile_monotone F hF
  have hprofLower : fabiusLogProfile F (n : ℝ) ≤ fabiusLogProfile F t :=
    hmono hnle
  have hprofUpper : fabiusLogProfile F t ≤ fabiusLogProfile F (n + 1 : ℕ) :=
    hmono htlt.le
  have hnerr := fabiusLogProfile_natCast_error_le F hF n hn_one
  have hnsuccerr := fabiusLogProfile_natCast_error_le F hF (n + 1) hnsucc_one
  have hnerrBounds := (abs_le.mp hnerr)
  have hnsuccerrBounds := (abs_le.mp hnsuccerr)
  have herrorLower :
      -(3 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) -
          Real.log 2 / 2 * (t ^ 2 - (n : ℝ) ^ 2) ≤
        fabiusLogProfile F t - Real.log 2 / 2 * t ^ 2 := by
    calc
      -(3 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) -
          Real.log 2 / 2 * (t ^ 2 - (n : ℝ) ^ 2) ≤
          (fabiusLogProfile F (n : ℝ) - Real.log 2 / 2 * (n : ℝ) ^ 2) -
            Real.log 2 / 2 * (t ^ 2 - (n : ℝ) ^ 2) :=
        sub_le_sub_right hnerrBounds.1 _
      _ = fabiusLogProfile F (n : ℝ) - Real.log 2 / 2 * t ^ 2 := by ring
      _ ≤ fabiusLogProfile F t - Real.log 2 / 2 * t ^ 2 :=
        sub_le_sub_right hprofLower _
  have herrorUpper :
      fabiusLogProfile F t - Real.log 2 / 2 * t ^ 2 ≤
        3 * ((n + 1 : ℕ) : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) +
          Real.log 2 / 2 * (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) := by
    calc
      fabiusLogProfile F t - Real.log 2 / 2 * t ^ 2 ≤
          fabiusLogProfile F (n + 1 : ℕ) - Real.log 2 / 2 * t ^ 2 :=
        sub_le_sub_right hprofUpper _
      _ = (fabiusLogProfile F (n + 1 : ℕ) -
            Real.log 2 / 2 * ((n + 1 : ℕ) : ℝ) ^ 2) +
          Real.log 2 / 2 * (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) := by ring
      _ ≤ 3 * ((n + 1 : ℕ) : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) +
          Real.log 2 / 2 * (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) :=
        by
          simpa [Nat.add_assoc] using add_le_add_right hnsuccerrBounds.2
            (Real.log 2 / 2 * (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2))
  have hcastSucc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hcastSuccSucc : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  have hn1_le_tsq : ((n + 1 : ℕ) : ℝ) ≤ t ^ 2 := by
    have hn1_le : ((n + 1 : ℕ) : ℝ) ≤ t + 1 := by
      rw [hcastSucc]
      linarith
    have ht1_le : t + 1 ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
    exact hn1_le.trans ht1_le
  have hn2_le_tsq : ((n + 2 : ℕ) : ℝ) ≤ t ^ 2 := by
    have hn2_le : ((n + 2 : ℕ) : ℝ) ≤ t + 2 := by
      rw [hcastSuccSucc]
      linarith
    have ht2_le : t + 2 ≤ t ^ 2 := by
      have hprod : 0 ≤ (t - 2) * (t + 1) :=
        mul_nonneg (sub_nonneg.mpr ht) (by linarith)
      nlinarith
    exact hn2_le.trans ht2_le
  have hlogn1 : Real.log ((n + 1 : ℕ) : ℝ) ≤ 2 * Real.log t := by
    calc
      Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (t ^ 2) :=
        Real.log_le_log hn1pos hn1_le_tsq
      _ = 2 * Real.log t := by rw [Real.log_pow]; norm_num
  have hlogn2 : Real.log ((n + 2 : ℕ) : ℝ) ≤ 2 * Real.log t := by
    calc
      Real.log ((n + 2 : ℕ) : ℝ) ≤ Real.log (t ^ 2) :=
        Real.log_le_log hn2pos hn2_le_tsq
      _ = 2 * Real.log t := by rw [Real.log_pow]; norm_num
  have hlogn1nonneg : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hnsucc_one)
  have hlogn2nonneg : 0 ≤ Real.log ((n + 2 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 2 by omega))
  have hnTerm :
      3 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) ≤
        6 * (t * Real.log t) := by
    have hmul := mul_le_mul hnle hlogn1 hlogn1nonneg ht0
    nlinarith
  have hnsucc_le : ((n + 1 : ℕ) : ℝ) ≤ 2 * t := by
    rw [hcastSucc]
    linarith
  have hnsuccTerm :
      3 * ((n + 1 : ℕ) : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) ≤
        12 * (t * Real.log t) := by
    have hmul := mul_le_mul hnsucc_le hlogn2 hlogn2nonneg (by positivity)
    nlinarith
  have hnsq_le_tsq : (n : ℝ) ^ 2 ≤ t ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hn0 hnle
  have htsq_le_succsq : t ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    exact (sq_le_sq₀ ht0 hn1pos.le).mpr htlt.le
  have hlowerGap : t ^ 2 - (n : ℝ) ^ 2 ≤ 3 * t := by
    calc
      t ^ 2 - (n : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 - (n : ℝ) ^ 2 :=
        sub_le_sub_right htsq_le_succsq _
      _ = 2 * (n : ℝ) + 1 := by rw [hcastSucc]; ring
      _ ≤ 3 * t := by linarith
  have hupperGap : ((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2 ≤ 3 * t := by
    calc
      ((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2 ≤
          ((n + 1 : ℕ) : ℝ) ^ 2 - (n : ℝ) ^ 2 :=
        sub_le_sub_left hnsq_le_tsq _
      _ = 2 * (n : ℝ) + 1 := by rw [hcastSucc]; ring
      _ ≤ 3 * t := by linarith
  have hlogcoeff :
      Real.log 2 / 2 * (3 * t) ≤ 2 * (t * Real.log t) := by
    calc
      Real.log 2 / 2 * (3 * t) = (3 * t / 2) * Real.log 2 := by ring
      _ ≤ (3 * t / 2) * Real.log t :=
        mul_le_mul_of_nonneg_left hlogtwo_le (by positivity)
      _ ≤ 2 * (t * Real.log t) := by
        have := mul_le_mul_of_nonneg_right (show 3 * t / 2 ≤ 2 * t by linarith) hlogt
        nlinarith
  have hlowerGapBound :
      Real.log 2 / 2 * (t ^ 2 - (n : ℝ) ^ 2) ≤
        2 * (t * Real.log t) := by
    calc
      Real.log 2 / 2 * (t ^ 2 - (n : ℝ) ^ 2) ≤
          Real.log 2 / 2 * (3 * t) :=
        mul_le_mul_of_nonneg_left hlowerGap (by positivity)
      _ ≤ 2 * (t * Real.log t) := hlogcoeff
  have hupperGapBound :
      Real.log 2 / 2 * (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) ≤
        2 * (t * Real.log t) := by
    calc
      Real.log 2 / 2 * (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) ≤
          Real.log 2 / 2 * (3 * t) :=
        mul_le_mul_of_nonneg_left hupperGap (by positivity)
      _ ≤ 2 * (t * Real.log t) := hlogcoeff
  have hrate : 0 ≤ t * Real.log t := mul_nonneg ht0 hlogt
  have hlowerSum :
      3 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) +
          Real.log 2 / 2 * (t ^ 2 - (n : ℝ) ^ 2) ≤
        8 * (t * Real.log t) := by
    calc
      3 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) +
          Real.log 2 / 2 * (t ^ 2 - (n : ℝ) ^ 2) ≤
          6 * (t * Real.log t) + 2 * (t * Real.log t) :=
        add_le_add hnTerm hlowerGapBound
      _ = 8 * (t * Real.log t) := by ring
  have hupperSum :
      3 * ((n + 1 : ℕ) : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) +
          Real.log 2 / 2 * (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) ≤
        14 * (t * Real.log t) := by
    calc
      3 * ((n + 1 : ℕ) : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) +
          Real.log 2 / 2 * (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) ≤
          12 * (t * Real.log t) + 2 * (t * Real.log t) :=
        add_le_add hnsuccTerm hupperGapBound
      _ = 14 * (t * Real.log t) := by ring
  rw [abs_le]
  constructor
  · calc
      -(16 * (t * Real.log t)) ≤ -(8 * (t * Real.log t)) := by
        exact neg_le_neg (mul_le_mul_of_nonneg_right (by norm_num : (8 : ℝ) ≤ 16) hrate)
      _ ≤ -(3 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) -
          Real.log 2 / 2 * (t ^ 2 - (n : ℝ) ^ 2) := by
        simpa [neg_add] using neg_le_neg hlowerSum
      _ ≤ fabiusLogProfile F t - Real.log 2 / 2 * t ^ 2 := herrorLower
  · calc
      fabiusLogProfile F t - Real.log 2 / 2 * t ^ 2 ≤
          3 * ((n + 1 : ℕ) : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) +
            Real.log 2 / 2 * (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) := herrorUpper
      _ ≤ 14 * (t * Real.log t) := hupperSum
      _ ≤ 16 * (t * Real.log t) :=
        mul_le_mul_of_nonneg_right (by norm_num) hrate

/-- The full logarithmic profile has the coarse equation-(11) error rate. -/
theorem fabiusLogProfile_sub_quadratic_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun t : ℝ => fabiusLogProfile F t - Real.log 2 / 2 * t ^ 2) =O[atTop]
      (fun t : ℝ => t * Real.log t) := by
  rw [isBigO_iff]
  refine ⟨16, ?_⟩
  filter_upwards [eventually_abs_fabiusLogProfile_sub_quadratic_le F hF,
    eventually_ge_atTop (2 : ℝ)] with t hbound ht
  have hrate : 0 ≤ t * Real.log t :=
    mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  change |fabiusLogProfile F t - Real.log 2 / 2 * t ^ 2| ≤
    16 * |t * Real.log t|
  rw [abs_of_nonneg hrate]
  exact hbound

/-- Equation (11) in the draft's original sign convention: the logarithm of
`F(2⁻ᵗ)` differs from `-(log 2)t²/2` by `O(t log t)`. -/
theorem log_fabiusLogPhi_add_quadratic_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun t : ℝ => Real.log (fabiusLogPhi F t) + Real.log 2 / 2 * t ^ 2)
      =O[atTop] (fun t : ℝ => t * Real.log t) := by
  have h := (fabiusLogProfile_sub_quadratic_isBigO F hF).neg_left
  apply h.congr'
  · exact Filter.Eventually.of_forall fun t => by
      unfold fabiusLogProfile
      ring
  · exact EventuallyEq.rfl


end Fabius
