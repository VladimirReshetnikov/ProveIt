import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

open Filter

namespace Erdos3

def amplificationGain (κ H₀ : ℝ) : ℕ → ℝ
  | 0 => H₀
  | j + 1 => κ * amplificationGain κ H₀ j ^ 2

theorem amplificationGain_closed {κ : ℝ} (hκ : κ ≠ 0) (H₀ : ℝ) (j : ℕ) :
    amplificationGain κ H₀ j = κ⁻¹ * (κ * H₀) ^ (2 ^ j) := by
  induction j with
  | zero => simp [amplificationGain, hκ]
  | succ j ih =>
    rw [amplificationGain, ih, show (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 from pow_succ 2 j,
      pow_mul]
    field_simp

theorem amplificationGain_pos {κ H₀ : ℝ} (hκ : 0 < κ) (hH : 0 < H₀) (j : ℕ) :
    0 < amplificationGain κ H₀ j := by
  rw [amplificationGain_closed hκ.ne']
  positivity

theorem amplificationGain_tendsto {κ H₀ : ℝ} (hκ : 0 < κ) (hH : 1 < κ * H₀) :
    Tendsto (amplificationGain κ H₀) atTop atTop := by
  have hpow : Tendsto (fun j : ℕ ↦ (2 : ℕ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have h := ((tendsto_pow_atTop_atTop_of_one_lt hH).comp hpow).const_mul_atTop
    (inv_pos.mpr hκ)
  have heq : amplificationGain κ H₀ = fun j ↦ κ⁻¹ * (κ * H₀) ^ (2 ^ j) :=
    funext (amplificationGain_closed hκ.ne' H₀)
  simpa only [heq, Function.comp_apply] using h

theorem exists_amplificationGain_mul_ge_one {κ H₀ a : ℝ}
    (hκ : 0 < κ) (hH : 1 < κ * H₀) (ha : 0 < a) :
    ∃ j : ℕ, 1 ≤ amplificationGain κ H₀ j * a := by
  obtain ⟨j, hj⟩ := ((amplificationGain_tendsto hκ hH).eventually
    (eventually_ge_atTop (1 / a))).exists
  exact ⟨j, (div_le_iff₀ ha).mp hj⟩

def amplificationResource (p : ℝ) (D K : ℕ) : ℕ → ℝ
  | 0 => (2 + p) ^ D
  | j + 1 => (2 + amplificationResource p D K j) ^ K

theorem amplificationResource_ge_two {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (j : ℕ) :
    2 ≤ amplificationResource p D K j := by
  induction j with
  | zero =>
    change 2 ≤ (2 + p) ^ D
    have h := pow_le_pow_right₀ (show 1 ≤ 2 + p by linarith) hD
    simp only [pow_one] at h
    linarith
  | succ j ih =>
    change 2 ≤ (2 + amplificationResource p D K j) ^ K
    have h := pow_le_pow_right₀ (show 1 ≤ 2 + amplificationResource p D K j by linarith) hK
    simp only [pow_one] at h
    linarith

theorem amplificationResource_room {x : ℝ} (hx : 0 ≤ x) (E : ℕ) :
    x + (2 + x) ^ E ≤ (2 + x) ^ (E + 1) := by
  have hp : 1 ≤ (2 + x) ^ E := one_le_pow₀ (by linarith)
  rw [pow_succ]
  nlinarith

theorem log_amplificationResource_le {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 2 ≤ K) (j : ℕ) :
    Real.log (amplificationResource p D K j) ≤
      (K : ℝ) ^ j * (D * Real.log (2 + p) + 2 * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hmain : ∀ j : ℕ, Real.log (amplificationResource p D K j) + 2 * Real.log 2 ≤
      (K : ℝ) ^ j * (D * Real.log (2 + p) + 2 * Real.log 2) := by
    intro j
    induction j with
    | zero => simp [amplificationResource, Real.log_pow]
    | succ j ih =>
      have hx := amplificationResource_ge_two hp hD (by omega : 1 ≤ K) j
      have hlog : Real.log (2 + amplificationResource p D K j) ≤
          Real.log (amplificationResource p D K j) + Real.log 2 := by
        calc
          _ ≤ Real.log (amplificationResource p D K j * 2) :=
            Real.log_le_log (by linarith) (by linarith)
          _ = _ := Real.log_mul (by linarith) (by norm_num)
      have hstep : Real.log (amplificationResource p D K (j + 1)) =
          K * Real.log (2 + amplificationResource p D K j) := by
        rw [amplificationResource, Real.log_pow]
      rw [hstep, pow_succ]
      have hlogK := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ K by positivity)
      have hihK := mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ K by positivity)
      nlinarith
  exact (by linarith [hmain j])

end Erdos3

end

section

namespace Erdos3

theorem pow_log_exchange {b p : ℝ} (hb : 0 < b) (hp : 0 < p) (t : ℝ) :
    b ^ (t * Real.log p) = p ^ (t * Real.log b) := by
  rw [Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hp]
  congr 1
  ring

theorem pow_floor_log_le {b p t : ℝ} (hb : 1 < b) (hp : 1 ≤ p) (ht : 0 ≤ t) :
    b ^ ⌊t * Real.log p⌋₊ ≤ p ^ (t * Real.log b) := by
  rw [← pow_log_exchange (by linarith : 0 < b) (by linarith : 0 < p) t,
    ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hb.le
  exact Nat.floor_le (mul_nonneg ht (Real.log_nonneg hp))

theorem div_le_pow_floor_log {b p t : ℝ} (hb : 1 < b) (hp : 0 < p) :
    p ^ (t * Real.log b) / b ≤ b ^ ⌊t * Real.log p⌋₊ := by
  have hb0 : 0 < b := by linarith
  apply (div_le_iff₀ hb0).mpr
  calc
    p ^ (t * Real.log b) = b ^ (t * Real.log p) := (pow_log_exchange hb0 hp t).symm
    _ ≤ b ^ ((⌊t * Real.log p⌋₊ : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le hb.le (Nat.lt_floor_add_one _).le
    _ = b ^ ⌊t * Real.log p⌋₊ * b := by
      rw [Real.rpow_add hb0, Real.rpow_one, Real.rpow_natCast]

noncomputable def levelCoefficient (K : ℝ) : ℝ := 1 / (4 * Real.log K)

noncomputable def gainExponent (K : ℝ) : ℝ := levelCoefficient K * Real.log 2

noncomputable def potentialExponent (K : ℝ) : ℝ := 1 - gainExponent K / 2

theorem levelCoefficient_pos {K : ℝ} (hK : 1 < K) : 0 < levelCoefficient K := by
  unfold levelCoefficient
  exact one_div_pos.mpr (mul_pos (by norm_num) (Real.log_pos hK))

theorem levelCoefficient_mul_log {K : ℝ} (hK : 1 < K) :
    levelCoefficient K * Real.log K = 1 / 4 := by
  unfold levelCoefficient
  have hlog : Real.log K ≠ 0 := (Real.log_pos hK).ne'
  field_simp

theorem gainExponent_pos_le_quarter {K : ℝ} (hK : 2 ≤ K) :
    0 < gainExponent K ∧ gainExponent K ≤ 1 / 4 := by
  have hK1 : 1 < K := by linarith
  have ht := levelCoefficient_pos hK1
  constructor
  · exact mul_pos ht (Real.log_pos (by norm_num))
  · have hlog : Real.log 2 ≤ Real.log K := Real.log_le_log (by norm_num) hK
    have h := mul_le_mul_of_nonneg_left hlog ht.le
    rwa [levelCoefficient_mul_log hK1] at h

theorem potentialExponent_bounds {K : ℝ} (hK : 2 ≤ K) :
    1 / 4 < potentialExponent K ∧ potentialExponent K < 1 ∧
      potentialExponent K + gainExponent K - 1 = gainExponent K / 2 := by
  obtain ⟨hν0, hν1⟩ := gainExponent_pos_le_quarter hK
  unfold potentialExponent
  constructor
  · linarith
  constructor
  · linarith
  · ring

theorem resource_base_at_selected_level {K p : ℝ} (hK : 1 < K) (hp : 1 ≤ p) :
    K ^ ⌊levelCoefficient K * Real.log p⌋₊ ≤ p ^ (1 / 4 : ℝ) := by
  have h := pow_floor_log_le hK hp (levelCoefficient_pos hK).le
  rwa [levelCoefficient_mul_log hK] at h

theorem gain_base_at_selected_level {K p : ℝ} (hK : 1 < K) (hp : 1 ≤ p) :
    p ^ gainExponent K / 2 ≤ (2 : ℝ) ^ ⌊levelCoefficient K * Real.log p⌋₊ ∧
      (2 : ℝ) ^ ⌊levelCoefficient K * Real.log p⌋₊ ≤ p ^ gainExponent K := by
  constructor
  · exact div_le_pow_floor_log (by norm_num) (by linarith)
  · exact pow_floor_log_le (by norm_num) hp (levelCoefficient_pos hK).le

end Erdos3

end

section

namespace Erdos3

theorem amplificationResource_add_two_le_succ {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (j : ℕ) :
    amplificationResource p D K j + 2 ≤ amplificationResource p D K (j + 1) := by
  have hj := amplificationResource_ge_two hp hD hK j
  have hpow := pow_le_pow_right₀
    (show 1 ≤ 2 + amplificationResource p D K j by linarith) hK
  simpa only [pow_one, amplificationResource, add_comm] using hpow

theorem amplificationResource_strictMono {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) :
    StrictMono (amplificationResource p D K) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have h := amplificationResource_add_two_le_succ hp hD hK j
  linarith

theorem amplificationResource_monotone {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) :
    Monotone (amplificationResource p D K) :=
  (amplificationResource_strictMono hp hD hK).monotone

theorem amplificationResource_zero_le {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (j : ℕ) :
    amplificationResource p D K 0 ≤ amplificationResource p D K j :=
  amplificationResource_monotone hp hD hK (Nat.zero_le j)

theorem amplificationResource_parameter_le_zero {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) : p ≤ amplificationResource p D K 0 := by
  have hpow := pow_le_pow_right₀ (show 1 ≤ 2 + p by linarith) hD
  simp only [pow_one] at hpow
  change p ≤ (2 + p) ^ D
  linarith

theorem amplificationResource_parameter_le {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (j : ℕ) :
    p ≤ amplificationResource p D K j :=
  (amplificationResource_parameter_le_zero hp hD).trans
    (amplificationResource_zero_le hp hD hK j)

theorem amplificationResource_max_threshold_le {p b : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K)
    (hb : b ≤ amplificationResource p D K 0) (j : ℕ) :
    max b 2 ≤ amplificationResource p D K j :=
  max_le (hb.trans (amplificationResource_zero_le hp hD hK j))
    (amplificationResource_ge_two hp hD hK j)

theorem amplificationResource_max_nat_threshold_le {p : ℝ} {D K n₀ : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K)
    (hn₀ : (n₀ : ℝ) ≤ amplificationResource p D K 0) (j : ℕ) :
    max (n₀ : ℝ) 2 ≤ amplificationResource p D K j :=
  amplificationResource_max_threshold_le hp hD hK hn₀ j

end Erdos3

end

section

namespace Erdos3

theorem amplificationFinalCost_one_le {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (E j : ℕ) :
    1 ≤ (2 + amplificationResource p D K j) ^ E := by
  apply one_le_pow₀
  have h := amplificationResource_ge_two hp hD hK j
  linarith

theorem amplificationFinalCost_add_two_le {p : ℝ} {D K E : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (hE : 1 ≤ E) (j : ℕ) :
    amplificationResource p D K j + 2 ≤ (2 + amplificationResource p D K j) ^ E := by
  have h := amplificationResource_ge_two hp hD hK j
  have hpow := pow_le_pow_right₀
    (show 1 ≤ 2 + amplificationResource p D K j by linarith) hE
  simpa only [pow_one, add_comm] using hpow

theorem amplificationFinalCost_resource_le {p : ℝ} {D K E : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (hE : 1 ≤ E) (j : ℕ) :
    amplificationResource p D K j ≤ (2 + amplificationResource p D K j) ^ E := by
  have h := amplificationFinalCost_add_two_le hp hD hK hE j
  linarith

theorem amplificationFinalCost_pos {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 1 ≤ K) (E j : ℕ) :
    0 < (2 + amplificationResource p D K j) ^ E :=
  zero_lt_one.trans_le (amplificationFinalCost_one_le hp hD hK E j)

end Erdos3

end

end OAI
