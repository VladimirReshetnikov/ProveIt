import DiophantineConsistency.ConsecutivePell
import Mathlib.Data.ZMod.Basic

/-!
# Integer minimum norms for the ordinary strong-gap system

These are local arithmetic certificates for report 47's minimum-norm
finalizers. They do not identify ordinary and normalized strong equations in
the same coordinates, and do not assume a compiler or consistency bridge.
-/

namespace DiophantineConsistency.MinimumNorm

set_option maxRecDepth 8000

private theorem not_isSquare_between (d n : ℤ) (hn : 0 ≤ n)
    (hlo : n ^ 2 < d) (hhi : d < (n + 1) ^ 2) : ¬ IsSquare d := by
  rintro ⟨x, hx⟩
  have hs : d = |x| ^ 2 := by rw [sq_abs]; simpa only [pow_two] using hx
  have hl : n < |x| := (sq_lt_sq₀ hn (abs_nonneg x)).mp (by simpa only [← hs] using hlo)
  have hh : |x| < n + 1 :=
    (sq_lt_sq₀ (abs_nonneg x) (by omega)).mp (by simpa only [← hs] using hhi)
  omega

/-- A nonzero second coordinate cannot have zero norm at a nonsquare integer. -/
theorem norm_ne_zero_of_not_isSquare (d x y : ℤ) (hd : ¬ IsSquare d) (hy : y ≠ 0) :
    x ^ 2 - d * y ^ 2 ≠ 0 := by
  intro h
  have he : x ^ 2 = y ^ 2 * d := by nlinarith only [h]
  obtain ⟨k, hk⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp
    (show y ^ 2 ∣ x ^ 2 from ⟨d, he⟩)
  exact hd ⟨k, by
    rw [hk, mul_pow] at he
    simpa only [pow_two] using (mul_left_cancel₀ (pow_ne_zero 2 hy) he).symm⟩

theorem consecutive_not_isSquare (n : ℤ) (hn : 1 ≤ n) : ¬ IsSquare (n * (n + 1)) := by
  apply not_isSquare_between _ n (by omega) <;> nlinarith

theorem consecutive_norm_ne_zero (n x y : ℤ) (hn : 1 ≤ n) (hy : y ≠ 0) :
    x ^ 2 - n * (n + 1) * y ^ 2 ≠ 0 :=
  norm_ne_zero_of_not_isSquare _ _ _ (consecutive_not_isSquare n hn) hy

theorem main_discriminant_not_isSquare (a : ℤ) (ha : 0 ≤ a) :
    ¬ IsSquare (a ^ 2 + 4 * a + 3) := by
  apply not_isSquare_between _ (a+1) (by omega) <;> nlinarith

theorem main_norm_ne_zero (a x y : ℤ) (ha : 0 ≤ a) (hy : y ≠ 0) :
    x ^ 2 - (a ^ 2 + 4 * a + 3) * y ^ 2 ≠ 0 :=
  norm_ne_zero_of_not_isSquare _ _ _ (main_discriminant_not_isSquare a ha) hy

/-- This discriminant excludes the negative unit by its residue modulo four. -/
theorem main_norm_ne_neg_one (a x y : ℤ) :
    x ^ 2 - (a ^ 2 + 4 * a + 3) * y ^ 2 ≠ -1 := by
  intro he
  have hm := congrArg (fun z : ℤ => (z : ZMod 4)) he
  push_cast at hm
  have bad : ∀ a x y : ZMod 4, x ^ 2 - (a ^ 2 + 4 * a + 3) * y ^ 2 ≠ -1 := by decide
  exact bad _ _ _ hm

theorem square_ge_one_of_ne_zero (z : ℤ) (hz : z ≠ 0) : 1 ≤ z ^ 2 := by
  have hp := sq_pos_of_ne_zero hz
  omega

theorem square_eq_one_iff (z : ℤ) (hz : z ≠ -1) : z ^ 2 = 1 ↔ z = 1 := by
  rw [sq_eq_one_iff]
  exact or_iff_left hz

theorem consecutive_norm_minimum (n x y : ℤ) (hn : 2 ≤ n) (hy : y ≠ 0) :
    1 ≤ (x ^ 2 - n * (n+1) * y ^ 2) ^ 2 ∧
      ((x ^ 2 - n * (n+1) * y ^ 2) ^ 2 = 1 ↔ x ^ 2 - n * (n+1) * y ^ 2 = 1) :=
  ⟨square_ge_one_of_ne_zero _ (consecutive_norm_ne_zero n x y (by omega) hy),
    square_eq_one_iff _ (ConsecutivePell.norm_ne_neg_one n x y hn)⟩

theorem main_norm_minimum (a x y : ℤ) (ha : 0 ≤ a) (hy : y ≠ 0) :
    1 ≤ (x ^ 2 - (a ^ 2 + 4*a + 3) * y ^ 2) ^ 2 ∧
      ((x ^ 2 - (a ^ 2 + 4*a + 3) * y ^ 2) ^ 2 = 1 ↔
        x ^ 2 - (a ^ 2 + 4*a + 3) * y ^ 2 = 1) :=
  ⟨square_ge_one_of_ne_zero _ (main_norm_ne_zero a x y ha hy),
    square_eq_one_iff _ (main_norm_ne_neg_one a x y)⟩

/-- The gap auxiliary norm, with no sign restriction on `V` or `V+e`. -/
def auxiliary {R : Type*} [CommRing R] (U V e : R) : R :=
  U * V ^ 2 - (U - 1) * (V + e) ^ 2

def strongGap {R : Type*} [CommRing R] (U I : R) : R := I ^ 2 - U

theorem auxiliary_expanded {R : Type*} [CommRing R] (U V e : R) :
    auxiliary U V e = U * (V ^ 2 - (V+e) ^ 2) + (V+e) ^ 2 := by
  unfold auxiliary
  ring

/-- The gap presentation removes the highest common square from the auxiliary
norm; this is the degree cancellation used by report 47. -/
theorem auxiliary_gap_identity {R : Type*} [CommRing R] (U V e : R) :
    auxiliary U V e = V ^ 2 - (U-1) * e * (2*V+e) := by
  unfold auxiliary
  ring

theorem main_norm_cancellation {R : Type*} [CommRing R] (a c X gamma : R) :
    (X + a*c + gamma*(4*a+3)) ^ 2 - (a ^ 2 + 4*a+3) * c ^ 2 =
      2*a*c*(X + gamma*(4*a+3)) + (X + gamma*(4*a+3)) ^ 2 - (4*a+3)*c ^ 2 := by ring

/-- A positive gap excludes zero auxiliary norm when `U ≥ 2`. -/
theorem auxiliary_ne_zero (U V e : ℤ) (hU : 2 ≤ U) (he : 0 < e) :
    auxiliary U V e ≠ 0 := by
  intro ha
  have hy : V + e ≠ 0 := by
    intro hy
    have hm : U * V ^ 2 = 0 := by simpa only [auxiliary, hy, zero_pow (by decide : 2 ≠ 0),
      mul_zero, sub_zero] using ha
    have hv : V = 0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hm).resolve_left (by omega))
    omega
  apply consecutive_norm_ne_zero (U-1) (U*V) (V+e) (by omega) hy
  calc
    (U*V) ^ 2 - (U-1) * (U-1+1) * (V+e) ^ 2 = U * auxiliary U V e := by
      unfold auxiliary
      ring
    _ = 0 := by rw [ha, mul_zero]

/-- A square auxiliary parameter also excludes the negative unit modulo four. -/
theorem square_auxiliary_ne_neg_one (I V e : ℤ) : auxiliary (I ^ 2) V e ≠ -1 := by
  intro he
  have hm := congrArg (fun z : ℤ => (z : ZMod 4)) he
  simp only [auxiliary] at hm
  push_cast at hm
  have bad : ∀ I V e : ZMod 4,
      I ^ 2 * V ^ 2 - (I ^ 2 - 1) * (V + e) ^ 2 ≠ -1 := by decide
  exact bad _ _ _ hm

theorem auxiliary_ne_neg_one_of_gap_zero (U V e I : ℤ) (hW : strongGap U I = 0) :
    auxiliary U V e ≠ -1 := by
  have hU : U = I ^ 2 := by unfold strongGap at hW; linarith
  rw [hU]
  exact square_auxiliary_ne_neg_one I V e

/-- The degenerate `U=0` branch stays strictly above the desired block minimum. -/
theorem zero_parameter_block_gt_one (V e I : ℤ) (hI : 2 ≤ |I|) :
    1 < (auxiliary 0 V e) ^ 2 + (strongGap 0 I) ^ 2 := by
  have hisq : (4 : ℤ) ≤ I ^ 2 := by
    have h := (sq_le_sq₀ (by norm_num : (0 : ℤ) ≤ 2) (abs_nonneg I)).mpr hI
    norm_num only [sq_abs, Int.reducePow] at h
    exact h
  have hw : (16 : ℤ) ≤ (strongGap 0 I) ^ 2 := by
    unfold strongGap
    nlinarith [sq_nonneg (I ^ 2 - 4)]
  nlinarith [sq_nonneg (auxiliary 0 V e)]

theorem coupled_block_ge_one (U V e I : ℤ) (he : 0 < e)
    (hU : U = 0 ∨ 2 ≤ U) (hI : U = 0 → 2 ≤ |I|) :
    1 ≤ (auxiliary U V e) ^ 2 + (strongGap U I) ^ 2 := by
  rcases hU with rfl | hU
  · exact (zero_parameter_block_gt_one V e I (hI rfl)).le
  · have haux := square_ge_one_of_ne_zero _ (auxiliary_ne_zero U V e hU he)
    nlinarith [sq_nonneg (strongGap U I)]

/-- The coupled block reaches its integer minimum exactly at the positive
auxiliary unit and a vanishing ordinary strong gap. -/
theorem coupled_block_eq_one_iff (U V e I : ℤ) (he : 0 < e)
    (hU : U = 0 ∨ 2 ≤ U) (hI : U = 0 → 2 ≤ |I|) :
    (auxiliary U V e) ^ 2 + (strongGap U I) ^ 2 = 1 ↔
      auxiliary U V e = 1 ∧ strongGap U I = 0 := by
  constructor
  · intro h
    rcases hU with rfl | hU
    · have hbig := zero_parameter_block_gt_one V e I (hI rfl)
      omega
    · have haux := square_ge_one_of_ne_zero _ (auxiliary_ne_zero U V e hU he)
      have hWsq : (strongGap U I) ^ 2 = 0 := by nlinarith [sq_nonneg (strongGap U I)]
      have hW := sq_eq_zero_iff.mp hWsq
      have hauxsq : (auxiliary U V e) ^ 2 = 1 := by nlinarith
      exact ⟨(square_eq_one_iff _ (auxiliary_ne_neg_one_of_gap_zero U V e I hW)).mp hauxsq, hW⟩
  · rintro ⟨ha, hw⟩
    rw [ha, hw]
    norm_num

theorem ordinary_parameter_alternatives (a f : ℤ) (ha : 0 ≤ a) (hf : 1 ≤ f) :
    (a ^ 2 + 4*a + 3) * (f ^ 2 - 1) = 0 ∨
      2 ≤ (a ^ 2 + 4*a + 3) * (f ^ 2 - 1) := by
  by_cases hf1 : f = 1
  · simp only [hf1, one_pow, sub_self, mul_zero, true_or]
  · right
    have hdelta : 3 ≤ a ^ 2 + 4*a + 3 := by nlinarith [sq_nonneg a]
    have hf2 : 2 ≤ f := by omega
    have hfactor : 3 ≤ f ^ 2 - 1 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hdelta) (sub_nonneg.mpr hfactor)]

theorem ordinary_root_ge_nine (i c : ℤ) (hi : 1 ≤ i) (hc : 3 ≤ c) : 9 ≤ i * c ^ 2 := by
  have hc2 : 9 ≤ c ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hi (sq_nonneg c)
  nlinarith

theorem ordinary_coupled_minimum (a f i c V e : ℤ)
    (ha : 0 ≤ a) (hf : 1 ≤ f) (hi : 1 ≤ i) (hc : 3 ≤ c) (he : 0 < e) :
    let U := (a ^ 2 + 4*a + 3) * (f ^ 2 - 1)
    let I := i * c ^ 2
    1 ≤ (auxiliary U V e) ^ 2 + (strongGap U I) ^ 2 ∧
      ((auxiliary U V e) ^ 2 + (strongGap U I) ^ 2 = 1 ↔
        auxiliary U V e = 1 ∧ strongGap U I = 0) := by
  dsimp only
  have hU := ordinary_parameter_alternatives a f ha hf
  have hI : (a ^ 2 + 4*a + 3) * (f ^ 2 - 1) = 0 → 2 ≤ |i * c ^ 2| := by
    intro _
    have hbig := ordinary_root_ge_nine i c hi hc
    have hle := le_abs_self (i * c ^ 2)
    omega
  exact ⟨coupled_block_ge_one _ _ _ _ he hU hI, coupled_block_eq_one_iff _ _ _ _ he hU hI⟩

/-- Report 47's clean minimum-norm finalizer, as a polynomial over any ring. -/
def minima76 {R : Type*} [CommRing R] (n0 n1 na W nk rt : R) : R :=
  n0 ^ 2 + n1 ^ 2 + na ^ 2 + W ^ 2 + (nk - 1) ^ 2 + rt ^ 2 - 3

def minima75 {R : Type*} [CommRing R] (n0 n1 na W nk nt : R) : R :=
  n0 ^ 2 + n1 ^ 2 + na ^ 2 + W ^ 2 + (nk * nt - 1) ^ 2 - 3

/-- Three independent integer minima force all six local comparisons. -/
theorem minima76_zero_iff (n0 n1 na W nk rt : ℤ)
    (h0 : 1 ≤ n0 ^ 2) (h0eq : n0 ^ 2 = 1 ↔ n0 = 1)
    (h1 : 1 ≤ n1 ^ 2) (h1eq : n1 ^ 2 = 1 ↔ n1 = 1)
    (ha : 1 ≤ na ^ 2 + W ^ 2) (haeq : na ^ 2 + W ^ 2 = 1 ↔ na = 1 ∧ W = 0) :
    minima76 n0 n1 na W nk rt = 0 ↔
      n0 = 1 ∧ n1 = 1 ∧ na = 1 ∧ W = 0 ∧ nk = 1 ∧ rt = 0 := by
  unfold minima76
  constructor
  · intro h
    have hn0 : n0 ^ 2 = 1 := by nlinarith [sq_nonneg (nk-1), sq_nonneg rt]
    have hn1 : n1 ^ 2 = 1 := by nlinarith [sq_nonneg (nk-1), sq_nonneg rt]
    have hna : na ^ 2 + W ^ 2 = 1 := by nlinarith [sq_nonneg (nk-1), sq_nonneg rt]
    have hnk : (nk-1) ^ 2 = 0 := by nlinarith [sq_nonneg (nk-1), sq_nonneg rt]
    have hrt : rt ^ 2 = 0 := by nlinarith [sq_nonneg (nk-1), sq_nonneg rt]
    obtain ⟨hna1, hw0⟩ := haeq.mp hna
    exact ⟨h0eq.mp hn0, h1eq.mp hn1, hna1, hw0,
      sub_eq_zero.mp (sq_eq_zero_iff.mp hnk), sq_eq_zero_iff.mp hrt⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    norm_num

theorem minima75_zero_iff (n0 n1 na W nk nt : ℤ)
    (h0 : 1 ≤ n0 ^ 2) (h0eq : n0 ^ 2 = 1 ↔ n0 = 1)
    (h1 : 1 ≤ n1 ^ 2) (h1eq : n1 ^ 2 = 1 ↔ n1 = 1)
    (ha : 1 ≤ na ^ 2 + W ^ 2) (haeq : na ^ 2 + W ^ 2 = 1 ↔ na = 1 ∧ W = 0) :
    minima75 n0 n1 na W nk nt = 0 ↔
      n0 = 1 ∧ n1 = 1 ∧ na = 1 ∧ W = 0 ∧ nk * nt = 1 := by
  have h := minima76_zero_iff n0 n1 na W (nk*nt) 0 h0 h0eq h1 h1eq ha haeq
  simpa only [minima76, minima75, zero_pow (by decide : 2 ≠ 0), add_zero, and_true] using h

/-- A closed local certificate with the actual three norm shapes. -/
theorem ordinary_minima76_zero_iff (n x y a D c U V e I nk rt : ℤ)
    (hn : 2 ≤ n) (hy : y ≠ 0) (ha : 0 ≤ a) (hc : c ≠ 0) (he : 0 < e)
    (hU : U = 0 ∨ 2 ≤ U) (hI : U = 0 → 2 ≤ |I|) :
    minima76 (x ^ 2 - n * (n+1) * y ^ 2)
      (D ^ 2 - (a ^ 2 + 4*a + 3) * c ^ 2) (auxiliary U V e) (strongGap U I) nk rt = 0 ↔
      x ^ 2 - n * (n+1) * y ^ 2 = 1 ∧
      D ^ 2 - (a ^ 2 + 4*a + 3) * c ^ 2 = 1 ∧
      auxiliary U V e = 1 ∧ strongGap U I = 0 ∧ nk = 1 ∧ rt = 0 := by
  have h0 := consecutive_norm_minimum n x y hn hy
  have h1 := main_norm_minimum a D c ha hc
  exact minima76_zero_iff _ _ _ _ _ _ h0.1 h0.2 h1.1 h1.2
    (coupled_block_ge_one U V e I he hU hI) (coupled_block_eq_one_iff U V e I he hU hI)

theorem ordinary_minima75_zero_iff (n x y a D c U V e I nk nt : ℤ)
    (hn : 2 ≤ n) (hy : y ≠ 0) (ha : 0 ≤ a) (hc : c ≠ 0) (he : 0 < e)
    (hU : U = 0 ∨ 2 ≤ U) (hI : U = 0 → 2 ≤ |I|) :
    minima75 (x ^ 2 - n * (n+1) * y ^ 2)
      (D ^ 2 - (a ^ 2 + 4*a + 3) * c ^ 2) (auxiliary U V e) (strongGap U I) nk nt = 0 ↔
      x ^ 2 - n * (n+1) * y ^ 2 = 1 ∧
      D ^ 2 - (a ^ 2 + 4*a + 3) * c ^ 2 = 1 ∧
      auxiliary U V e = 1 ∧ strongGap U I = 0 ∧ nk * nt = 1 := by
  have h0 := consecutive_norm_minimum n x y hn hy
  have h1 := main_norm_minimum a D c ha hc
  exact minima75_zero_iff _ _ _ _ _ _ h0.1 h0.2 h1.1 h1.2
    (coupled_block_ge_one U V e I he hU hI) (coupled_block_eq_one_iff U V e I he hU hI)

/-- The full ordinary parameters supply every hypothesis of the clean local
six-comparison certificate. -/
theorem gap_minima76_zero_iff (n x y a D c f i V e nk rt : ℤ)
    (hn : 2 ≤ n) (hy : y ≠ 0) (ha : 0 ≤ a) (hf : 1 ≤ f)
    (hi : 1 ≤ i) (hc : 3 ≤ c) (he : 0 < e) :
    let U := (a ^ 2 + 4*a + 3) * (f ^ 2 - 1)
    let I := i * c ^ 2
    let N0 := x ^ 2 - n * (n+1) * y ^ 2
    let N1 := D ^ 2 - (a ^ 2 + 4*a + 3) * c ^ 2
    minima76 N0 N1 (auxiliary U V e) (strongGap U I) nk rt = 0 ↔
      N0 = 1 ∧ N1 = 1 ∧ auxiliary U V e = 1 ∧ strongGap U I = 0 ∧ nk = 1 ∧ rt = 0 := by
  dsimp only
  have h0 := consecutive_norm_minimum n x y hn hy
  have h1 := main_norm_minimum a D c ha (by omega)
  have haux := ordinary_coupled_minimum a f i c V e ha hf hi hc he
  exact minima76_zero_iff _ _ _ _ _ _ h0.1 h0.2 h1.1 h1.2 haux.1 haux.2

theorem gap_minima75_zero_iff (n x y a D c f i V e nk nt : ℤ)
    (hn : 2 ≤ n) (hy : y ≠ 0) (ha : 0 ≤ a) (hf : 1 ≤ f)
    (hi : 1 ≤ i) (hc : 3 ≤ c) (he : 0 < e) :
    let U := (a ^ 2 + 4*a + 3) * (f ^ 2 - 1)
    let I := i * c ^ 2
    let N0 := x ^ 2 - n * (n+1) * y ^ 2
    let N1 := D ^ 2 - (a ^ 2 + 4*a + 3) * c ^ 2
    minima75 N0 N1 (auxiliary U V e) (strongGap U I) nk nt = 0 ↔
      N0 = 1 ∧ N1 = 1 ∧ auxiliary U V e = 1 ∧ strongGap U I = 0 ∧ nk * nt = 1 := by
  dsimp only
  have h0 := consecutive_norm_minimum n x y hn hy
  have h1 := main_norm_minimum a D c ha (by omega)
  have haux := ordinary_coupled_minimum a f i c V e ha hf hi hc he
  exact minima75_zero_iff _ _ _ _ _ _ h0.1 h0.2 h1.1 h1.2 haux.1 haux.2

end DiophantineConsistency.MinimumNorm
