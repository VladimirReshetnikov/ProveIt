import GowersSzemeredi.Proofs16AlphabetLineCover
import GowersSzemeredi.Proofs16Lemma6Parameters

/-! Elementary bounds for the constant-line certificates used to audit the
packaged hypotheses of Lemma 16.10. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem alphabet_cover_controls (k : Nat) {sigma gamma r : Real}
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hr : 1 ≤ r) :
    0 < (multipleC (sigma / (2 * r)) gamma k) ^ r ∧
      (multipleC (sigma / (2 * r)) gamma k) ^ r ≤ 1 ∧
      1 ≤ (multipleQ (sigma / (2 * r)) gamma k) ^ r := by
  have heq : r⁻¹ * (sigma / 2) = sigma / (2 * r) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simpa only [Nat.cast_one, one_mul, heq] using
    section16_slice_control_ranges (r := 1) (k := k) (by omega) hr hg hg1
      (show 0 < sigma / 2 by positivity) (show sigma / 2 ≤ 1 by linarith)

theorem section16Lemma9Width_le_scale (m q k : Nat) {sigma theta gamma delta theta1 zeta : Real}
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hr : 1 ≤ section16Lemma9R theta gamma k)
    (ht : 1 ≤ section16T delta theta1 k) (hz : 0 ≤ zeta) (hz1 : zeta ≤ 2) :
    section16Lemma9Width m q k sigma theta gamma delta theta1 zeta ≤ m := by
  obtain ⟨ha, ha1, _⟩ := alphabet_cover_controls (k + 1) hs hs1 hg hg1 hr
  obtain ⟨hb, hb1, _⟩ := alphabet_cover_controls k hs hs1 hd hd1 ht
  have hK : (1 : Real) ≤ section16K k := by
    exact_mod_cast (show 1 ≤ section16K k from Nat.one_le_iff_ne_zero.mpr (by unfold section16K; positivity))
  have hden : (1 : Real) ≤ 2 * (section16K k : Real) ^ (2 ^ (k + 1) * q) := by
    have h := one_le_pow₀ (n := 2 ^ (k + 1) * q) hK
    linarith
  let a : Real := ((multipleC (sigma / (2 * section16Lemma9R theta gamma k)) gamma (k + 1)) ^
      section16Lemma9R theta gamma k *
      (multipleC (sigma / (2 * section16T delta theta1 k)) delta k) ^ section16T delta theta1 k) /
      (2 * (section16K k : Real) ^ (2 ^ (k + 1) * q))
  have ha0 : 0 < a := div_pos (mul_pos ha hb) (zero_lt_one.trans_le hden)
  have haone : a ≤ 1 := by
    exact (div_le_one (zero_lt_one.trans_le hden)).mpr ((mul_le_one₀ ha1 hb.le hb1).trans hden)
  change (zeta / 2) * (m : Real) ^ a ≤ m
  have hscale : (m : Real) ^ a ≤ m := by
    by_cases hm : m = 0
    · simp only [hm, Nat.cast_zero, Real.zero_rpow ha0.ne', le_refl]
    · have hm1 : (1 : Real) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hm1 haone
  calc
    _ ≤ 1 * (m : Real) ^ a := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _)
    _ ≤ m := by simpa only [one_mul] using hscale

theorem alphabet_q_bound_amplification (k : Nat) {sigma r : Real}
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (hr : 1 ≤ r) :
    r * multipleQ (1 / 2) 1 k ≤ (multipleQ (sigma / (2 * r)) 1 k) ^ r := by
  let E : Nat := 2 ^ (2 ^ (k + 8))
  have hE : 0 < E := by dsimp [E]; positivity
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hbase : 2 * r ≤ 2 * r / sigma := (le_div_iff₀ hs).mpr (by nlinarith)
  have hq : multipleQ (sigma / (2 * r)) 1 k = (2 * r / sigma) ^ E := by
    simp only [multipleQ, multipleC, one_mul, ← inv_pow, inv_div, E]
  have hqhalf : multipleQ (1 / 2) 1 k = (2 : Real) ^ E := by
    simp only [multipleQ, multipleC, one_mul, ← inv_pow, inv_div, div_one, E]
  have hamplify : r * multipleQ (1 / 2) 1 k ≤ multipleQ (sigma / (2 * r)) 1 k := by
    rw [hq, hqhalf]
    calc
      r * (2 : Real) ^ E ≤ r ^ E * 2 ^ E := mul_le_mul_of_nonneg_right
        (le_self_pow₀ hr hE.ne') (by positivity)
      _ = (2 * r) ^ E := by rw [mul_pow]; ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hbase _
  have hqone : 1 ≤ multipleQ (sigma / (2 * r)) 1 k := by
    rw [hq]
    exact one_le_pow₀ (by linarith)
  exact hamplify.trans (Real.self_le_rpow_of_one_le hqone hr)

end LeanProofs.GowersSzemeredi
