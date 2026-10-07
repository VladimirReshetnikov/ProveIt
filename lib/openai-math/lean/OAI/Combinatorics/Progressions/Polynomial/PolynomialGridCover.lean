import OAI.Combinatorics.Progressions.Sampling.RationalGridMajorSet

namespace OAI

section

namespace Erdos3

theorem inverse_power_mono {A B ζ : ℝ} {a b : ℕ}
    (hB : 0 ≤ B) (hAB : A ≤ B) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hab : a ≤ b) :
    A / ζ ^ a ≤ B / ζ ^ b := by
  exact div_le_div₀ hB hAB (pow_pos hζ _)
    (pow_le_pow_of_le_one hζ.le hζ1 hab)

theorem one_le_inverse_power {C ζ : ℝ} (hC : 1 ≤ C) (hζ : 0 < ζ)
    (hζ1 : ζ ≤ 1) (r : ℕ) : 1 ≤ C / ζ ^ r := by
  apply (le_div_iff₀ (pow_pos hζ r)).mpr
  simpa only [one_mul] using (pow_le_one₀ hζ.le hζ1 : ζ ^ r ≤ 1).trans hC

noncomputable def polynomialGridCover (J : Type*) [Fintype J] [DecidableEq J]
    (M : ℕ) (C : ℝ) (r : ℕ) (ζ : ℝ) : Finset (J → Fin M) :=
  rationalGridMajorBox J M ⌈C / ζ ^ r⌉₊ ⌈C / ζ ^ r⌉₊

theorem rationalGridMajorBox_ceil_card (J : Type*) [Fintype J] [DecidableEq J]
    (M : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    ((rationalGridMajorBox J M ⌈X⌉₊ ⌈X⌉₊).card : ℝ) ≤
      (195 * X ^ 4) ^ Fintype.card J := by
  have hX0 : 0 ≤ X := by linarith
  have hQ0 : (0 : ℝ) ≤ ⌈X⌉₊ := Nat.cast_nonneg _
  have hQ : (⌈X⌉₊ : ℝ) ≤ 2 * X := by
    have := Nat.ceil_lt_add_one hX0
    linarith
  have hQ1 : (⌈X⌉₊ : ℝ) + 1 ≤ 3 * X := by linarith
  have hp := mul_le_mul hQ hQ1 (by positivity : 0 ≤ (⌈X⌉₊ : ℝ) + 1) (by positivity)
  have hm : 2 * (⌈X⌉₊ : ℝ) * (⌈X⌉₊ + 1) + 1 ≤ 13 * X ^ 2 := by
    nlinarith [sq_nonneg (X - 1)]
  have hr : 2 * (⌈X⌉₊ : ℝ) + 1 ≤ 5 * X := by linarith
  have hbase : ((⌈X⌉₊ : ℝ) + 1) * (2 * ⌈X⌉₊ * (⌈X⌉₊ + 1) + 1) *
      (2 * ⌈X⌉₊ + 1) ≤ 195 * X ^ 4 := by
    calc
      _ ≤ (3 * X) * (13 * X ^ 2) * (5 * X) := by gcongr
      _ = _ := by ring
  exact (rationalGridMajorBox_card J M ⌈X⌉₊ ⌈X⌉₊).trans
    (pow_le_pow_left₀ (by positivity) hbase _)

theorem polynomialGridCover_card (J : Type*) [Fintype J] [DecidableEq J]
    (M : ℕ) {C ζ : ℝ} (r : ℕ) (hC : 1 ≤ C) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ((polynomialGridCover J M C r ζ).card : ℝ) ≤
      (195 * C ^ 4) ^ Fintype.card J / ζ ^ (4 * r * Fintype.card J) := by
  have h := rationalGridMajorBox_ceil_card J M (one_le_inverse_power hC hζ hζ1 r)
  unfold polynomialGridCover
  apply h.trans_eq
  simp only [div_pow, ← mul_div_assoc, ← pow_mul]
  rw [Nat.mul_comm r 4]

end Erdos3

end

end OAI
