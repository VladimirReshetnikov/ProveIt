import OAI.Combinatorics.Progressions.Nilpotent.BCHOuterGridChangeBasis

namespace OAI

section

namespace Erdos3

open Module

theorem integral_grid_allowance_le_exp (K d H l : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ((K * H ^ (d ^ 3) * l : ℕ) : ℝ) ≤ Real.exp ((p + (K + 5 : ℕ)) ^ (K + 5)) := by
  let C := K + 5
  let t : ℝ := p + C
  have ht : 5 ≤ t := by dsimp [t, C]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) K]
  have hpt : p ≤ t := by dsimp [t]; exact le_add_of_nonneg_right (Nat.cast_nonneg C)
  have hKt : (K : ℝ) ≤ t := by dsimp [t, C]; push_cast; linarith
  have htt : t ≤ t ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ (show 1 ≤ t by linarith) (by decide : 1 ≤ 4)
  have hp4 : ((d ^ 3 : ℕ) : ℝ) * p ≤ t ^ 4 := by
    rw [Nat.cast_pow]
    calc
      _ ≤ p ^ 3 * p := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg d) hd 3) hp
      _ = p ^ 4 := by ring
      _ ≤ t ^ 4 := pow_le_pow_left₀ hp hpt 4
  have hlog : (K : ℝ) + (d ^ 3 : ℕ) * p + p ≤ t ^ C := by
    calc
      _ ≤ t ^ 4 + t ^ 4 + t ^ 4 := add_le_add (add_le_add (hKt.trans htt) hp4) (hpt.trans htt)
      _ = 3 * t ^ 4 := by ring
      _ ≤ t * t ^ 4 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = t ^ 5 := by ring
      _ ≤ t ^ C := pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  have hK : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
  have hpow : ((H ^ (d ^ 3) : ℕ) : ℝ) ≤ Real.exp ((d ^ 3 : ℕ) * p) := by
    rw [Nat.cast_pow, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg H) hH _
  calc
    _ ≤ Real.exp K * Real.exp ((d ^ 3 : ℕ) * p) * Real.exp p := by
      rw [Nat.cast_mul, Nat.cast_mul]
      exact mul_le_mul (mul_le_mul hK hpow (by positivity) (by positivity)) hl
        (by positivity) (by positivity)
    _ = Real.exp ((K : ℝ) + (d ^ 3 : ℕ) * p + p) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr hlog

theorem exists_integral_grid_subgroup_exp (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ),
      0 < l → (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      ∃ (B : ℕ) (Λ : Subgroup (NilpotentLieBCHGroup L s hnil)),
        0 < B ∧ l ∣ B ∧ (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        Λ ≤ Γ ∧ bchSubgroupCoordinates e Λ = scaledIntegerGrid B := by
  refine ⟨bchIntegralDenominatorBound s + 5, by omega, ?_⟩
  intro ι L _ _ _ e hnil Γ l H p hl hc hinner hp hd hH hlp
  obtain ⟨B, Λ, hB, hdiv, hbound, hΛ, hcoords⟩ := exists_integral_grid_subgroup e hnil Γ l hl hc hinner
  exact ⟨B, Λ, hB, hdiv, (Nat.cast_le.mpr hbound).trans
    (integral_grid_allowance_le_exp _ _ _ _ hp hd hH hlp), hΛ, hcoords⟩

end Erdos3

end

end OAI
