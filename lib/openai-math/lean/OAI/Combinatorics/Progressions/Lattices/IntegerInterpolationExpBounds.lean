import OAI.Combinatorics.Progressions.Polynomial.IntegerPolynomialInterpolation

namespace OAI

section

namespace Erdos3

theorem constantIntegerInterpolation_power_bounds {X ρ : ℝ}
    (hX : 8 ≤ X) (hA : (probabilityProfileLipschitz : ℝ) ≤ X)
    (hρ : 0 < ρ) (hρX : ρ⁻¹ ≤ X) :
    constantIntegerInterpolationCap ρ ≤ X^3 ∧ constantIntegerInterpolationLip ρ ≤ X^7 := by
  have hX0 : 0 ≤ X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have h2 : (2 : ℝ) ≤ X := by linarith
  have hc : constantIntegerInterpolationCap ρ ≤ X^3 := by
    unfold constantIntegerInterpolationCap
    rw [div_eq_mul_inv]
    calc
      _ ≤ X * X * X := by gcongr
      _ = _ := by ring
  refine ⟨hc, ?_⟩
  unfold constantIntegerInterpolationLip
  apply max_le
  · have ht : 2 * (probabilityProfileLipschitz : ℝ) / ρ^2 ≤ X^4 := by
      rw [div_eq_mul_inv, ← inv_pow]
      calc
        _ ≤ X * X * X^2 := by gcongr
        _ = _ := by ring
    exact ht.trans (pow_le_pow_right₀ hX1 (by norm_num))
  · have hc0 : 0 ≤ constantIntegerInterpolationCap ρ := by
      unfold constantIntegerInterpolationCap
      positivity
    calc
      _ ≤ X * (X^3)^2 := by gcongr
      _ = _ := by ring

theorem principalAxisInterpolation_power_bounds (h L : ℕ) {X γ : ℝ}
    (hX : 8 ≤ X) (hA : (probabilityProfileLipschitz : ℝ) ≤ X)
    (hγ : 0 < γ) (hγX : γ⁻¹ ≤ X) (hL : (L : ℝ)^h ≤ X) :
    principalAxisInterpolationCap h L γ ≤ X^3 ∧ principalAxisInterpolationLip h L γ ≤ X^7 := by
  have hX0 : 0 ≤ X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have h2 : (2 : ℝ) ≤ X := by linarith
  have h4 : (4 : ℝ) ≤ X := by linarith
  have hX3 : X ≤ X^3 := by simpa only [pow_one] using (pow_le_pow_right₀ hX1 (show 1 ≤ 3 by norm_num))
  constructor
  · unfold principalAxisInterpolationCap
    apply max_le
    · rw [div_eq_mul_inv]
      calc
        _ ≤ X * X * X := by gcongr
        _ = _ := by ring
    · exact hL.trans hX3
  · unfold principalAxisInterpolationLip
    apply max_le
    · have ht : 8 * (probabilityProfileLipschitz : ℝ) * ((L : ℝ)^h)^2 / γ^2 ≤ X^6 := by
        rw [div_eq_mul_inv, ← inv_pow]
        calc
          _ ≤ X * X * X^2 * X^2 := by gcongr
          _ = _ := by ring
      exact ht.trans (pow_le_pow_right₀ hX1 (by norm_num))
    · have ht : 2 * ((L : ℝ)^h)^2 ≤ X^3 := by
        calc
          _ ≤ X * X^2 := by gcongr
          _ = _ := by ring
      exact ht.trans (pow_le_pow_right₀ hX1 (by norm_num))

theorem tailAxisInterpolation_power_bounds (L s : ℕ) {X ε : ℝ}
    (hX : 8 ≤ X) (hA : (probabilityProfileLipschitz : ℝ) ≤ X)
    (hε : 0 < ε) (hεX : ε⁻¹ ≤ X) (hL : (L : ℝ)^s ≤ X) (hL1 : (L : ℝ)^(s+1) ≤ X) :
    tailAxisInterpolationCap L s ε ≤ X^3 ∧ tailAxisInterpolationLip L s ε ≤ X^7 := by
  have hX0 : 0 ≤ X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have h2 : (2 : ℝ) ≤ X := by linarith
  have hX3 : X ≤ X^3 := by simpa only [pow_one] using (pow_le_pow_right₀ hX1 (show 1 ≤ 3 by norm_num))
  constructor
  · unfold tailAxisInterpolationCap
    apply max_le
    · rw [div_eq_mul_inv]
      calc
        _ ≤ X * X * X := by gcongr
        _ = _ := by ring
    · exact hL1.trans hX3
  · unfold tailAxisInterpolationLip
    apply max_le
    · have ht : 2 * (probabilityProfileLipschitz : ℝ) * ((L : ℝ)^s)^2 / ε^2 ≤ X^6 := by
        rw [div_eq_mul_inv, ← inv_pow]
        calc
          _ ≤ X * X * X^2 * X^2 := by gcongr
          _ = _ := by ring
      exact ht.trans (pow_le_pow_right₀ hX1 (by norm_num))
    · have ht : 2 * ((L : ℝ)^(s+1))^2 ≤ X^3 := by
        calc
          _ ≤ X * X^2 := by gcongr
          _ = _ := by ring
      exact ht.trans (pow_le_pow_right₀ hX1 (by norm_num))

theorem integerPolynomialInterpolation_power_bounds (h L s : ℕ) {X ρ γ ε : ℝ}
    (hX : 8 ≤ X) (hA : (probabilityProfileLipschitz : ℝ) ≤ X)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
    (hρX : ρ⁻¹ ≤ X) (hγX : γ⁻¹ ≤ X) (hεX : ε⁻¹ ≤ X)
    (hLh : (L : ℝ)^h ≤ X) (hLs : (L : ℝ)^s ≤ X) (hLs1 : (L : ℝ)^(s+1) ≤ X) :
    integerPolynomialInterpolationCap h L s ρ γ ε ≤ X^3 ∧
      integerPolynomialInterpolationLip h L s ρ γ ε ≤ X^7 := by
  obtain ⟨hc, hl⟩ := constantIntegerInterpolation_power_bounds hX hA hρ hρX
  obtain ⟨pc, pl⟩ := principalAxisInterpolation_power_bounds h L hX hA hγ hγX hLh
  obtain ⟨tc, tl⟩ := tailAxisInterpolation_power_bounds L s hX hA hε hεX hLs hLs1
  exact ⟨max_le hc (max_le pc tc), max_le hl (max_le pl tl)⟩

end Erdos3

end

section

namespace Erdos3

def integerInterpolationLogEnvelope (m : ℕ) (P : ℝ) : ℝ := ((m : ℝ) + 1) * P + 8

theorem integerPolynomialInterpolation_exp_bounds (m h L s : ℕ)
    (hh : h ≤ m) (hs : s ≤ m) {P ρ γ ε : ℝ} (hP : 0 ≤ P)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hL : (L : ℝ) ≤ Real.exp P)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
    (hρP : ρ⁻¹ ≤ Real.exp P) (hγP : γ⁻¹ ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    integerPolynomialInterpolationCap h L s ρ γ ε ≤
        Real.exp (3 * integerInterpolationLogEnvelope m P) ∧
      integerPolynomialInterpolationLip h L s ρ γ ε ≤
        Real.exp (7 * integerInterpolationLogEnvelope m P) := by
  let Q := integerInterpolationLogEnvelope m P
  let X := Real.exp Q
  have hm0 := Nat.cast_nonneg (α := ℝ) m
  have hPQ : P ≤ Q := by dsimp [Q, integerInterpolationLogEnvelope]; nlinarith
  have hQ8 : 8 ≤ Q := by dsimp [Q, integerInterpolationLogEnvelope]; nlinarith
  have hX : 8 ≤ X := by dsimp [X]; linarith [Real.add_one_le_exp Q]
  have hPX : Real.exp P ≤ X := Real.exp_le_exp.mpr hPQ
  have hp (k : ℕ) (hk : k ≤ m + 1) : (L : ℝ)^k ≤ X := by
    calc
      _ ≤ (Real.exp P)^k := pow_le_pow_left₀ (Nat.cast_nonneg _) hL _
      _ = Real.exp ((k : ℝ) * P) := (Real.exp_nat_mul P k).symm
      _ ≤ X := by
        apply Real.exp_le_exp.mpr
        have hkr : (k : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hk
        have hmul := mul_le_mul_of_nonneg_right hkr hP
        dsimp [Q, integerInterpolationLogEnvelope]
        linarith
  have h := integerPolynomialInterpolation_power_bounds h L s hX (hA.trans hPX) hρ hγ hε
    (hρP.trans hPX) (hγP.trans hPX) (hεP.trans hPX) (hp h (by omega)) (hp s (by omega)) (hp (s+1) (by omega))
  simpa only [X, ← Real.exp_nat_mul, Nat.cast_ofNat, Q] using h

end Erdos3

end

end OAI
