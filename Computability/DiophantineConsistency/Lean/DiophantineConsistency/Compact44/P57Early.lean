import DiophantineConsistency.Compact44.P62Early

/-! # Package 57: the early index congruence from the carrier modulo `U = 4q⁴`

`P62Early.early` with its carrier hypothesis replaced by the residue it is used
for, `(H·k) % U = (H(R+1)) % U`. Package 57's fused norm supplies exactly that:
`U ∣ H(k − R − 1)`, whichever sign the restored first root has. The rest is
`P62Early`: `U ∣ 4XY²`, `gcd(U, H) ∣ 3` (`P62Early.gcd_dvd_three`), and
`3(R+1) < 3q⁴ < U ≤ 3μ`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace P57Early
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ArithmeticGcdNormalization ArithmeticPellRecurrence
open ArithmeticPellCongruences P72Mu P62Early
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem mod_one_add_mul (b K : V) (hb : 1 < b) : (1 + b * K) % b = 1 := by
  rw [mod_add_mul' _ _ (lt_trans (by simp) hb)]; exact mod_eq_self_of_lt hb

theorem early_of_mod (q X Y k R H U a w s τ : V)
    (hq3 : 3 ≤ q) (hw : 0 < w) (hs : 0 < s) (hX : X = w * q) (hYq : Y = s * (q * q * q))
    (hH : H = 4 * a + 3) (ha : a = X * Y + Y) (hU : U = 4 * ((q * q) * (q * q)))
    (hτ : τ * τ = 1 + ((X * Y) * Y) * (((X * Y) * Y) + 1) * k * k)
    (hmodk : (H * k) % U = (H * (R + 1)) % U)
    (hwin : R + 1 < q * (q * (q * q))) :
    ∃ n s' μ : V, 2 * ycoord n (2 * ((X * Y) * Y - 1) + 1) = k ∧
      xcoord n (2 * ((X * Y) * Y - 1) + 1) = τ ∧ n ≤ k ∧
      k = 2 * n + 4 * ((X * Y) * Y) * s' ∧ 0 < μ ∧ R + 1 < μ ∧
      (2 * n) % μ = R + 1 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq3
  have hX0 : 0 < X := by rw [hX]; exact mul_pos hw hq0
  have hY0 : 0 < Y := by rw [hYq]; exact mul_pos hs (mul_pos (mul_pos hq0 hq0) hq0)
  have hQ : 0 < (X * Y) * Y := mul_pos (mul_pos hX0 hY0) hY0
  obtain ⟨n, hnk, hnx, hny⟩ :=
    ArithmeticPellFirstNorm.positive_parameter_solution ((X * Y) * Y) τ k hQ hτ
  have hQ1 : (X * Y) * Y - 1 + 1 = (X * Y) * Y := tsub_add_cancel_of_le (pos_iff_one_le.mp hQ)
  have hB : 2 * ((X * Y) * Y) ∣ 2 * ((X * Y) * Y - 1) + 1 + 1 :=
    ⟨1, by calc 2 * ((X * Y) * Y - 1) + 1 + 1 = 2 * ((X * Y) * Y - 1 + 1) := by ring
      _ = 2 * ((X * Y) * Y) * 1 := by rw [hQ1]; ring⟩
  obtain ⟨_, s', _, hys⟩ := residue_quotients n (2 * ((X * Y) * Y - 1) + 1) (2 * ((X * Y) * Y)) hB
  have hks : k = 2 * n + 4 * ((X * Y) * Y) * s' := by rw [← hny, hys]; ring
  -- the carrier modulo U
  have hU0 : 0 < U := by rw [hU]; exact mul_pos (by norm_num) (mul_pos (mul_pos hq0 hq0) (mul_pos hq0 hq0))
  have e1 : H * k = H * (2 * n) + U * (H * (w * s * s * q * q * q * s')) := by
    rw [hks, hU, hX, hYq]; ring
  have hmodU : (H * (2 * n)) % U = (H * (R + 1)) % U := by
    rw [← hmodk, e1, mod_add_mul' _ _ hU0]
  obtain ⟨g0, μ, hg0, hUμ, hg0H, hμ0, hmod⟩ := gcd_cancel U H (2 * n) (R + 1) hU0 hmodU
  -- g0 divides 3
  have eH : H = 3 + q * q * q * (4 * s * (w * q + 1)) := by rw [hH, ha, hX, hYq]; ring
  have hodd : (3 + q * q * q * (4 * s * (w * q + 1))) % 2 = 1 := by
    have : 3 + q * q * q * (4 * s * (w * q + 1)) = 1 + 2 * (1 + 2 * (q * q * q * s * (w * q + 1))) := by ring
    rw [this]; exact mod_one_add_mul _ _ (by norm_num)
  have hgU : g0 ∣ 4 * ((q * q) * (q * q)) := ⟨μ, by rw [← hU, hUμ]⟩
  have hgH : g0 ∣ 3 + q * q * q * (4 * s * (w * q + 1)) := by rw [← eH]; exact hg0H
  have hg3 : g0 ∣ 3 := gcd_dvd_three q (4 * s * (w * q + 1)) g0 hgU hgH hodd
  have hg0le : g0 ≤ 3 := Arithmetic.le_of_dvd (by norm_num) hg3
  have hU3 : U ≤ 3 * μ := by rw [hUμ]; exact mul_le_mul_of_nonneg_right hg0le (Arithmetic.zero_le _)
  have hRμ : R + 1 < μ := by
    have h1 : 3 * (R + 1) < 3 * (q * (q * (q * q))) := mul_lt_mul_of_pos_left hwin (by norm_num)
    have h2 : 3 * (q * (q * (q * q))) ≤ U := by
      rw [hU]
      calc 3 * (q * (q * (q * q))) ≤ 4 * (q * (q * (q * q))) :=
            mul_le_mul_of_nonneg_right (by norm_num) (Arithmetic.zero_le _)
        _ = 4 * ((q * q) * (q * q)) := by ring
    have h3 : 3 * (R + 1) < 3 * μ := lt_of_lt_of_le h1 (le_trans h2 hU3)
    exact lt_of_mul_lt_mul_left h3 (Arithmetic.zero_le _)
  refine ⟨n, s', μ, hny, hnx, hnk, hks, hμ0, hRμ, ?_⟩
  rw [hmod]
  exact mod_eq_self_of_lt hRμ

end P57Early

#print axioms P57Early.early_of_mod
