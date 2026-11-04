import DiophantineConsistency.Compact44.P72Window
import DiophantineConsistency.ArithmeticPellFirstNorm
import DiophantineConsistency.ArithmeticPellClassification
import DiophantineConsistency.ArithmeticPellCongruences

/-! # P13, section 6: the early index congruence

This module works with abstract natural data that satisfy P13's §4–§6
relations. Then:

* the first norm `τ² = 1 + Q(Q+1)k²`, with `Q = XY²`, gives an index `n` with
  `2ψ(n) = k`, and so `k = 2n + 4Q·s`;
* the main carrier, reduced modulo `S = 4qY`, gives
  `(H·2n) % S = (H(R+1)) % S`;
* the gcd cancellation gives `μ ∣ S` with `S ≤ 3μ`, hence `R + 1 < μ` and
  `(2n) % μ = R + 1`.

In particular `2n ≥ R + 1`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace P72Early
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ArithmeticGcdNormalization ArithmeticPellRecurrence
open ArithmeticPellCongruences P72Mu
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem early (q X Y k R H M S g c a γ t y τ : V)
    (hq3 : 3 ≤ q) (hX : 0 < X) (hy0 : 0 < y) (hYq : Y = q * (q * q) * y)
    (hH : H = 3 + 4 * a) (ha : a = X * Y + Y)
    (hS : S = 4 * (Y * q)) (hM : M = S * q)
    (hτ : τ * τ = 1 + ((X * Y) * Y) * (((X * Y) * Y) + 1) * k * k)
    (hcar : M * g + H * k = M * (X + a * c) + H * (M * γ + S * X + R + 1))
    (hqt : q = 3 * t + 2)
    (hwin : R + 1 < q * (q * (q * q))) :
    ∃ n s μ : V, 2 * ycoord n (2 * ((X * Y) * Y - 1) + 1) = k ∧
      xcoord n (2 * ((X * Y) * Y - 1) + 1) = τ ∧ n ≤ k ∧
      k = 2 * n + 4 * ((X * Y) * Y) * s ∧ 0 < μ ∧ μ ∣ S ∧ R + 1 < μ ∧
      (2 * n) % μ = R + 1 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq3
  have hY0 : 0 < Y := by rw [hYq]; exact mul_pos (mul_pos hq0 (mul_pos hq0 hq0)) hy0
  have hQ : 0 < (X * Y) * Y := mul_pos (mul_pos hX hY0) hY0
  obtain ⟨n, hnk, hnx, hny⟩ :=
    ArithmeticPellFirstNorm.positive_parameter_solution ((X * Y) * Y) τ k hQ hτ
  -- k = 2n + 4Qs
  have hQ1 : (X * Y) * Y - 1 + 1 = (X * Y) * Y := tsub_add_cancel_of_le (pos_iff_one_le.mp hQ)
  have hB : 2 * ((X * Y) * Y) ∣ 2 * ((X * Y) * Y - 1) + 1 + 1 :=
    ⟨1, by calc 2 * ((X * Y) * Y - 1) + 1 + 1 = 2 * ((X * Y) * Y - 1 + 1) := by ring
      _ = 2 * ((X * Y) * Y) * 1 := by rw [hQ1]; ring⟩
  obtain ⟨_, s, _, hys⟩ := residue_quotients n (2 * ((X * Y) * Y - 1) + 1) (2 * ((X * Y) * Y)) hB
  have hks : k = 2 * n + 4 * ((X * Y) * Y) * s := by rw [← hny, hys]; ring
  -- the carrier modulo S
  have hS0 : 0 < S := by rw [hS]; exact mul_pos (by norm_num) (mul_pos hY0 hq0)
  have e1 : M * g + H * k = H * (2 * n) + S * (q * g + H * (X * (q * q * y) * s)) := by
    rw [hks, hM, hS, hYq]; ring
  have e2 : M * (X + a * c) + H * (M * γ + S * X + R + 1) =
      H * (R + 1) + S * (q * (X + a * c) + H * (q * γ + X)) := by
    rw [hM]; ring
  have hmodS : (H * (2 * n)) % S = (H * (R + 1)) % S := by
    have h : (M * g + H * k) % S = (M * (X + a * c) + H * (M * γ + S * X + R + 1)) % S :=
      congrArg (fun z : V => z % S) hcar
    rwa [e1, e2, mod_add_mul' _ _ hS0, mod_add_mul' _ _ hS0] at h
  obtain ⟨g0, μ, hg0, hSμ, hg0H, hμ0, hmod⟩ := gcd_cancel S H (2 * n) (R + 1) hS0 hmodS
  -- g0 divides 3
  have hbez0 := bez_q_H q t (4 * (q * q * y * (X + 1))) hqt
  have hbez : Bez q (3 + 4 * (X * Y + Y)) 1 := by
    have e : q * (4 * (q * q * y * (X + 1))) + 3 = 3 + 4 * (X * Y + Y) := by rw [hYq]; ring
    rwa [e] at hbez0
  have hgS : g0 ∣ 4 * (Y * q) := ⟨μ, by rw [← hS, hSμ]⟩
  have hgH : g0 ∣ 3 + 4 * (X * Y + Y) := by rw [← ha, ← hH]; exact hg0H
  have hg3 : g0 ∣ 3 := gcd_dvd_three q X Y g0 hbez hgS hgH
  have hg0le : g0 ≤ 3 := Arithmetic.le_of_dvd (by norm_num) hg3
  have hS3 : S ≤ 3 * μ := by rw [hSμ]; exact mul_le_mul_of_nonneg_right hg0le (Arithmetic.zero_le _)
  -- R + 1 < μ
  have hq4 : 4 * (q * (q * (q * q))) ≤ S := by
    rw [hS, hYq]
    have : q * (q * (q * q)) ≤ q * (q * q) * y * q := by
      calc q * (q * (q * q)) = q * (q * q) * 1 * q := by ring
        _ ≤ q * (q * q) * y * q := by
          apply mul_le_mul_of_nonneg_right _ (Arithmetic.zero_le _)
          exact mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hy0) (Arithmetic.zero_le _)
    calc 4 * (q * (q * (q * q))) ≤ 4 * (q * (q * q) * y * q) :=
          mul_le_mul_of_nonneg_left this (Arithmetic.zero_le _)
      _ = 4 * (q * (q * q) * y * q) := rfl
  have hRμ : R + 1 < μ := by
    have h1 : 3 * (R + 1) < 3 * (q * (q * (q * q))) := mul_lt_mul_of_pos_left hwin (by norm_num)
    have h2 : 3 * (q * (q * (q * q))) ≤ 4 * (q * (q * (q * q))) :=
      mul_le_mul_of_nonneg_right (by norm_num) (Arithmetic.zero_le _)
    have h3 : 3 * (R + 1) < 3 * μ := lt_of_lt_of_le h1 (le_trans h2 (le_trans hq4 hS3))
    exact lt_of_mul_lt_mul_left h3 (Arithmetic.zero_le _)
  refine ⟨n, s, μ, hny, hnx, hnk, hks, hμ0, ⟨g0, by rw [hSμ]; ring⟩, hRμ, ?_⟩
  rw [hmod]
  exact mod_eq_self_of_lt hRμ

end P72Early

#print axioms P72Early.early
