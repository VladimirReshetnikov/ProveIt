import DiophantineConsistency.Compact44.P72Early

/-! # Package 64: the early index congruence for the modulus `U = Y²`

This module works with abstract natural data satisfying package 64's
relations, as `P72Early` does for P13's modulus `S = 4qY`:

* the first norm `τ² = 1 + Q(Q+1)k²`, with `Q = XY²`, gives an index `n` with
  `2ψ(n) = k`, and so `k = 2n + 4Q·s`. Since `U ∣ 4Q`, this is `2n` modulo `U`;
* the main carrier, reduced modulo `U`, gives `(H·2n) % U = (H(R+1)) % U`;
* `gcd(U, H) ∣ 9`, because `H = 4(X+1)Y + 3` gives
  `H² + 16(X+1)²Y² = 9 + 8(X+1)Y·H`;
* so `U ≤ 9μ` for `μ = U / gcd(U, H)`. With `Y ≥ q³` and `q ≥ 3`, this gives
  `9(R+1) < 9q⁴ ≤ q⁶ ≤ U ≤ 9μ`, hence `(2n) % μ = R + 1`.

No index quotient or coprimality of `q` and `H` is needed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace P64Early
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ArithmeticGcdNormalization ArithmeticPellRecurrence
open ArithmeticPellCongruences P72Mu
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A common divisor of `Y²` and `H = 4(XY+Y)+3` divides `9`. -/
theorem gcd_dvd_nine (X Y g0 : V) (hgY : g0 ∣ Y * Y) (hgH : g0 ∣ 3 + 4 * (X * Y + Y)) : g0 ∣ 9 := by
  set H : V := 3 + 4 * (X * Y + Y) with hH
  obtain ⟨μ, hμ⟩ := hgY
  obtain ⟨h', hh'⟩ := hgH
  rcases (Arithmetic.zero_le g0).lt_or_eq with hg0 | hg0
  · have e : H * H + 16 * ((X + 1) * (X + 1)) * (Y * Y) = 9 + 8 * (X + 1) * Y * H := by
      rw [hH]; ring
    have e1 : H * H + 16 * ((X + 1) * (X + 1)) * (Y * Y) = g0 * (h' * H + 16 * ((X + 1) * (X + 1)) * μ) := by
      rw [hμ]; nth_rewrite 1 [hh']; ring
    have e2 : 9 + 8 * (X + 1) * Y * H = 9 + g0 * (8 * (X + 1) * Y * h') := by
      rw [hh']; ring
    have hm : (9 : V) % g0 = 0 := by
      have h := congrArg (fun t : V => t % g0) (e1.symm.trans (e.trans e2))
      rw [mod_add_mul' _ _ hg0] at h
      rw [← h]; exact mod_eq_zero_iff_dvd.mpr ⟨_, rfl⟩
    exact mod_eq_zero_iff_dvd.mp hm
  · exfalso
    rw [← hg0, zero_mul] at hh'
    rw [hH] at hh'
    exact absurd hh' (ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num) (Arithmetic.zero_le _)))

theorem early (q X Y k R H U g c a γ y τ : V)
    (hq3 : 3 ≤ q) (hX : 0 < X) (hy0 : 0 < y) (hYq : Y = q * (q * q) * y)
    (hH : H = 3 + 4 * a) (ha : a = X * Y + Y) (hU : U = Y * Y)
    (hτ : τ * τ = 1 + ((X * Y) * Y) * (((X * Y) * Y) + 1) * k * k)
    (hcar : U * g + H * k = U * (X + a * c) + H * (U * γ + R + 1))
    (hwin : R + 1 < q * (q * (q * q))) :
    ∃ n s μ : V, 2 * ycoord n (2 * ((X * Y) * Y - 1) + 1) = k ∧
      xcoord n (2 * ((X * Y) * Y - 1) + 1) = τ ∧ n ≤ k ∧
      k = 2 * n + 4 * ((X * Y) * Y) * s ∧ 0 < μ ∧ R + 1 < μ ∧
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
  -- the carrier modulo U
  have hU0 : 0 < U := by rw [hU]; exact mul_pos hY0 hY0
  have e1 : U * g + H * k = H * (2 * n) + U * (g + H * (4 * X * s)) := by
    rw [hks, hU]; ring
  have e2 : U * (X + a * c) + H * (U * γ + R + 1) = H * (R + 1) + U * ((X + a * c) + H * γ) := by
    ring
  have hmodU : (H * (2 * n)) % U = (H * (R + 1)) % U := by
    have h : (U * g + H * k) % U = (U * (X + a * c) + H * (U * γ + R + 1)) % U :=
      congrArg (fun z : V => z % U) hcar
    rwa [e1, e2, mod_add_mul' _ _ hU0, mod_add_mul' _ _ hU0] at h
  obtain ⟨g0, μ, hg0, hUμ, hg0H, hμ0, hmod⟩ := gcd_cancel U H (2 * n) (R + 1) hU0 hmodU
  -- g0 divides 9
  have hgY : g0 ∣ Y * Y := ⟨μ, by rw [← hU, hUμ]⟩
  have hgH : g0 ∣ 3 + 4 * (X * Y + Y) := by rw [← ha, ← hH]; exact hg0H
  have hg9 : g0 ∣ 9 := gcd_dvd_nine X Y g0 hgY hgH
  have hg0le : g0 ≤ 9 := Arithmetic.le_of_dvd (by norm_num) hg9
  have hU9 : U ≤ 9 * μ := by rw [hUμ]; exact mul_le_mul_of_nonneg_right hg0le (Arithmetic.zero_le _)
  -- R + 1 < μ
  have hq6 : 9 * (q * (q * (q * q))) ≤ U := by
    have hqq : 9 ≤ q * q := by
      calc (9 : V) = 3 * 3 := by norm_num
        _ ≤ q * q := mul_le_mul hq3 hq3 (by norm_num) (Arithmetic.zero_le _)
    have hY3 : q * (q * q) ≤ Y := by
      rw [hYq]; exact le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp hy0)
    calc 9 * (q * (q * (q * q))) ≤ (q * q) * (q * (q * (q * q))) :=
          mul_le_mul_of_nonneg_right hqq (Arithmetic.zero_le _)
      _ = (q * (q * q)) * (q * (q * q)) := by ring
      _ ≤ Y * Y := mul_le_mul hY3 hY3 (Arithmetic.zero_le _) (Arithmetic.zero_le _)
      _ = U := hU.symm
  have hRμ : R + 1 < μ := by
    have h1 : 9 * (R + 1) < 9 * (q * (q * (q * q))) := mul_lt_mul_of_pos_left hwin (by norm_num)
    have h3 : 9 * (R + 1) < 9 * μ := lt_of_lt_of_le h1 (le_trans hq6 hU9)
    exact lt_of_mul_lt_mul_left h3 (Arithmetic.zero_le _)
  refine ⟨n, s, μ, hny, hnx, hnk, hks, hμ0, hRμ, ?_⟩
  rw [hmod]
  exact mod_eq_self_of_lt hRμ

end P64Early

#print axioms P64Early.gcd_dvd_nine
#print axioms P64Early.early
