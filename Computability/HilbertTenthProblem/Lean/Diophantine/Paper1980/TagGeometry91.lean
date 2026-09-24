import Diophantine.Paper1980.Bootstrap91
import Diophantine.Paper1980.TagRows

/-!
# Radix geometry of the 91-operation tag certificate

`EXPLORATION_COMPILED_INITIAL_TAG_BOUND.md`, §2 (end) and `EXPLORATION_SINGLE_CONTENT_GUARD_TAG.md`,
§3.  After the kernel (`q = 3^e`): `R ∣ q` gives `R = 3^m`, the head equation
`H(R − 1) = q − 1` gives `q = R^t` and `H = heads m t` (the row-head word), the width
`A = R/C` and the transport scale `D = R/k` are powers of three, and the fixed
constants are the expected powers: `k = 3^(β−1)`, `C = 3^γ`, `B = 3^(a−1)`,
`cc = rep(β − 1)`, `jA = rep β · (R/K)`.
-/

namespace Jones1980

open Ternary

/-- The recovered geometry of a solution: the exponents `e, m, t, γ, β, a` with
`q = 3^e = R^t`, `R = 3^m`, `C = 3^γ`, `k = 3^(β−1)`, `B = 3^(a−1)`, the width
`A = 3^(m−γ)`, the scale `D = 3^(m−β+1)`, and `H = heads m t`. -/
structure Geometry91 (T : Tag91) (H R q D Z e m t γ β a : ℕ) : Prop where
  hq : q = 3 ^ e
  hR : R = 3 ^ m
  he : e = m * t
  hm : 1 ≤ m
  ht : 1 ≤ t
  hC : T.C = 3 ^ γ
  hβ : 2 ≤ β
  hk : T.Khalf = 3 ^ (β - 1)
  ha : 2 ≤ a
  hB : T.B = 3 ^ (a - 1)
  hγ : 6 ≤ γ
  hγm : γ ≤ m
  hβm : 3 * β < m
  hH : H = heads m t
  hZ : Z = 3 ^ (m - γ) * H
  hD : D = 3 ^ (m - (β - 1))

section Geometry

variable {T : Tag91} {Ninit Linit : ℕ}
  {Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z : ℕ}
  (hT : T.Ok)
  (hP : Pos91 Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z)
  (hS : Sys91 T Ninit Linit Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z)

include hT hP hS

theorem geometry91 : ∃ e m t γ β a, Geometry91 T H R q D Z e m t γ β a := by
  obtain ⟨e, he1, hqe, -, -, -, -, -, -, -⟩ := mask91 hT hP hS
  -- `R` is a power of three
  have hRq : R ∣ q := ⟨v, hS.E5.symm⟩
  rw [hqe] at hRq
  obtain ⟨m, hme, hRm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hRq
  have hR3 := R_ge91 hT hP hS
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hRm; omega
    · exact h0
  -- the head equation: `q = R^t`, `H = heads m t`
  have hhead : H * (3 ^ m - 1) = 3 ^ e - 1 := by
    have h3 := hS.E3
    have hq1 : 1 ≤ q := hP.q
    have hR1 : 1 ≤ R := hP.R
    rw [← hRm, ← hqe]
    have : H * (R - 1) = R * H - H := by rw [Nat.mul_sub, mul_one, mul_comm]
    rw [this]
    omega
  obtain ⟨t, hte, hHt⟩ := heads_of_head_eq hm1 hhead
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0, mul_zero] at hte; omega
    · exact h0
  -- the fixed constants
  obtain ⟨β, hβ2, hk⟩ := hT.Khalf_pow
  obtain ⟨a, ha2, hB⟩ := hT.B_pow
  obtain ⟨γ, hC⟩ := hT.C_pow
  -- the width `A = R/C` and the scale `D = R/k` are powers of three
  obtain ⟨A, hA0, hRA, hZA, hkD⟩ := width_recovery91 hT hP hS
  have hγm : γ ≤ m := by
    have : 3 ^ γ ≤ 3 ^ m := by
      rw [← hC, ← hRm, hRA]; exact Nat.le_mul_of_pos_right _ hA0
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hAdvd : T.C ∣ R := ⟨A, hRA⟩
  have hA : A = 3 ^ (m - γ) := by
    have h1 : 3 ^ γ * A = 3 ^ γ * 3 ^ (m - γ) := by
      rw [← pow_add, Nat.add_sub_cancel' hγm, ← hRm, ← hC, hRA]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hβm : 3 * β < m := by
    -- `K³ < C ≤ R`, so `3^(3β) < 3^m`
    have h3 : (3 * T.Khalf) ^ 3 < R := lt_of_lt_of_le hT.C_gt_K3 (C_le_R91 hT hP hS)
    have h4 : (3 * T.Khalf) ^ 3 = 3 ^ (3 * β) := by
      rw [hk, ← pow_succ', Nat.sub_add_cancel (by omega), ← pow_mul]; ring_nf
    rw [h4, hRm] at h3
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h3
  have hγ6 : 6 ≤ γ := by
    -- `C > K³ ≥ 3^6`
    have h3 : (3 * T.Khalf) ^ 3 < T.C := hT.C_gt_K3
    have h4 : 3 ^ 6 ≤ (3 * T.Khalf) ^ 3 := by
      have : 9 ≤ 3 * T.Khalf := by have := three_le_Khalf hT; omega
      calc 3 ^ 6 = 9 ^ 3 := by norm_num
        _ ≤ (3 * T.Khalf) ^ 3 := Nat.pow_le_pow_left this 3
    rw [hC] at h3
    have : 3 ^ 6 < 3 ^ γ := lt_of_le_of_lt h4 h3
    exact ((Nat.pow_lt_pow_iff_right (by norm_num)).1 this).le
  have hD : D = 3 ^ (m - (β - 1)) := by
    have h1 : 3 ^ (β - 1) * D = 3 ^ (β - 1) * 3 ^ (m - (β - 1)) := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega), ← hRm, ← hk, hS.E0]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  exact ⟨e, m, t, γ, β, a, hqe, hRm, hte, hm1, ht1, hC, hβ2, hk, ha2, hB, hγ6, hγm, hβm, hHt,
    by rw [hZA, hA], hD⟩

end Geometry

end Jones1980
