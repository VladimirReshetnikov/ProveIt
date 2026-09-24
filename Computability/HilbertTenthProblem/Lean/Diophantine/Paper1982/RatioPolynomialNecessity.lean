import Diophantine.Paper1982.RatioPolynomialDefs

/-!
# Positive witnesses for the polynomial ratio subsystem of Theorem 3

The witnesses of Lemma 2.25 supply the ratio equations, and Corollary 2.29
replaces the remaining Pell sequence by three polynomial equations.
The strict approximation inequality supplies a positive slack `η`.
The positive quotient theorem supplies `γ > 0` in the first-coordinate
congruence; congruence alone would only give an integer quotient.
-/

namespace Jones1982

open Pell Diophantine JSWW1976 Jones1978

/-- Necessity for the last ten polynomial equations of Theorem 3, with all
sixteen auxiliary witnesses strictly positive. -/
theorem exists_ratioPolynomial {R N b : ℕ}
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b) (hbN : b ≤ N)
    (hdvd : N ^ 2 ∣ (2 * R).choose R) (hpow : ∃ v, b = 2 ^ v) :
    ∃ a c d f h i j k o p s w γ η τ φ : ℕ,
      0 < a ∧ 0 < c ∧ 0 < d ∧ 0 < f ∧ 0 < h ∧ 0 < i ∧ 0 < j ∧ 0 < k ∧
      0 < o ∧ 0 < p ∧ 0 < s ∧ 0 < w ∧ 0 < γ ∧ 0 < η ∧ 0 < τ ∧ 0 < φ ∧
      RatioPolynomial R N b a c d f h i j k o p s w γ η τ φ := by
  obtain ⟨h, s, w, φ, A, B', C, K, M, P, U, V, W, Y,
    hh, hs, hw, hφ, hB, hW, -⟩ := exists_B25core hR hN hbR hb hbN hdvd hpow
  obtain ⟨hU, -, hM, hAbig, hA, -, hB'C, -, -, -⟩ := hB.sizes hR hN hs hw
  have hP : 0 < P := by rw [hB.B1]; positivity
  have hK : 0 < K := by have := hB.B4; omega
  have hC : 0 < C := by have := hB.B7; omega
  have hB' : 1 < B' := by rw [hB.B7]; omega
  have hB'odd : Odd B' := by rw [hB.B7]; exact ⟨R, by ring⟩
  obtain ⟨D, F, i, j, o, hD, hF, hi, hj, ho, hQ⟩ :=
    (corollary_2_29 hA hB' hB'C (Or.inr hB'odd)).1 (hB.B14 hA)
  have hCψ : C = ψ hA (2 * R + 1) := by rw [hB.B14 hA, hB.B7]
  obtain ⟨n, hDn, hCn⟩ := eq_pell_of_sq hA hQ.Q1
  have hn : n = 2 * R + 1 := (strictMono_y hA).injective (by rw [← hCn, hCψ])
  have hDχ : D = χ hA (2 * R + 1) := by simpa only [hn] using hDn
  obtain ⟨γ, hγ, hγeq⟩ :=
    exists_positive_pell_quotient_int hA (by omega) (by omega : 2 ≤ 2 * R + 1)
  rw [← hDχ, ← hCψ] at hγeq
  have hbw : b * w = 2 ^ (2 * R + 1) := hB.B11.symm.trans hW
  have hbwZ : (b : ℤ) * w = 2 ^ (2 * R + 1) := by exact_mod_cast hbw
  rw [← hbwZ] at hγeq
  -- The positive square root in the Pell equation for `P` and `K`.
  obtain ⟨τ, hτeq⟩ := hB.B2
  have hτ : 0 < τ := by
    by_contra hn
    have : τ = 0 := by omega
    rw [this] at hτeq
    omega
  -- The positive slack converting the strict approximation into an equation.
  have hclose : 4 * ((C : ℤ) - K * s * N ^ 2) ^ 2 < (K : ℤ) ^ 2 := by
    have hclose := hB.B3
    rw [hB.B10] at hclose
    push_cast at hclose
    have he : (C : ℤ) - K * ((N : ℤ) ^ 2 * s) = C - K * s * N ^ 2 := by ring
    rwa [he] at hclose
  let η : ℕ := ((K : ℤ) ^ 2 - 4 * ((C : ℤ) - K * s * N ^ 2) ^ 2).toNat
  have hηeq : (η : ℤ) = (K : ℤ) ^ 2 - 4 * ((C : ℤ) - K * s * N ^ 2) ^ 2 :=
    Int.toNat_of_nonneg (by omega)
  have hη : 0 < η := by
    exact_mod_cast (show (0 : ℤ) < η by omega)
  refine ⟨A, C, D, F, h, i, j, K, o, P, s, w, γ, η, τ, φ,
    by omega, hC, hD, hF, hh, hi, hj, hK, ho, hP, hs, hw, hγ, hη, hτ, hφ, ?_⟩
  have hA2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hA.le
  have hP2 : 1 ≤ P ^ 2 := Nat.one_le_pow _ _ hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hB.B1, hB.B5, hB.B10, hB.B9]
    ring
  · have ht := congrArg (fun n : ℕ => (n : ℤ)) hτeq
    push_cast [Nat.cast_sub hP2] at ht
    linear_combination ht
  · omega
  · have hKdef := congrArg (fun n : ℕ => (n : ℤ)) hB.B4
    push_cast [Nat.cast_sub hP] at hKdef
    linear_combination hKdef
  · rw [hB.B6, hB.B5, hB.B10, hB.B9]
    ring
  · rw [hB.B8, hB.B7]
  · linear_combination hγeq
  · have hDsq := congrArg (fun n : ℕ => (n : ℤ)) hQ.Q1
    push_cast [Nat.cast_sub hA2] at hDsq
    exact hDsq
  · have hFsq := congrArg (fun n : ℕ => (n : ℤ)) hQ.Q2
    push_cast [Nat.cast_sub hA2] at hFsq
    exact hFsq
  · have hDF := hQ.Q3
    rw [hB.B7] at hDF
    push_cast at hDF
    exact hDF

end Jones1982
