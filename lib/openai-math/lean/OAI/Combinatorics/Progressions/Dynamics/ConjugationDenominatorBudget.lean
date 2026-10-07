import OAI.Combinatorics.Progressions.Geometry.ConjugationCoordinates

namespace OAI

section

namespace Erdos3

open Module

theorem exists_conjugation_denominator_exp_bound (s : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) : ℝ) ≤
        Real.exp ((p + K) ^ K) := by
  obtain ⟨C, hC, hcoeff⟩ := exists_bchProductCoordinatePolynomial_exp_budget s
  let K := C + 3 * s + 10
  refine ⟨K, by dsimp [K]; omega, ?_⟩
  intro ι L _ _ _ e H p hp hd hH hc
  let t := p + K
  have hK : (s : ℝ) + 3 ≤ K := by exact_mod_cast (show s + 3 ≤ K by dsimp [K]; omega)
  have ht : 3 ≤ t := by dsimp [t]; linarith
  have hpt : p + 3 ≤ t := by dsimp [t]; linarith
  have hs : (s : ℝ) + 1 ≤ t := by dsimp [t]; linarith
  have hshift : p + 3 + C ≤ t := by
    have h : C + 3 ≤ K := by dsimp [K]; omega
    have h' : (C : ℝ) + 3 ≤ K := by exact_mod_cast h
    dsimp [t]
    linarith
  have hcoeff' : ∀ i m, (((conjugationCoordinatePolynomial e s i).coeff m).den : ℝ) ≤
      Real.exp (t ^ C) := by
    intro i m
    have h := (hcoeff (lieStructureConstants e) H (p + 3) ([0, 1, 2] : List (Fin 3))
      (by positivity) (by linarith) (by simp; linarith) (by simp; linarith)
      (hH.trans (Real.exp_le_exp.mpr (by linarith))) hc i m).2
    exact h.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) hshift C))
  have hcard : ∀ i, ((conjugationCoordinatePolynomial e s i).support.card : ℝ) ≤ t ^ (2 * s + 1) := by
    intro i
    have h := (Nat.cast_le (α := ℝ)).mpr
      (bchProductCoordinatePolynomial_support_card (lieStructureConstants e) s ([0, 1, 2] : List (Fin 3)) i)
    simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h
    have hb : 3 * (Fintype.card ι : ℝ) + 1 ≤ t ^ 2 := by nlinarith [sq_nonneg p]
    apply h.trans
    calc
      _ ≤ t * (t ^ 2) ^ s := mul_le_mul hs (pow_le_pow_left₀ (by positivity) hb s) (by positivity) (by linarith)
      _ = t ^ (2 * s + 1) := by rw [← pow_mul, pow_succ']
  have hD := polynomialFamilyDenominator_exp_bound (conjugationCoordinatePolynomial e s)
    (p := t - 2) (by linarith) C 1 (2 * s + 1)
    (by simpa only [sub_add_cancel] using hcoeff')
    (by simpa only [sub_add_cancel] using hcard)
    (by rw [sub_add_cancel, pow_one]; linarith)
  rw [sub_add_cancel] at hD
  apply hD.trans
  exact Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith) (by dsimp [K]; omega))

end Erdos3

end

end OAI
