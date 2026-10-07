import OAI.Combinatorics.Progressions.Polynomial.PolynomialRationalApproximationMono

namespace OAI

section

namespace Erdos3

theorem PolynomialRationalApproximation.nat_smul {I : Type*} {T : I → ℝ} {R : ℝ}
    {P : MvPolynomial I ℝ} (h : PolynomialRationalApproximation T R P)
    (q : ℕ) (hq : 0 < q) :
    PolynomialRationalApproximation T ((q : ℝ) * R) ((q : ℝ) • P) := by
  obtain ⟨D, hD, hDR, Q, hQ⟩ := h
  have hR : 0 ≤ R := (Nat.cast_nonneg D).trans hDR
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨D, hD, hDR.trans (by nlinarith), (q : ℤ) • Q, ?_⟩
  intro α
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
  calc
    |(q : ℝ) * P.coeff α - ((q : ℝ) * ((Q.coeff α : ℤ) : ℝ)) / D| =
        (q : ℝ) * |P.coeff α - ((Q.coeff α : ℤ) : ℝ) / D| := by
      rw [mul_div_assoc, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg q)]
    _ ≤ (q : ℝ) * (R / monomialScale T α) :=
      mul_le_mul_of_nonneg_left (hQ α) (Nat.cast_nonneg q)
    _ = ((q : ℝ) * R) / monomialScale T α := by ring

end Erdos3

end

end OAI
