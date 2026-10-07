import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoefficientGridDenominator

namespace OAI

section

namespace Erdos3

open MvPolynomial

theorem exists_rationalPolynomial_of_realCoefficientGrid
    {σ : Type*} (P : MvPolynomial σ ℝ) {q : ℕ} (hq : 0 < q)
    (hP : realPolynomialCoefficientGrid q P) :
    ∃ Q : MvPolynomial σ ℚ,
      MvPolynomial.map (algebraMap ℚ ℝ) Q = P ∧
      (fun α => Q.coeff α) ∈ denominatorGrid q ∧ Q.totalDegree = P.totalDegree := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  obtain ⟨z, hz⟩ := hP
  have hrange : P ∈ (MvPolynomial.map (algebraMap ℚ ℝ)).range := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    obtain ⟨α, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    refine ⟨(z α : ℚ) / (q : ℚ), ?_⟩
    have hα : (z α : ℝ) = (q : ℝ) * P.coeff α := congrFun hz α
    simp only [map_div₀, map_intCast, map_natCast, hα, mul_div_cancel_left₀ _ hq0]
  obtain ⟨Q, hQ⟩ := hrange
  refine ⟨Q, hQ, ?_, ?_⟩
  · apply (realPolynomialCoefficientGrid_ratCast_iff q Q).mp
    rw [hQ]
    exact ⟨z, hz⟩
  · rw [← hQ]
    unfold totalDegree
    rw [MvPolynomial.support_map_of_injective Q (algebraMap ℚ ℝ).injective]

end Erdos3

end

end OAI
