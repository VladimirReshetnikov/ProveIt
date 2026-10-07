import OAI.Combinatorics.Progressions.Polynomial.PolynomialIntegerInputs

namespace OAI

section

namespace Erdos3

open MvPolynomial

theorem polynomial_rational_value_denominator {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℚ) (q s : ℕ) (hdegree : P.totalDegree ≤ s)
    (x : σ → ℚ) (hx : x ∈ denominatorGrid q) :
    ∃ a : ℤ, ((polynomialDenominator P * q ^ s : ℕ) : ℚ) * eval x P = (a : ℚ) := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨eval z (integralNumeratorPolynomial P q s), ?_⟩
  have h := integralNumeratorPolynomial_eval P q s hdegree x z hz
  simpa only [Nat.cast_mul, Nat.cast_pow] using h.symm

theorem polynomial_family_rational_values_grid {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℚ) (q s : ℕ) (hdegree : ∀ i, (P i).totalDegree ≤ s)
    (x : σ → ℚ) (hx : x ∈ denominatorGrid q) :
    (fun i => eval x (P i)) ∈ denominatorGrid (polynomialFamilyDenominator P * q ^ s) := by
  classical
  have h (i : ι) : ∃ a : ℤ,
      ((polynomialFamilyDenominator P * q ^ s : ℕ) : ℚ) * eval x (P i) = (a : ℚ) := by
    obtain ⟨k, hk⟩ := polynomialDenominator_dvd_family P i
    obtain ⟨a, ha⟩ := polynomial_rational_value_denominator (P i) q s (hdegree i) x hx
    refine ⟨(k : ℤ) * a, ?_⟩
    simp only [Nat.cast_mul, Nat.cast_pow] at ha
    rw [hk]
    simp only [Nat.cast_mul, Nat.cast_pow, Int.cast_mul, Int.cast_natCast]
    calc
      _ = (k : ℚ) * ((polynomialDenominator (P i) : ℚ) * (q : ℚ) ^ s * eval x (P i)) := by ring
      _ = _ := by rw [ha]
  choose a ha using h
  exact ⟨a, ha⟩

theorem pairInput_mem_denominatorGrid {ι : Type*} (a b : ι → ℚ) (q : ℕ)
    (ha : a ∈ denominatorGrid q) (hb : b ∈ denominatorGrid q) :
    (fun xi : Fin 2 × ι => (![a, b] xi.1) xi.2) ∈ denominatorGrid q := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  refine ⟨fun xi => (![u, v] xi.1) xi.2, ?_⟩
  rintro ⟨i, j⟩
  fin_cases i
  · exact hu j
  · exact hv j

end Erdos3

end

end OAI
