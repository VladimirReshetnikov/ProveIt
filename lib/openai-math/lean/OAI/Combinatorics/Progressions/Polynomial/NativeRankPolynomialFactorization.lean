import OAI.Combinatorics.Progressions.Linear.RankIntervalFactorization

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
  {E : RationalFilteredNilmanifold L s n} (T : E.DegreeRankStructure r)

theorem polynomialOrbit_mul_coefficient_sub_mem_rank_two
    (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ)
    (g h : E.filtration.realification.PolynomialOrbit w) :
    coefficients (g * h).log α - (coefficients g.log α + coefficients h.log α) ∈
      (T.filtration.layer (Finsupp.weight w α) 2).baseChange ℝ := by
  have hh := T.filtration.realification.polynomialOrbit_mul_coefficient_sub_mem_rank_two
    hs w α (T.orbitEquiv w g) (T.orbitEquiv w h)
  rw [← map_mul, T.orbitEquiv_log, T.orbitEquiv_log, T.orbitEquiv_log] at hh
  exact hh

theorem exists_polynomialOrbit_factorization_rank_two
    (hs : 1 ≤ s) (w : σ → ℕ) (α : ι → σ →₀ ℕ)
    (g ε A U ρ : E.filtration.realification.PolynomialOrbit w)
    (hg : E.filtration.realification.polynomialOrbitEval w 0 g = 1)
    (hε : E.filtration.realification.polynomialOrbitEval w 0 ε = 1)
    (hA : E.filtration.realification.polynomialOrbitEval w 0 A = 1)
    (hU : E.filtration.realification.polynomialOrbitEval w 0 U = 1)
    (hρ : E.filtration.realification.polynomialOrbitEval w 0 ρ = 1)
    (hcoeff : ∀ i, coefficients g.log (α i) -
      (coefficients ε.log (α i) + coefficients A.log (α i) +
        coefficients U.log (α i) + coefficients ρ.log (α i)) ∈
          (T.filtration.layer (Finsupp.weight w (α i)) 2).baseChange ℝ) :
    ∃ K : E.filtration.realification.PolynomialOrbit w,
      E.filtration.realification.polynomialOrbitEval w 0 K = 1 ∧ ε * A * K * U * ρ = g ∧
      ∀ i, coefficients K.log (α i) ∈
        (T.filtration.layer (Finsupp.weight w (α i)) 2).baseChange ℝ := by
  obtain ⟨K, hK0, hprod, hK⟩ := T.filtration.realification.exists_polynomialOrbit_factorization_rank_two
    hs w α (T.orbitEquiv w g) (T.orbitEquiv w ε) (T.orbitEquiv w A)
    (T.orbitEquiv w U) (T.orbitEquiv w ρ)
    ((T.orbitEquiv_eval w g 0).trans hg) ((T.orbitEquiv_eval w ε 0).trans hε)
    ((T.orbitEquiv_eval w A 0).trans hA) ((T.orbitEquiv_eval w U 0).trans hU)
    ((T.orbitEquiv_eval w ρ 0).trans hρ) (by
      intro i
      change coefficients (T.orbitEquiv w g).log (α i) -
        (coefficients (T.orbitEquiv w ε).log (α i) + coefficients (T.orbitEquiv w A).log (α i) +
          coefficients (T.orbitEquiv w U).log (α i) + coefficients (T.orbitEquiv w ρ).log (α i)) ∈
        (T.filtration.layer (Finsupp.weight w (α i)) 2).baseChange ℝ
      simpa only [T.orbitEquiv_log] using hcoeff i)
  let K' := (T.orbitEquiv w).symm K
  have hK'eq : T.orbitEquiv w K' = K := (T.orbitEquiv w).apply_symm_apply K
  have hK'log : K'.log = K.log := by
    rw [← hK'eq, T.orbitEquiv_log]
  refine ⟨K', ?_, ?_, ?_⟩
  · have hh := T.orbitEquiv_eval w K' 0
    rw [hK'eq] at hh
    exact hh.symm.trans hK0
  · apply (T.orbitEquiv w).injective
    simpa only [map_mul, hK'eq] using hprod
  · intro i
    rw [hK'log]
    exact hK i

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI
