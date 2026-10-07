import OAI.Combinatorics.Progressions.Estimates.FrozenMarkedLeftOrbitBound
import OAI.Combinatorics.Progressions.Estimates.NativeCorrelatedFactorFamily

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_frozenMarkedRightOrbit_grid_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ ι κ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [DecidableEq κ]
        [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
        {t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
        (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ) (S : M →ₗ[ℚ] L)
        (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j) (H : ℕ) (p : ℝ),
        0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
        (∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) →
        ∀ q r : ℕ, 0 < q → 0 < r →
          ((matrixDenominator (LinearMap.toMatrix c b S) * q * r : ℕ) : ℝ) ≤ Real.exp p →
          ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            matrixDenominator (LinearMap.toMatrix c b S) * q * r ∣ m ∧
            ∀ marked : G.realification.PolynomialOrbit w,
              CoefficientGrid (c.baseChange ℝ) q marked.log →
              ∀ center : F.realification.Group,
                (b.baseChange ℝ).equivFun center.coord ∈ realDenominatorGrid r →
                ∀ x : σ → ℤ,
                  (b.baseChange ℝ).equivFun
                    (F.realification.polynomialOrbitEval w x
                      (F.frozenMarkedRightOrbit G w S hS marked center)).coord ∈
                    realDenominatorGrid m := by
  obtain ⟨C, hC, hclosure⟩ := exists_real_bch_rational_closure s
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ _ t F G b c w S hS H p hp hd hH hb q r hq hr hlp
  have hDq : 0 < matrixDenominator (LinearMap.toMatrix c b S) * q :=
    Nat.mul_pos (matrixDenominator_pos _) hq
  obtain ⟨m, hm, hmp, hlm, hmul, _⟩ :=
    hclosure b H p F.lowerCentralSeries_eq_bot hp hd hH hb
      (matrixDenominator (LinearMap.toMatrix c b S) * q * r)
      (Nat.mul_pos hDq hr) hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro marked hmarked center hcenter x
  rw [← polynomialOrbitRealEval_integer, frozenMarkedRightOrbit_realEval,
    polynomialOrbitRealEval_integer]
  apply hmul
  · exact realDenominatorGrid_subset_of_dvd hDq (dvd_mul_right _ _)
      (realified_linear_coordinate_grid c b S q _
        (G.polynomialOrbit_coefficient_grid_value c w q marked hmarked x))
  · exact realDenominatorGrid_subset_of_dvd hr (dvd_mul_left _ _) hcenter

end Erdos3.NilpotentLieFiltration

end

end OAI
