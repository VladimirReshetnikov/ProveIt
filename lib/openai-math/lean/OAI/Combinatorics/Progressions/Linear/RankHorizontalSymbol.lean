import OAI.Combinatorics.Progressions.Polynomial.ShiftedPolynomialBasis

namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def rankLayerCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.adaptedLieSubalgebra w →ₗ[ℚ] F.layer (Finsupp.weight w α) 1 :=
  (F.associatedDegree.adaptedCoefficientMap w α).codRestrict (F.layer (Finsupp.weight w α) 1) (by
    intro p
    rw [← F.rank_zero_eq_one]
    exact p.property α)

@[simp] theorem rankLayerCoefficient_coe (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.associatedDegree.adaptedLieSubalgebra w) :
    (F.rankLayerCoefficient w α p : L) = coefficients p.val α := rfl

noncomputable def higherHorizontalCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.adaptedLieSubalgebra w →ₗ[ℚ] F.HigherHorizontal (Finsupp.weight w α) :=
  (F.higherHorizontalMk (Finsupp.weight w α)).comp (F.rankLayerCoefficient w α)

theorem bracket_coefficient_mem_rank_two (w : σ → ℕ)
    (p q : F.associatedDegree.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients ⁅p.val, q.val⁆ α ∈ F.layer (Finsupp.weight w α) 2 := by
  classical
  have hmono (β : σ →₀ ℕ) (x : L) (hx : x ∈ F.layer (Finsupp.weight w β) 2) :
      coefficients (monomial (R := ℚ) β x) α ∈ F.layer (Finsupp.weight w α) 2 := by
    by_cases hβα : β = α
    · subst β
      simpa using hx
    · simp [hβα]
  rw [← sum_monomial_coefficients p.val, ← sum_monomial_coefficients q.val]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients p.val).support (coefficients q.val).support
    (fun β => monomial (R := ℚ) β (coefficients p.val β))
    (fun γ => monomial (R := ℚ) γ (coefficients q.val γ))]
  simp only [map_sum, Finsupp.finsetSum_apply]
  apply Submodule.sum_mem
  intro β _
  apply Submodule.sum_mem
  intro γ _
  rw [lie_monomial]
  apply hmono
  rw [map_add]
  exact F.lie_mem (F.rankLayerCoefficient w β p).property (F.rankLayerCoefficient w γ q).property

theorem higherHorizontalCoefficient_lie (w : σ → ℕ) (α : σ →₀ ℕ)
    (p q : F.associatedDegree.adaptedLieSubalgebra w) :
    F.higherHorizontalCoefficient w α ⁅p, q⁆ = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact F.bracket_coefficient_mem_rank_two w p q α

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def higherHorizontalSymbolCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.PolynomialSymbol w →ₗ[ℚ] F.HigherHorizontal (Finsupp.weight w α) :=
  (F.associatedDegree.shiftedAdaptedIdeal w).toSubmodule.liftQ
    (F.higherHorizontalCoefficient w α) (by
      intro p hp
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact F.lex_antitone (Or.inl (Nat.lt_succ_self (Finsupp.weight w α))) (hp α))

@[simp] theorem higherHorizontalSymbolCoefficient_map (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.associatedDegree.adaptedLieSubalgebra w) :
    F.higherHorizontalSymbolCoefficient w α (F.associatedDegree.polynomialSymbolMap w p) =
      F.higherHorizontalCoefficient w α p := rfl

theorem higherHorizontalSymbolCoefficient_lie (w : σ → ℕ) (α : σ →₀ ℕ)
    (p q : F.associatedDegree.PolynomialSymbol w) :
    F.higherHorizontalSymbolCoefficient w α ⁅p, q⁆ = 0 := by
  obtain ⟨p, rfl⟩ := F.associatedDegree.polynomialSymbolMap_surjective w p
  obtain ⟨q, rfl⟩ := F.associatedDegree.polynomialSymbolMap_surjective w q
  rw [← LieHom.map_lie, F.higherHorizontalSymbolCoefficient_map]
  exact F.higherHorizontalCoefficient_lie w α p q

theorem higherHorizontalCoefficient_translate (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (h : σ → ℚ) (α : σ →₀ ℕ) (p : F.associatedDegree.adaptedLieSubalgebra w) :
    F.higherHorizontalCoefficient w α
      ⟨translate h p.val, (F.associatedDegree.mem_adaptedSubmodule w _).mpr
        (F.associatedDegree.adapted_translate w hw h
          ((F.associatedDegree.mem_adaptedSubmodule w _).mp p.property))⟩ =
      F.higherHorizontalCoefficient w α p := by
  apply (F.higherHorizontalMk_eq _ _ _).mpr
  have hnext := F.associatedDegree.translate_sub_coefficient_mem w hw h
    ((F.associatedDegree.mem_adaptedSubmodule w _).mp p.property) α
  have hrank := F.lex_antitone (i := 2) (j := 0)
    (Or.inl (Nat.lt_succ_self (Finsupp.weight w α))) hnext
  simpa only [rankLayerCoefficient_coe, map_sub, Finsupp.sub_apply] using hrank

end Erdos3.DegreeRankLieFiltration

end

end OAI
