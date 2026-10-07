import OAI.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization

namespace OAI

section

namespace Erdos3

theorem exists_polynomial_subspace_separation (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {ι κ σ : Type*} [Fintype ι] [Fintype κ]
      (A : Matrix ι κ ℚ) (H l : ℕ), 1 ≤ H → 0 < l →
      (∀ i j, RationalHeightLE (A i j) H) →
      ∀ p : ℝ, 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p →
      (Fintype.card κ : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p →
      (H : ℝ) ≤ Real.exp (P.eval₂ (Nat.castRingHom ℝ) p) →
      (l : ℝ) ≤ Real.exp (P.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∀ α : σ →₀ ℕ, α ≠ 0 → ∀ a b : ι → ℝ,
      ‖a‖ ≤ Real.exp (P.eval₂ (Nat.castRingHom ℝ) p) / monomialScale T α →
      b ∈ realDenominatorGrid l →
      a + b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) →
      a ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) ∧
        b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) := by
  let R := (P + 2) ^ 48 + (P + 2) ^ 24 + P + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro ι κ σ _ _ A H l hH hl hA p hp hι hκ hHp hlp T hT α hα a b ha hb hsum
  have hbudget : separationBudget (P.eval₂ (Nat.castRingHom ℝ) p) ≤ (p + C) ^ C := by
    simpa [R, separationBudget, Polynomial.eval₂_pow] using hbound p hp
  exact controlled_real_column_span_separation A hH hl hA (natPolynomial_eval_nonneg P hp)
    hι hκ hHp hlp T (fun i => (Real.exp_le_exp.mpr hbudget).trans (hT i)) hα a b ha hb hsum

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

theorem exists_vectorPolynomial_subspace_separation (budget : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {J I σ : Type*} [Fintype J] [Fintype I]
      (B : Matrix J I ℚ) (H q : ℕ), 1 ≤ H → 0 < q →
      (∀ j i, RationalHeightLE (B j i) H) →
      ∀ p : ℝ, 0 ≤ p →
      (Fintype.card J : ℝ) ≤ budget.eval₂ (Nat.castRingHom ℝ) p →
      (Fintype.card I : ℝ) ≤ budget.eval₂ (Nat.castRingHom ℝ) p →
      (H : ℝ) ≤ Real.exp (budget.eval₂ (Nat.castRingHom ℝ) p) →
      (q : ℝ) ≤ Real.exp (budget.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∀ A E P Q : VectorPolynomial σ ℝ (J → ℝ),
      A = E + P + Q →
      (∀ α, coefficients A α ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) →
      (∀ α, coefficients P α ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) →
      coefficients E 0 = 0 → coefficients Q 0 = 0 →
      (∀ α j, |coefficients E α j| ≤
        Real.exp (budget.eval₂ (Nat.castRingHom ℝ) p) / monomialScale T α) →
      (∀ α, coefficients Q α ∈ realDenominatorGrid q) →
      (∀ α, coefficients E α ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) ∧
      (∀ α, coefficients Q α ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) ∧
      (∀ x, eval x E ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) ∧
      (∀ x, eval x Q ∈
        Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))) := by
  obtain ⟨C, hC, hsep⟩ := exists_polynomial_subspace_separation budget
  refine ⟨C, hC, ?_⟩
  intro J I σ _ _ B H q hH hq hB p hp hJ hI hHp hqp T hT A E P Q
    hdecomp hA hP hE0 hQ0 hE hQ
  let K := Submodule.span ℝ (Set.range (fun i j => (B j i : ℝ)))
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hcoeff (α : σ →₀ ℕ) : coefficients E α ∈ K ∧ coefficients Q α ∈ K := by
    by_cases hα : α = 0
    · subst α
      rw [hE0, hQ0]
      exact ⟨K.zero_mem, K.zero_mem⟩
    · have hsum : coefficients E α + coefficients Q α ∈ K := by
        have hm := K.sub_mem (hA α) (hP α)
        have heq : coefficients A α - coefficients P α =
            coefficients E α + coefficients Q α := by
          rw [hdecomp]
          simp only [map_add, Finsupp.add_apply]
          abel
        rwa [heq] at hm
      have hnorm : ‖coefficients E α‖ ≤
          Real.exp (budget.eval₂ (Nat.castRingHom ℝ) p) / monomialScale T α := by
        apply (pi_norm_le_iff_of_nonneg (div_nonneg (Real.exp_nonneg _)
          (monomialScale_pos T hTpos α).le)).mpr
        intro j
        simpa only [Real.norm_eq_abs] using hE α j
      exact hsep B H q hH hq hB p hp hJ hI hHp hqp T hT α hα
        (coefficients E α) (coefficients Q α) hnorm (hQ α) hsum
  have hEK : ∀ α, coefficients E α ∈ K := fun α => (hcoeff α).1
  have hQK : ∀ α, coefficients Q α ∈ K := fun α => (hcoeff α).2
  refine ⟨hEK, hQK, ?_, ?_⟩
  · intro x
    rw [← eval_restrictCoefficients K E hEK x]
    exact (eval (V := K) x (restrictCoefficients K E hEK)).property
  · intro x
    rw [← eval_restrictCoefficients K Q hQK x]
    exact (eval (V := K) x (restrictCoefficients K Q hQK)).property

end Erdos3

end

end OAI
