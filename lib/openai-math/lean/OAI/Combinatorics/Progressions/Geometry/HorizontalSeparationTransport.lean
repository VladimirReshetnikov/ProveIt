import OAI.Combinatorics.Progressions.Linear.ControlledKernelSplitTransport

namespace OAI

section

namespace Erdos3

theorem horizontal_parts_separation_equiv {H ι κ ν σ : Type*}
    [AddCommGroup H] [Module ℝ H] [Fintype ι] [Fintype κ] [Fintype ν]
    (e : H ≃ₗ[ℝ] (ι → ℝ)) (U K : Submodule ℝ H)
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ)
    (hAspan : Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) = U.map e.toLinearMap)
    (hBspan : Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) = K.map e.toLinearMap)
    {J l : ℕ} (hJ : 1 ≤ J) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) J) (hB : ∀ i j, RationalHeightLE (B i j) J)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hJp : (J : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) (i : σ)
    (y small rational : H) (k : K) (hsystem : y = small + rational + k.val)
    (hy : y ∈ U) (hs : ‖e small‖ ≤ Real.exp p / T i)
    (hr : e rational ∈ realDenominatorGrid l) :
    small ∈ U ⊔ K ∧ rational ∈ U ⊔ K := by
  classical
  let M := Matrix.fromCols A B
  have hM : ∀ i j, RationalHeightLE (M i j) J := by
    intro i j
    cases j with
    | inl j => exact hA i j
    | inr j => exact hB i j
  have hspan : Submodule.span ℝ (Set.range (fun j i => (M i j : ℝ))) =
      U.map e.toLinearMap ⊔ K.map e.toLinearMap := by
    change Submodule.span ℝ (Set.range ((Matrix.fromCols A B).map (Rat.castHom ℝ)).col) = _
    rw [real_column_span_fromCols, hAspan, hBspan]
  have heq : e y = e small + e rational + e k.val := by rw [hsystem, map_add, map_add]
  have hs' : ‖e small‖ ≤ Real.exp p / monomialScale T (Finsupp.single i 1) := by
    simpa [monomialScale] using hs
  have hparts := horizontal_parts_separation (U.map e.toLinearMap) (K.map e.toLinearMap)
    M hspan hJ hl hM hp hι hcols hJp hlp T hT
    (show (Finsupp.single i 1 : σ →₀ ℕ) ≠ 0 by simp) (e y) (e small) (e rational) (e k.val)
    heq ⟨y, hy, rfl⟩ ⟨k.val, k.property, rfl⟩ hs' hr
  have hmem (x : H) (hx : e x ∈ U.map e.toLinearMap ⊔ K.map e.toLinearMap) : x ∈ U ⊔ K := by
    rw [← Submodule.map_sup, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] at hx
    exact hx
  exact ⟨hmem small hparts.1, hmem rational hparts.2⟩

end Erdos3

end

end OAI
