import OAI.Combinatorics.Progressions.Estimates.SymbolFastMembership

namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

theorem projectedHorizontal_factorization (ht : 1 ≤ t) (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : σ → ℝ) (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) (l : ℕ)
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hfactor : F.SymbolFactorizationIn b ω hF T X p l U) :
    ∃ E R : F.RealPolynomialSymbolGroup (fun _ : σ => 1),
      F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp p) E ∧
      F.SymbolRationalGrid b ω hF (fun _ => 1) l R ∧
      ∀ α : σ →₀ ℕ,
        (G.projectedHorizontalSymbolCoefficient F φ hφ (fun _ => 1) α).baseChange ℝ X.coord -
          (G.projectedHorizontalSymbolCoefficient F φ hφ (fun _ => 1) α).baseChange ℝ E.coord -
          (G.projectedHorizontalSymbolCoefficient F φ hφ (fun _ => 1) α).baseChange ℝ R.coord ∈
        (G.layerHorizontalImage (F.gradedRefiltrationLayer U) φ
          (fun d x hx => hφ d x (F.gradedRefiltrationLayer_le U d hx))
            (Finsupp.weight (fun _ => 1) α)).baseChange ℝ := by
  obtain ⟨E, P, R, hprod, hE, hR, hP⟩ := hfactor
  refine ⟨E, R, hE, hR, ?_⟩
  intro α
  let f := (G.projectedHorizontalSymbolCoefficient F φ hφ (fun _ : σ => 1) α).baseChange ℝ
  have hsum := congrArg (G.realProjectedHorizontalSymbolHom F φ hφ ht (fun _ : σ => 1) α) hprod
  rw [map_mul, map_mul] at hsum
  have hsum' := congrArg Multiplicative.toAdd hsum
  change f E.coord + f P.coord + f R.coord = f X.coord at hsum'
  have hres : f X.coord - f E.coord - f R.coord = f P.coord := by
    rw [← hsum']
    abel
  change f X.coord - f E.coord - f R.coord ∈ _
  rw [hres]
  exact G.real_projectedHorizontalSymbolCoefficient_mem F φ hφ b ω hF (fun _ => 1) U P.coord hP α

end Erdos3.DegreeRankLieFiltration

end

end OAI
