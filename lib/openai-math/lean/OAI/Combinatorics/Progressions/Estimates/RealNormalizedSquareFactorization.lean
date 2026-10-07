import OAI.Combinatorics.Progressions.Polynomial.RealSquarePolynomialFactors

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include b ω hF in
theorem exists_real_normalized_square_factors (h : σ → ℚ) (e m : ℝ ⊗[ℚ] L)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (r : F.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hf : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) r).coord =
      normalizedShiftLog (s + 1) h (-e) (-m) (F.realAdaptedPolynomialMap (fun _ => 1) g.coord))
    (hs : F.realAdaptedPolynomialMap (fun _ => 1) (F.realSquareSndPolynomialHom (fun _ => 1) r).coord =
      F.realAdaptedPolynomialMap (fun _ => 1) g.coord) :
    ∃ x : ℝ ⊗[ℚ] F.normalizedRelativeSubmodule (fun _ : σ => 1),
      F.realAdaptedPolynomialTensor (fun _ => 1)
        ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
          F.realification.normalizedRelativeLog h e m
            (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord) ∧
      r = F.realRelativeSquarePolynomial (fun _ => 1) (fun _ => Nat.zero_lt_one) x *
        F.realSquareDiagonalPolynomialHom (fun _ => 1) g ∧
      F.realNormalizedFirstCoefficientMap (fun _ => 1) x =
        F.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          F.realFirstCoefficientConstant (fun _ => 1) e -
          F.realFirstCoefficientAdjoint (fun _ => 1) g (F.realFirstCoefficientConstant (fun _ => 1) m) := by
  have hzero := F.realSquarePolynomial_horizontal (fun _ : σ => 1) r
  rw [hf, hs] at hzero
  obtain ⟨x, hx, hcoeff⟩ := F.exists_real_normalizedRelative_preimage b ω hF h e m g hzero
  let y : F.RealAdaptedPolynomialGroup (fun _ : σ => 1) :=
    ⟨(F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x⟩
  have hshift : F.realAdaptedPolynomialTensor (fun _ => 1)
      (F.realSquareFstPolynomialHom (fun _ => 1) r).coord =
        F.realification.normalizedShiftAdapted h (-e) (-m)
          (F.realAdaptedPolynomialTensor (fun _ => 1) g.coord) := Subtype.ext hf
  have hy : F.realAdaptedPolynomialGroupHom (fun _ => 1) y =
      F.realAdaptedPolynomialGroupHom (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) r) *
        (F.realAdaptedPolynomialGroupHom (fun _ => 1) g)⁻¹ := by
    apply NilpotentLieBCHGroup.ext
    change F.realAdaptedPolynomialTensor (fun _ => 1)
        ((F.normalizedRelativeSubmodule (fun _ => 1)).subtype.baseChange ℝ x) =
      lieBCH (s + 1)
        (F.realAdaptedPolynomialTensor (fun _ => 1) (F.realSquareFstPolynomialHom (fun _ => 1) r).coord)
        (-(F.realAdaptedPolynomialTensor (fun _ => 1) g.coord))
    rw [hshift]
    exact hx
  have hfirst : F.realSquareFstPolynomialHom (fun _ => 1) r = y * g := by
    apply F.realAdaptedPolynomialGroupHom_injective (fun _ => 1) b ω hF
    rw [map_mul, hy]
    group
  have hsecond : F.realSquareSndPolynomialHom (fun _ => 1) r = g := by
    apply F.realAdaptedPolynomialGroupHom_injective (fun _ => 1) b ω hF
    apply NilpotentLieBCHGroup.ext
    exact Subtype.ext hs
  exact ⟨x, hx, F.realSquarePolynomial_factorization (fun _ => 1)
    (fun _ => Nat.zero_lt_one) r g x hfirst hsecond, hcoeff⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
