import OAI.Combinatorics.Progressions.Estimates.RealFirstCoefficientHorizontal

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

def RealAdaptedCoefficientGrid (l : ℕ) (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) : Prop :=
  (fun z : AdaptedBasisIndex w ω => ((F.adaptedMonomialBasis b ω hF w).baseChange ℝ).repr x z)
    ∈ realDenominatorGrid l

theorem realAdaptedCoefficientGrid_polynomial_iff (l : ℕ) (g : F.RealAdaptedPolynomialGroup w) :
    F.RealAdaptedCoefficientGrid b ω hF w l g.coord ↔
      F.PolynomialRationalGrid b w l (F.realAdaptedPolynomialGroupHom w g) :=
  (F.polynomialRationalGrid_groupHom_iff b w ω hF l g).symm

theorem realAdaptedCoefficientGrid_mono {l m : ℕ} (hl : 0 < l) (hlm : l ∣ m)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w)
    (hx : F.RealAdaptedCoefficientGrid b ω hF w l x) :
    F.RealAdaptedCoefficientGrid b ω hF w m x :=
  realDenominatorGrid_subset_of_dvd hl hlm hx

theorem realAdaptedDirectionalDerivative_grid [Fintype σ] (l : ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l x) (h : σ → ℤ) :
    F.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l
      (F.realAdaptedDirectionalDerivative (fun i => (h i : ℚ)) x) := by
  classical
  have hfull := (F.realAdaptedCoefficientGrid_polynomial_iff b ω hF (fun _ => 1) l
    (⟨x⟩ : F.RealAdaptedPolynomialGroup (fun _ => 1))).mp hx
  obtain ⟨a, ha⟩ := hfull
  have hcoord (z : AdaptedBasisIndex (fun _ : σ => 1) ω) : ∃ n : ℤ, (n : ℝ) = (l : ℝ) *
      ((F.adaptedMonomialBasis b ω hF (fun _ => 1)).baseChange ℝ).repr
        (F.realAdaptedDirectionalDerivative (fun i => (h i : ℚ)) x) z := by
    rw [← F.realAdaptedPolynomialTensor_coordinates (fun _ => 1) b ω hF,
      F.realAdaptedDirectionalDerivative_polynomial]
    let f := ((b.baseChange ℝ).coord z.val.2).restrictScalars ℚ
    exact directionalDerivative_integral_coordinate f
      (F.realAdaptedPolynomialMap (fun _ => 1) x) l
      (fun β => ⟨a (β, z.val.2), congrFun ha (β, z.val.2)⟩) h z.val.1
  choose a ha using hcoord
  exact ⟨a, funext ha⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
