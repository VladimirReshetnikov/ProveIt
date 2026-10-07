import OAI.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def layerSamplerTailScaleFloor (R σ : Fin m → ℝ) (j : Fin m) : ℝ :=
  32 * (probabilityProfileLipschitz : ℝ) *
    ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      (j.val + 1)) : ℝ) + 1) / (σ j * R j)

theorem layerSamplerTailWidth_of_scaleFloor
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {S0 : ℕ} (hfloor : ∀ j, layerSamplerTailScaleFloor (G := G) B R σ j ≤ S0) :
    ∀ j, 8 * (probabilityProfileLipschitz : ℝ) ≤
      layerSamplerTailWidth (G := G) B R σ j * S0 := by
  intro j
  have hj := (div_le_iff₀ (mul_pos (hσ j) (hR j))).mp (hfloor j)
  change 8 * (probabilityProfileLipschitz : ℝ) ≤
    (σ j * R j / (4 * ((Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1))) * S0
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity)).mpr
  convert hj using 1 <;> ring

theorem layerSamplerTailScaleFloor_le_exp
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {a c r t : ℝ}
    (hprofile : 8 * (probabilityProfileLipschitz : ℝ) ≤ Real.exp a)
    (hcount : ∀ j : Fin m, 4 * ((Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1) ≤ Real.exp c)
    (hradius : ∀ j, (R j)⁻¹ ≤ Real.exp r)
    (htolerance : ∀ j, (σ j)⁻¹ ≤ Real.exp t) :
    ∀ j, layerSamplerTailScaleFloor (G := G) B R σ j ≤ Real.exp (a + c + r + t) := by
  intro j
  calc
    _ = (8 * (probabilityProfileLipschitz : ℝ)) *
        (4 * ((Fintype.card (BoundedCoefficientExponent
          (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1)) *
        (R j)⁻¹ * (σ j)⁻¹ := by
      unfold layerSamplerTailScaleFloor
      field_simp
      ring
    _ ≤ Real.exp a * Real.exp c * Real.exp r * Real.exp t := by
      have hRj := (hR j).le
      have hσj := (hσ j).le
      gcongr <;> first
        | exact hprofile
        | exact hcount j
        | exact hradius j
        | exact htolerance j
    _ = _ := by rw [Real.exp_add, Real.exp_add, Real.exp_add]

variable [∀ j, IsEmpty (Fin (n j))]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}

def emptyLayerSamplerScale (S0 : ℕ) (hS0 : 0 < S0)
    (hwidth : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) ≤
      layerSamplerTailWidth (G := G) B R σ j * S0) :
    LayerSamplerScale (G := G) B U b R σ where
  value := S0
  positive := hS0
  width := hwidth
  gap := fun _ i => isEmptyElim i

@[simp] theorem emptyLayerSamplerScale_value (S0 : ℕ) (hS0 : 0 < S0)
    (hwidth : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) ≤
      layerSamplerTailWidth (G := G) B R σ j * S0) :
    (emptyLayerSamplerScale B U b S0 hS0 hwidth).value = S0 := rfl

def emptyLayerSamplerScaleOfFloor
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S0 : ℕ) (hS0 : 0 < S0)
    (hfloor : ∀ j, layerSamplerTailScaleFloor (G := G) B R σ j ≤ S0) :
    LayerSamplerScale (G := G) B U b R σ :=
  emptyLayerSamplerScale B U b S0 hS0 (layerSamplerTailWidth_of_scaleFloor B hR hσ hfloor)

@[simp] theorem emptyLayerSamplerScaleOfFloor_value
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S0 : ℕ) (hS0 : 0 < S0)
    (hfloor : ∀ j, layerSamplerTailScaleFloor (G := G) B R σ j ≤ S0) :
    (emptyLayerSamplerScaleOfFloor B U b hR hσ S0 hS0 hfloor).value = S0 := rfl

def emptyLayerSamplerScaleOfExp
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {a c r t : ℝ}
    (hprofile : 8 * (probabilityProfileLipschitz : ℝ) ≤ Real.exp a)
    (hcount : ∀ j : Fin m, 4 * ((Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1) ≤ Real.exp c)
    (hradius : ∀ j, (R j)⁻¹ ≤ Real.exp r)
    (htolerance : ∀ j, (σ j)⁻¹ ≤ Real.exp t)
    (S0 : ℕ) (hS0 : 0 < S0) (hS : Real.exp (a + c + r + t) ≤ S0) :
    LayerSamplerScale (G := G) B U b R σ :=
  emptyLayerSamplerScaleOfFloor B U b hR hσ S0 hS0 (fun j =>
    (layerSamplerTailScaleFloor_le_exp B hR hσ hprofile hcount hradius htolerance j).trans hS)

@[simp] theorem emptyLayerSamplerScaleOfExp_value
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {a c r t : ℝ}
    (hprofile : 8 * (probabilityProfileLipschitz : ℝ) ≤ Real.exp a)
    (hcount : ∀ j : Fin m, 4 * ((Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1) ≤ Real.exp c)
    (hradius : ∀ j, (R j)⁻¹ ≤ Real.exp r)
    (htolerance : ∀ j, (σ j)⁻¹ ≤ Real.exp t)
    (S0 : ℕ) (hS0 : 0 < S0) (hS : Real.exp (a + c + r + t) ≤ S0) :
    (emptyLayerSamplerScaleOfExp B U b hR hσ hprofile hcount hradius htolerance
      S0 hS0 hS).value = S0 := rfl

end Erdos3.VectorPolynomial

end

end OAI
