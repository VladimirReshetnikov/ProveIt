import OAI.Combinatorics.Progressions.Geometry.PhysicalChartRadiusBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedPhysicalChartRadius_density_small {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (α : Type*) [Fintype α] (C R : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hR : ∀ j, 0 ≤ R j)
    (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j) (j : Fin m) :
    C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4 := by
  let N := (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ)
  let F := (2 : ℝ) ^ Fintype.card α * (1 + Fintype.card α) ^ (j.val + 1)
  let D := (N + 1) * F * ((C j + 1) * ((Fintype.card (I j) : ℝ) + 1))
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hCj := hC j
  have hF₁ : (1 : ℝ) ≤ 2 ^ Fintype.card α := one_le_pow₀ (by norm_num)
  have hF₂ : (1 : ℝ) ≤ (1 + Fintype.card α) ^ (j.val + 1) :=
    one_le_pow₀ (by linarith [show (0 : ℝ) ≤ Fintype.card α from Nat.cast_nonneg _])
  have hF : 1 ≤ F := by
    simpa only [one_mul] using mul_le_mul hF₁ hF₂ (by norm_num) (by positivity)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hcoef : C j * ((Fintype.card (I j) : ℝ) + 1) ≤ D := by
    have hNF : 1 ≤ (N + 1) * F := by nlinarith
    have h := mul_le_mul_of_nonneg_right hNF
      (by positivity : 0 ≤ (C j + 1) * ((Fintype.card (I j) : ℝ) + 1))
    dsimp only [D]
    nlinarith [hC j, show (0 : ℝ) ≤ Fintype.card (I j) from Nat.cast_nonneg _]
  calc
    _ ≤ D * R j := mul_le_mul_of_nonneg_right hcoef (hR j)
    _ ≤ D * (1 / (4 * D)) := mul_le_mul_of_nonneg_left (hsmall j) hD.le
    _ = 1 / 4 := by field_simp [hD.ne']

end Erdos3.VectorPolynomial

end

end OAI
