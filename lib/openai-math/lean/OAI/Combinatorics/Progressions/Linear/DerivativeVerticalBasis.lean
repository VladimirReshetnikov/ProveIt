import OAI.Combinatorics.Progressions.Geometry.DerivativeVerticalCoordinates

namespace OAI

section

namespace Erdos3

theorem exists_vertical_derivative_grid_matrix
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ] {k : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (v : Fin k → EuclideanSpace ℝ (σ ⊕ κ))
    (hli : LinearIndependent ℝ v)
    (hv : ∀ j, v j ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl)
    (hzero : ∀ j, euclideanDerivativeShiftMap T hT (v j) = 0) :
    ∃ B : Matrix κ (Fin k) ℝ, LinearIndependent ℝ B.col ∧
      (∀ j, B.col j ∈ realDenominatorGrid l) ∧
      ∀ j, v j = euclideanVerticalMap scale hscale A (B.col j) := by
  choose r hr he using fun j =>
    euclideanDerivative_vertical_grid_coordinates T hT scale hscale Y A l hl (v j) (hv j) (hzero j)
  let B : Matrix κ (Fin k) ℝ := fun i j => r j i
  refine ⟨B, ?_, hr, he⟩
  apply LinearIndependent.of_comp (euclideanVerticalMap scale hscale A)
  have hf : euclideanVerticalMap scale hscale A ∘ B.col = v :=
    funext (fun j => (he j).symm)
  rw [hf]
  exact hli

end Erdos3

end

section

namespace Erdos3

theorem exists_derivative_vertical_basis_matrix
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R : ℝ) :
    let Λ := euclideanDerivativeLattice T hT scale hscale Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    ∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℤ L,
      ∃ B : Matrix κ (Fin (Module.finrank ℝ V)) ℝ,
        LinearIndependent ℝ B.col ∧ (∀ j, B.col j ∈ realDenominatorGrid l) ∧
        ∀ j, (b j).val.val.val = euclideanVerticalMap scale hscale A (B.col j) := by
  let Λ := euclideanDerivativeLattice T hT scale hscale Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hscale Y A l hl R
  let b := finiteLatticeBasis L
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ κ) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  let v := fun j => f (b j).val
  have hli : LinearIndependent ℝ v := by
    have h := (b.ofZLatticeBasis ℝ L).linearIndependent.map' f.toLinearMap
      (LinearMap.ker_eq_bot.mpr f.injective)
    simpa only [v, Function.comp_def, Module.Basis.ofZLatticeBasis_apply,
      LinearIsometry.coe_toLinearMap] using h
  have hv (j) : v j ∈ Λ := (b j).property
  have hz (j) : euclideanDerivativeShiftMap T hT (v j) = 0 := (b j).val.property
  obtain ⟨B, hB, hgrid, he⟩ := exists_vertical_derivative_grid_matrix
    T hT scale hscale Y A l hl v hli hv hz
  exact ⟨b, B, hB, hgrid, he⟩

end Erdos3

end

end OAI
