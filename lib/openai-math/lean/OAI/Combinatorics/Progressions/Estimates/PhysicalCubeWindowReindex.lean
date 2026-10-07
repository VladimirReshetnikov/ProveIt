import OAI.Combinatorics.Progressions.Geometry.PhysicalSupportedCubes
import OAI.Combinatorics.Progressions.Lattices.PhysicalSpatialResidueSupport

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem physicalResidueWindow_sum_eq_box_sum {K X : Type*} [Fintype K]
    [Fintype X] [DecidableEq X] {dim : ℕ}
    (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q N : X → ℕ) (hq : ∀ x, 0 < q x)
    (window : Finset (X → (Unit ⊕ Fin dim) → ℤ))
    (φ : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)
    (hbox : ∀ v ∈ window, φ (physicalResidueReconstruction root D base residue q v) ≠ 0 →
      ∀ s, physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s ∈ integerBox N)
    (hwindow : ∀ v, v ∉ window → φ (physicalResidueReconstruction root D base residue q v) = 0)
    (hresidue : ∀ u, φ u ≠ 0 → u ∈ Set.range (physicalResidueReconstruction root D base residue q)) :
    (∑ v ∈ window, φ (physicalResidueReconstruction root D base residue q v)) =
      ∑ u ∈ physicalIntegerBoxCubes N dim, φ u := by
  have hi := physicalResidueReconstruction_injective root D base residue q hq
  calc
    _ = ∑ u ∈ window.image (physicalResidueReconstruction root D base residue q), φ u := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => hi h
    _ = _ := by
      apply Finset.sum_congr_of_eq_on_inter
      · intro u hu hn
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
        by_contra hne
        exact hn ((mem_physicalIntegerBoxCubes N dim _).mpr (hbox v hv hne))
      · intro u _ hn
        by_contra hne
        obtain ⟨v, rfl⟩ := hresidue u hne
        have hv : v ∉ window := fun hv => hn (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
        exact hne (hwindow v hv)
      · intro _ _ _
        rfl

theorem physicalResidueWindow_sum_eq_count_mul_mean {K X : Type*} [Fintype K]
    [Fintype X] [DecidableEq X] {dim : ℕ}
    (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q N : X → ℕ) (hq : ∀ x, 0 < q x)
    (window : Finset (X → (Unit ⊕ Fin dim) → ℤ))
    (φ : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)
    (hbox : ∀ v ∈ window, φ (physicalResidueReconstruction root D base residue q v) ≠ 0 →
      ∀ s, physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s ∈ integerBox N)
    (hwindow : ∀ v, v ∉ window → φ (physicalResidueReconstruction root D base residue q v) = 0)
    (hresidue : ∀ u, φ u ≠ 0 → u ∈ Set.range (physicalResidueReconstruction root D base residue q)) :
    (∑ v ∈ window, φ (physicalResidueReconstruction root D base residue q v)) =
      (integerBoxCubeCount N dim : ℂ) *
        𝔼 p : SupportedCube dim (integerBox N : Set (X → ℤ)),
          φ ((physicalCubeParametersEquiv X dim).symm p.val) := by
  rw [physicalResidueWindow_sum_eq_box_sum root D base residue q N hq window φ hbox hwindow hresidue,
    physicalIntegerBoxCubes_sum_eq_count_mul_mean]

end Erdos3.BooleanCubeKernel

end

end OAI
