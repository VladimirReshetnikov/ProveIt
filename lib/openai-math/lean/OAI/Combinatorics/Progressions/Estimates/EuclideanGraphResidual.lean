import OAI.Combinatorics.Progressions.Lattices.ScaledLatticeCovolume
import OAI.Combinatorics.Progressions.Linear.EuclideanDerivativeProjection

namespace OAI

section

namespace Erdos3

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

noncomputable def euclideanDerivativeShiftMap (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) :
    EuclideanSpace ℝ (σ ⊕ κ) →ₗ[ℝ] (σ → ℝ) :=
  (coordinateScaleEquiv T hT).toLinearMap.comp
    ((LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp productEuclideanEquiv.symm.toLinearMap)

omit [Fintype σ] [Fintype κ] in
theorem euclideanDerivativeShiftMap_apply (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (v : EuclideanSpace ℝ (σ ⊕ κ)) (i : σ) :
    euclideanDerivativeShiftMap T hT v i = T i * v (Sum.inl i) := rfl

omit [Fintype σ] [Fintype κ] in
theorem euclideanDerivativeShiftMap_eq_zero_iff (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (v : EuclideanSpace ℝ (σ ⊕ κ)) :
    euclideanDerivativeShiftMap T hT v = 0 ↔ ∀ i : σ, v (Sum.inl i) = 0 := by
  simp only [funext_iff, euclideanDerivativeShiftMap_apply, Pi.zero_apply,
    mul_eq_zero, hT, false_or]

variable (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
  (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (l : ℕ) (hl : 0 < l)

theorem euclideanDerivativeShiftMap_integer (v : EuclideanSpace ℝ (σ ⊕ κ))
    (hv : v ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl) :
    euclideanDerivativeShiftMap T hT v ∈ realIntegerGrid := by
  have hv' := (euclideanDerivativeLattice_mem_iff T hT scale hscale Y A l hl v).mp hv
  obtain ⟨h, z, hz⟩ := (derivativeLattice_mem_iff T hT scale hscale Y A l hl _).mp hv'
  refine ⟨h, ?_⟩
  funext i
  change (h i : ℝ) = T i * (productEuclideanEquiv.symm v).1 i
  rw [hz, derivativeLatticeEquiv_apply]
  exact (mul_div_cancel₀ (h i : ℝ) (hT i)).symm

theorem euclideanDerivative_vertical_lattice_full (R : ℝ) :
    let Λ := euclideanDerivativeLattice T hT scale hscale Y A l hl
    let Z := shortVectorSpan Λ R
    IsZLattice ℝ (latticeKernel (shortVectorLattice Λ R)
      ((euclideanDerivativeShiftMap T hT).comp Z.subtype)) := by
  apply latticeKernel_full
  intro x hx
  exact euclideanDerivativeShiftMap_integer T hT scale hscale Y A l hl x.val hx

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_integer_shift_lifts
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → κ → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i) :
    let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
    let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT0 scale hscale Y A l hl
    let Z := shortVectorSpan Λ ρ
    ∃ I : ℕ, 0 < I ∧ ∀ z : σ → ℤ, ∃ v : Z,
      v ∈ shortVectorLattice Λ ρ ∧
      euclideanDerivativeShiftMap T hT0 v.val = I • (fun i => (z i : ℝ)) := by
  let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
  let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
  let Λ := euclideanDerivativeLattice T hT0 scale hscale Y A l hl
  let Z := shortVectorSpan Λ ρ
  let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
  let π₀ := (LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp productEuclideanEquiv.symm.toLinearMap
  have hproj : Z.map π₀ = ⊤ := euclideanDerivativeLattice_shortSpan_projection
    T hT scale hscale Y A l hl R δ hR H r hr hnorm hdense hlarge
  have hmap : Z.map (euclideanDerivativeShiftMap T hT0) = ⊤ := by
    change Z.map ((coordinateScaleEquiv T hT0).toLinearMap.comp π₀) = ⊤
    rw [Submodule.map_comp, hproj, Submodule.map_top]
    exact (coordinateScaleEquiv T hT0).range
  have hsurj : Function.Surjective π := by
    intro x
    have hx : x ∈ Z.map (euclideanDerivativeShiftMap T hT0) := by rw [hmap]; trivial
    obtain ⟨v, hv, he⟩ := hx
    exact ⟨⟨v, hv⟩, he⟩
  have hinteger : ∀ x ∈ shortVectorLattice Λ ρ, π x ∈ realIntegerGrid := by
    intro x hx
    exact euclideanDerivativeShiftMap_integer T hT0 scale hscale Y A l hl x.val hx
  let I := (latticeImage (shortVectorLattice Λ ρ) π).toAddSubgroup.relIndex
    integerCoordinateLattice.toAddSubgroup
  refine ⟨I, latticeImage_index_pos (shortVectorLattice Λ ρ) π hinteger hsurj, ?_⟩
  intro z
  exact latticeImage_index_lift (shortVectorLattice Λ ρ) π (fun i => (z i : ℝ)) ⟨z, rfl⟩

end Erdos3

end

section

namespace Erdos3

theorem euclidean_graph_residual_mem_kernel
    {σ κ : Type*} [Fintype σ] [Fintype κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i) (x : Z) :
    x - G (fun i => x.val (Sum.inl i)) ∈
      LinearMap.ker ((euclideanDerivativeShiftMap T hT).comp Z.subtype) := by
  change euclideanDerivativeShiftMap T hT
    ((x - G (fun i => x.val (Sum.inl i))).val) = 0
  apply (euclideanDerivativeShiftMap_eq_zero_iff T hT _).mpr
  intro i
  change x.val (Sum.inl i) - (G (fun j => x.val (Sum.inl j))).val (Sum.inl i) = 0
  rw [hG, sub_self]

end Erdos3

end

end OAI
