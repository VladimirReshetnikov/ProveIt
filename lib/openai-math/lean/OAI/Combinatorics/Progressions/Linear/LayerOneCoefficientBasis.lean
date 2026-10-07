import OAI.Combinatorics.Progressions.Geometry.RealFastCoefficientCoordinates

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

abbrev LayerOneBasisIndex (ω : ι → ℕ) := {i : ι // ¬ 2 ≤ ω i}

noncomputable def layerOneBasis : Basis (LayerOneBasisIndex ω) ℚ (L ⧸ F.layer 2) :=
  supportedQuotientBasis e (F.layer 2) {i | 2 ≤ ω i} (hF 2)

theorem layerOneBasis_repr_mk (x : L) (i : LayerOneBasisIndex ω) :
    (F.layerOneBasis e ω hF).repr ((F.layer 2).mkQ x) i = e.repr x i :=
  supportedQuotientBasis_repr_mk e (F.layer 2) {i | 2 ≤ ω i} (hF 2) x i

def horizontalCoefficientIndex (w : σ → ℕ) (i : LayerOneBasisIndex ω) :
    FirstCoefficientIndex w ω :=
  ⟨(0, i.val), by
    have hp := F.adaptedBasis_weight_pos e ω hF i.val
    have hi := i.property
    simp only [map_zero, Nat.zero_add]
    omega⟩

def layerOneIndexOfConstant (w : σ → ℕ) (z : FirstCoefficientIndex w ω)
    (hz : z.val.1 = 0) : LayerOneBasisIndex ω :=
  ⟨z.val.2, by
    have h := z.property
    rw [hz, map_zero] at h
    omega⟩

theorem horizontalCoefficientIndex_of_constant (w : σ → ℕ)
    (z : FirstCoefficientIndex w ω) (hz : z.val.1 = 0) :
    F.horizontalCoefficientIndex e ω hF w (layerOneIndexOfConstant ω w z hz) = z := by
  apply Subtype.ext
  exact Prod.ext hz.symm rfl

theorem firstCoefficientHorizontal_coordinates (w : σ → ℕ)
    (x : F.FirstCoefficientModule w) (i : LayerOneBasisIndex ω) :
    (F.layerOneBasis e ω hF).repr (F.firstCoefficientHorizontal w x) i =
      (F.firstCoefficientBasis e ω hF w).repr x (F.horizontalCoefficientIndex e ω hF w i) := by
  obtain ⟨x, rfl⟩ := F.firstCoefficientMap_surjective w x
  rw [F.firstCoefficientHorizontal_map, F.layerOneBasis_repr_mk,
    F.firstCoefficientBasis_repr_map]
  rfl

theorem realFirstCoefficientHorizontal_coordinates (w : σ → ℕ)
    (x : F.RealFirstCoefficientModule w) (i : LayerOneBasisIndex ω) :
    ((F.layerOneBasis e ω hF).baseChange ℝ).repr (F.realFirstCoefficientHorizontal w x) i =
      (F.realFirstCoefficientBasis e ω hF w).repr x
        (F.horizontalCoefficientIndex e ω hF w i) := by
  obtain ⟨x, rfl⟩ := (F.firstCoefficientRealEquiv w).surjective x
  change ((F.layerOneBasis e ω hF).baseChange ℝ).repr
    ((F.firstCoefficientHorizontal w).baseChange ℝ
      ((F.firstCoefficientRealEquiv w).symm (F.firstCoefficientRealEquiv w x))) i = _
  rw [LinearEquiv.symm_apply_apply, F.firstCoefficientRealEquiv_coordinates]
  exact baseChange_coordinate_eq (F.firstCoefficientBasis e ω hF w)
    (F.layerOneBasis e ω hF) (F.firstCoefficientHorizontal w)
    (F.horizontalCoefficientIndex e ω hF w)
    (F.firstCoefficientHorizontal_coordinates e ω hF w) x i

end Erdos3.NilpotentLieFiltration

end

end OAI
