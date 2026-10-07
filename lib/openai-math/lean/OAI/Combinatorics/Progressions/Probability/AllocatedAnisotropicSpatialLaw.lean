import OAI.Combinatorics.Progressions.Linear.AllocatedFixedKernelCover
import OAI.Combinatorics.Progressions.Linear.AnisotropicGoodKernelComparison

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Matrix

def physicalSpatialSplitEquiv (G N : Type*) : ((Unit ⊕ G) ⊕ N) ≃ Option (G ⊕ N) :=
  (Equiv.sumAssoc Unit G N).trans (physicalCubeOptionEquiv (G ⊕ N))

theorem physicalSpatialSplit_scale (G N : Type*) (H T : ℝ) :
    physicalSpatialInputScale (G ⊕ N) H T ∘ physicalSpatialSplitEquiv G N =
      Sum.elim (anisotropicSpatialScale G H T) (fun _ : N => T) := by
  funext j
  cases j with
  | inl j => cases j <;> rfl
  | inr j => rfl

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

omit [Fintype α] in
theorem allocatedPhysicalCube_split :
    (physicalCubeCoefficient root dirs).submatrix id
      (physicalSpatialSplitEquiv G (PrincipalTupleIndex B (layerSamplerDegree I n))) =
        Matrix.fromCols (rootDifferenceMatrix ker (scalarCubeDifferenceMatrix x)) cols := by
  ext i j
  cases j with
  | inl j =>
    cases j with
    | inl u =>
      cases u
      exact allocatedPhysicalCube_base_column B U basis S c x y i
    | inr g => exact allocatedPhysicalCube_kernel_columns B U basis S c x y i g
  | inr j => exact allocatedPhysicalCube_principal_columns B U basis S c x y i j

theorem allocatedPhysicalCube_anisotropic_law {H T : ℝ} (hH : 0 < H) (hT : 0 < T) :
    smoothMatrixImagePMF (physicalCubeCoefficient root dirs) (physicalSpatialInputScale vars H T)
      (physicalSpatialInputScale_pos vars hH hT) =
      anisotropicSpatialOutputLaw ker (scalarCubeDifferenceMatrix x) cols H T (fun _ => T)
        hH hT (fun _ => hT) := by
  have h := smoothMatrixImagePMF_reindex (physicalCubeCoefficient root dirs)
    (physicalSpatialSplitEquiv G (PrincipalTupleIndex B (layerSamplerDegree I n)))
    (physicalSpatialInputScale vars H T) (physicalSpatialInputScale_pos vars hH hT)
  rw [allocatedPhysicalCube_split] at h
  simpa only [physicalSpatialSplit_scale, anisotropicSpatialOutputLaw] using h.symm

variable [DecidableEq α] [DecidableEq G]

theorem allocatedPhysicalCube_anisotropic_error (selection : α ↪ G) {M : ℕ}
    {H T κ C₀ ρ ξ : ℝ} (hH : 0 < H) (hT : 0 < T) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀)
    (hr : ∀ g, |(ker g : ℝ)| * T ≤ H) (hrC : ∀ g, |(ker g : ℝ)| ≤ C₀)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hwidth : ∀ i j, ((|c (.inr j)| : ℤ) + (allocatedPrincipalSides B U basis S j : ℤ) : ℝ) * T ≤
      ξ * physicalSpatialOutputScale α H T S.value i)
    (hscaleH : ρ ≤ H) (hscaleT : ρ ≤ T)
    (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ) :
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    ∀ v, |(∏ i, physicalSpatialOutputScale α H T S.value i) *
        (smoothMatrixImagePMF (physicalCubeCoefficient root dirs) (physicalSpatialInputScale vars H T)
          (physicalSpatialInputScale_pos vars hH hT) v).toReal -
      maskedIntegerImageDensity (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection) cols)
        (physicalSpatialOutputScale α H T S.value)
        (anisotropicSpatialKernelDensity selection ker (scalarCubeDifferenceMatrix x) hp H T S.value
          hH hT (Nat.cast_pos.mpr S.positive)) v| ≤
      anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M κ C₀ ρ ξ := by
  classical
  intro hp
  have hcols : ∀ i j, |(cols i j : ℝ)| * T ≤ ξ * physicalSpatialOutputScale α H T S.value i := by
    intro i j
    exact principalSpatialColumns_scaled_bound (fun j => c (.inr j)) id (fun _ => T)
      (fun _ => hT.le) (hwidth i) y i j
  rw [allocatedPhysicalCube_anisotropic_law B U basis S c x y hH hT]
  exact goodScalarKernelTuple_anisotropic_error S.positive selection x ker cols (fun _ => T)
    hH hT hκ hρ hx hC₀ hLC hr hrC (fun _ => hT) hξ0 hξ1 hcols hscaleH hscaleT
    (fun _ => hscaleT) hmesh

end VectorPolynomial
end Erdos3

end

end OAI
