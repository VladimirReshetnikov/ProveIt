import OAI.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Matrix

noncomputable def splitPhysicalSpatialInputScale (G N : Type*)
    (H T : ℝ) (Q : N → ℝ) : Option (G ⊕ N) → ℝ
  | none => H
  | some (.inl _) => T
  | some (.inr j) => Q j

theorem splitPhysicalSpatialInputScale_pos (G N : Type*)
    {H T : ℝ} {Q : N → ℝ} (hH : 0 < H) (hT : 0 < T) (hQ : ∀ j, 0 < Q j) :
    ∀ k, 0 < splitPhysicalSpatialInputScale G N H T Q k := by
  rintro (_ | (g | j))
  · exact hH
  · exact hT
  · exact hQ j

theorem splitPhysicalSpatialInputScale_reindex (G N : Type*)
    (H T : ℝ) (Q : N → ℝ) :
    splitPhysicalSpatialInputScale G N H T Q ∘ physicalSpatialSplitEquiv G N =
      Sum.elim (anisotropicSpatialScale G H T) Q := by
  funext j
  cases j with
  | inl j => cases j <;> rfl
  | inr j => rfl

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "principal" => PrincipalTupleIndex B (layerSamplerDegree I n)
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

theorem allocatedPhysicalCube_split_width_law {H T : ℝ}
    (Q : principal → ℝ) (hH : 0 < H) (hT : 0 < T) (hQ : ∀ j, 0 < Q j) :
    smoothMatrixImagePMF (physicalCubeCoefficient root dirs)
      (splitPhysicalSpatialInputScale G principal H T Q)
      (splitPhysicalSpatialInputScale_pos G principal hH hT hQ) =
      anisotropicSpatialOutputLaw ker (scalarCubeDifferenceMatrix x) cols H T Q hH hT hQ := by
  have h := smoothMatrixImagePMF_reindex (physicalCubeCoefficient root dirs)
    (physicalSpatialSplitEquiv G principal)
    (splitPhysicalSpatialInputScale G principal H T Q)
    (splitPhysicalSpatialInputScale_pos G principal hH hT hQ)
  rw [allocatedPhysicalCube_split] at h
  simpa only [splitPhysicalSpatialInputScale_reindex, anisotropicSpatialOutputLaw] using h.symm

variable [DecidableEq α] [DecidableEq G]

theorem allocatedPhysicalCube_narrow_error (selection : α ↪ G) {M : ℕ}
    {H T W κ C₀ ρ ξ : ℝ} (hH : 0 < H) (hT : 0 < T) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hWT : W * T ≤ H) (hWC : W ≤ C₀) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hscaleH : ρ ≤ H) (hscaleQ : ρ ≤ ξ * T)
    (hmesh : anisotropicSpatialMeshThreshold selection principal C₀ ≤ ρ) :
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    ∀ v, |(∏ i, physicalSpatialOutputScale α H T S.value i) *
        (smoothMatrixImagePMF (physicalCubeCoefficient root dirs)
          (splitPhysicalSpatialInputScale G principal H T (fun _ => ξ * T))
          (splitPhysicalSpatialInputScale_pos G principal hH hT (fun _ => mul_pos hξ hT)) v).toReal -
      maskedIntegerImageDensity (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection) cols)
        (physicalSpatialOutputScale α H T S.value)
        (anisotropicSpatialKernelDensity selection ker (scalarCubeDifferenceMatrix x) hp H T S.value
          hH hT (Nat.cast_pos.mpr S.positive)) v| ≤
      anisotropicSpatialError selection principal M κ C₀ ρ ξ := by
  classical
  intro hp
  have hrall (k) : |(root k : ℝ)| ≤ W :=
    (allocatedPhysicalCube_root_budget B U basis S c x y k).trans hbudget
  have hr (g) : |(ker g : ℝ)| * T ≤ H :=
    (mul_le_mul_of_nonneg_right (hrall (.inl g)) hT.le).trans hWT
  have hrC (g) : |(ker g : ℝ)| ≤ C₀ := (hrall (.inl g)).trans hWC
  have hcols : ∀ i j, |(cols i j : ℝ)| * (ξ * T) ≤
      ξ * physicalSpatialOutputScale α H T S.value i := by
    rintro (i | i) j
    · change |(root (.inr j) : ℝ)| * (ξ * T) ≤ ξ * H
      calc
        _ = ξ * (|(root (.inr j) : ℝ)| * T) := by ring
        _ ≤ ξ * H := mul_le_mul_of_nonneg_left
          ((mul_le_mul_of_nonneg_right (hrall (.inr j)) hT.le).trans hWT) hξ.le
    · change |(dirs i (.inr j) : ℝ)| * (ξ * T) ≤ ξ * ((S.value : ℝ) * T)
      calc
        _ ≤ (S.value : ℝ) * (ξ * T) := mul_le_mul_of_nonneg_right
          (allocatedPhysicalCube_directions_bound B U basis S x y i (.inr j)) (mul_pos hξ hT).le
        _ = _ := by ring
  have hscaleT : ρ ≤ T := hscaleQ.trans (mul_le_of_le_one_left hT.le hξ1)
  rw [allocatedPhysicalCube_split_width_law B U basis S c x y]
  exact goodScalarKernelTuple_anisotropic_error S.positive selection x ker cols (fun _ => ξ * T)
    hH hT hκ hρ hx hC₀ hLC hr hrC (fun _ => mul_pos hξ hT) hξ.le hξ1 hcols
    hscaleH hscaleT (fun _ => hscaleQ) hmesh

end VectorPolynomial
end Erdos3

end

end OAI
