import OAI.Combinatorics.Progressions.Estimates.AllocatedActiveContainedTupleMap
import OAI.Combinatorics.Progressions.Lattices.AllocatedOriginalSampleResidueMixtureForecast

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem containedProgressionCubePi_residue
    {G : Type*} [Fintype G] (L : ℕ) (hL : 0 < L)
    (H step : G → ℕ) (c : G → ℤ) (hH : ∀ g, 0 < H g)
    (hsubset : ∀ g, integerProgressionSupport (c g) (step g : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (L : ℤ))
    (x : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hx : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight x ≠ 0)
    (q : ℕ) :
    (fun g => ((containedProgressionCubeMap Empty L (H g) (step g) (c g)
      hL (hsubset g) (x g) none : ℤ) : ZMod q)) =
      fun g => ((c g + (step g : ℤ) * (x g none : ℤ) : ℤ) : ZMod q) := by
  funext g
  have hb := integerScalarCubePi_root_bounds H hH x hx g
  have hc : IntegerScalarCube (H g) (fun a => (x g a : ℤ)) := by
    intro row
    have he : row = ∅ := Subsingleton.elim _ _
    simp only [he, integerScalarCubeValue, Finset.sum_empty, add_zero]
    exact ⟨hb.1, by have := hH g; omega⟩
  rw [containedProgressionCubeMap_value Empty L (H g) (step g) (c g) hL (hsubset g) (x g) hc]
  rfl

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedActiveContainedProgression_residue_join
    (step H : Input → ℕ) (c : Input → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (v : ∀ j, IntegerScalarCubeBox Empty (H j))
    (hv : (FiniteProbabilityWeights.pi
      (fun j => integerScalarCubeWeights Empty (H j) (hH j))).weight v ≠ 0)
    (q : ℕ) (u : PrincipalAxisTuples (α := Empty) short sides) :
    principalResidueLabel q (principalAxisJoin short u
      (allocatedActiveContainedProgression B U basis S step H c hsubset v)) =
      allocatedPrincipalResidueJoin B U basis S q u
        (fun j => ((c j + (step j : ℤ) * (v j none : ℤ) : ℤ) : ZMod q)) := by
  rw [allocatedPrincipalResidueJoin_label_join]
  congr 1
  funext j
  rw [allocatedActiveContainedProgression_value B U basis S step H c hH hsubset v hv j]

end VectorPolynomial
end Erdos3

end

end OAI
