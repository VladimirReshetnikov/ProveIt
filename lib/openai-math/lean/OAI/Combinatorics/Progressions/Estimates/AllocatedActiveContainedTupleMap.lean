import OAI.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

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
local notation "Output" => (Σ _a : Active, Unit)
local notation "sides" => allocatedPrincipalSides B U basis S

noncomputable def allocatedActiveContainedProgression
    (step H : Input → ℕ) (c : Input → ℤ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (v : ∀ j, IntegerScalarCubeBox Empty (H j)) :
    PrincipalAxisTuples (α := Empty) (fun a => ¬short a) sides :=
  fun j i => ⟨(containedProgressionCubeMap Empty S.value (H j) (step j) (c j)
    S.positive (hsubset j) (v j) i : ℤ), by
      simpa only [principalAxisLength, allocatedPrincipalSides_not_short B U basis S j.1 j.2]
        using (containedProgressionCubeMap Empty S.value (H j) (step j) (c j)
          S.positive (hsubset j) (v j) i).property⟩

theorem allocatedActiveContainedProgression_value
    (step H : Input → ℕ) (c : Input → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (v : ∀ j, IntegerScalarCubeBox Empty (H j))
    (hv : (FiniteProbabilityWeights.pi
      (fun j => integerScalarCubeWeights Empty (H j) (hH j))).weight v ≠ 0) (j : Input) :
    (allocatedActiveContainedProgression B U basis S step H c hsubset v j none : ℤ) =
      c j + (step j : ℤ) * (v j none : ℤ) := by
  have hb := integerScalarCubePi_root_bounds H hH v hv j
  have hc : IntegerScalarCube (H j) (fun i => (v j i : ℤ)) := by
    intro t
    have ht : t = ∅ := Subsingleton.elim _ _
    subst t
    simpa only [integerScalarCubeValue, Finset.sum_empty, add_zero] using
      (show 0 ≤ (v j none : ℤ) ∧ (v j none : ℤ) < (H j : ℤ) from ⟨hb.1, by have := hH j; omega⟩)
  simpa only [allocatedActiveContainedProgression, ite_true] using
    containedProgressionCubeMap_value Empty S.value (H j) (step j) (c j)
      S.positive (hsubset j) (v j) hc none

theorem allocatedOriginalSampleFullSliceMap_contained_physical
    (step H : Input → ℕ) (c : Input → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (v : ∀ j, IntegerScalarCubeBox Empty (H j))
    (hv : (FiniteProbabilityWeights.pi
      (fun j => integerScalarCubeWeights Empty (H j) (hH j))).weight v ≠ 0)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (u : PrincipalAxisTuples (α := Empty) short sides) :
    allocatedOriginalSampleFullSliceMap B U basis S x u
      (fun _ _ => 0) (fun _ _ => 1) sample
      (fun j => ((c j : ℝ) + (step j : ℝ) * (v j none : ℝ)) / S.value) =
      fun o : Output => allocatedFullMixedSiteValue (R := R) U basis
        (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x
          (principalAxisJoin short u
            (allocatedActiveContainedProgression B U basis S step H c hsubset v))) o.1.val := by
  have he (j : Input) :
      (allocatedActiveContainedProgression B U basis S step H c hsubset v j none : ℝ) =
      (c j : ℝ) + (step j : ℝ) * (v j none : ℝ) := by
    exact_mod_cast allocatedActiveContainedProgression_value B U basis S step H c hH hsubset v hv j
  simpa only [he] using allocatedOriginalSampleFullSliceMap_physical_join B U basis S sample x u
    (allocatedActiveContainedProgression B U basis S step H c hsubset v)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a))
  (fun a : Active => layerSamplerDegree I n (Subtype.val a))
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedActiveContainedTupleMap_eq
    (step H : Input → ℕ) (c : Input → ℤ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ)) :
    containedProgressionTupleMap (α := Empty)
      (fun a : Active => B (Subtype.val a)) (fun a : Active => layerSamplerDegree I n (Subtype.val a))
      (principalAxisLength (fun a => ¬short a) sides) H step c
      (fun j => allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩)
      (fun j => by
        simpa only [principalAxisLength, allocatedPrincipalSides_not_short B U basis S j.1 j.2]
          using hsubset j) =
      allocatedActiveContainedProgression B U basis S step H c hsubset := by
  funext v j i
  apply Subtype.ext
  simp only [containedProgressionTupleMap, allocatedActiveContainedProgression,
    containedProgressionCubeMap]
  split_ifs <;> rfl

end Erdos3.VectorPolynomial

end

end OAI
