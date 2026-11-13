import DiophantineConsistency.CompactIndexedMass
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactIndexedFlatten
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open CompactGenericAlignedMass
variable {V ι κ : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable [Fintype ι] [Fintype κ]

def offsets (es₀ es₁ : ι → V) (ec₀ ec₁ : κ → V) (eb : Fin 5 → V) :
    Aligned ι κ → V
  | .inl (.inl i) => es₀ i
  | .inl (.inr j) => ec₀ j
  | .inr (.inl (.inl i)) => es₁ i
  | .inr (.inl (.inr j)) => ec₁ j
  | .inr (.inr i) => eb i

theorem flatten (s : ι → ℕ) (c : κ → ℕ)
    (es₀ es₁ : ι → V) (ec₀ ec₁ : κ → V) (eb : Fin 5 → V) (r : V → V) :
    (∑ x : Aligned ι κ, (alignedCoeff s c x : V) * r (offsets es₀ es₁ ec₀ ec₁ eb x)) =
      ((∑ i, (s i : V) * r (es₀ i)) + (∑ j, (c j : V) * r (ec₀ j))) +
      ((∑ i, (s i : V) * r (es₁ i)) + (∑ j, (c j : V) * r (ec₁ j))) +
      (∑ i, r (eb i)) := by
  simp only [Fintype.sum_sum_type, alignedCoeff, bandCoeff, offsets, Nat.cast_one, one_mul, add_assoc]

/-- A split-band modular hypothesis gives the same congruence for the flattened family. -/
theorem flatten_congr (s : ι → ℕ) (c : κ → ℕ)
    (es₀ es₁ : ι → V) (ec₀ ec₁ : κ → V) (eb : Fin 5 → V) (r : V → V)
    (T M F : V)
    (h : (((∑ i, (s i : V) * r (es₀ i)) + (∑ j, (c j : V) * r (ec₀ j))) +
      ((∑ i, (s i : V) * r (es₁ i)) + (∑ j, (c j : V) * r (ec₁ j))) +
      (∑ i, r (eb i)) + T) % M = F) :
    ((∑ x : Aligned ι κ, (alignedCoeff s c x : V) * r (offsets es₀ es₁ ec₀ ec₁ eb x)) + T) % M = F := by
  rw [flatten]
  exact h
#print axioms CompactIndexedFlatten.flatten
#print axioms CompactIndexedFlatten.flatten_congr
end CompactIndexedFlatten
