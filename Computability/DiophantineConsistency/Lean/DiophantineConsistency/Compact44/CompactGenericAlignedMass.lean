import DiophantineConsistency.ArithmeticWindowCarry
import Mathlib.Data.Fintype.BigOperators
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactGenericAlignedMass
open scoped BigOperators
abbrev Aligned (ι κ : Type*) := (ι ⊕ κ) ⊕ ((ι ⊕ κ) ⊕ Fin 5)
def bandCoeff {ι κ : Type*} (s : ι → ℕ) (c : κ → ℕ) : ι ⊕ κ → ℕ
  | .inl i => s i
  | .inr j => c j
def alignedCoeff {ι κ : Type*} (s : ι → ℕ) (c : κ → ℕ) : Aligned ι κ → ℕ
  | .inl i => bandCoeff s c i
  | .inr (.inl i) => bandCoeff s c i
  | .inr (.inr _) => 1

theorem sum_identity {ι κ : Type*} [Fintype ι] [Fintype κ] (s : ι → ℕ) (c : κ → ℕ) :
    (∑ i : Aligned ι κ, alignedCoeff s c i)+1 = 2*((∑ i,s i)+(∑ j,c j))+6 := by
  classical
  simp only [Fintype.sum_sum_type, alignedCoeff, bandCoeff]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring
#print axioms CompactGenericAlignedMass.sum_identity
end CompactGenericAlignedMass
