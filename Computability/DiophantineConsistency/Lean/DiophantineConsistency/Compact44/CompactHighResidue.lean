import DiophantineConsistency.Compact44.CompactHighPopulation
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactHighResidue
open DiophantineConsistency
open CompactHighPopulation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticMaskConstants

private theorem prefix_mod_eight (l : List ℕ) :
    Nat.ofDigits (2^67) (4 :: l) % 8 = 4 := by
  rw [Nat.ofDigits_cons, Nat.add_mod, Nat.mul_mod]
  norm_num

theorem natural_mod_eight : (Nat.ofDigits (2^67) highDigits) % 8 = 4 := by
  have hd : highDigits = 4 :: highDigits.tail := by rfl
  have h := prefix_mod_eight highDigits.tail
  rw [← hd] at h
  exact h

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem model_mod_eight :
    ((Nat.ofDigits (2^67) highDigits : ℕ) : V) % 8 = 4 := by
  have h := cast_mod (V:=V) (Nat.ofDigits (2^67) highDigits) 8
  rw [natural_mod_eight] at h
  simpa only [Nat.cast_ofNat] using h.symm
end CompactHighResidue
#print axioms CompactHighResidue.natural_mod_eight
#print axioms CompactHighResidue.model_mod_eight
