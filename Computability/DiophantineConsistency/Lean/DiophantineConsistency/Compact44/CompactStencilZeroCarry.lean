import DiophantineConsistency.Compact44.CompactBooleanZeroCarry
import DiophantineConsistency.Compact44.CompactConcreteIndexedMass
import DiophantineConsistency.Compact44.GenericBandCarryFamily

/-! Specialize zero carry to the actual compact stencil coefficient mass. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactStencilZeroCarry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency
open ArithmeticStandardCasts ArithmeticWindowDigits CompactHeterogeneousCarry
open CompactGenericAlignedMass CompactConcreteIndexedMass CompactBooleanZeroCarry
attribute [local irreducible] Compact943Data.rows selectors copies

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

abbrev Idx := Aligned (Fin 943) (Fin 41) ⊕ Unit
def coeff : Idx → V :=
  GenericBandCarryFamily.coefficient (fun i : Aligned (Fin 943) (Fin 41) =>
    (alignedCoeff selectors copies i : V))

/-- The two reflected bands, bare rotations and temporal term have exactly
the checked finite stencil mass. -/
theorem coeff_mass : (∑ i, coeff i) = (CompactCoefficientMass.stencilMass : V) := by
  have hn := CompactConcreteIndexedMass.concrete_mass
  have hv : ((∑ i : Aligned (Fin 943) (Fin 41), alignedCoeff selectors copies i : ℕ) : V) + 1 =
      (CompactCoefficientMass.stencilMass : V) := by exact_mod_cast hn
  unfold coeff
  rw [Fintype.sum_sum_type]
  simp only [GenericBandCarryFamily.coefficient, Fintype.sum_unique]
  rw [← Nat.cast_sum]
  exact hv

theorem stencil_mass_room :
    (CompactCoefficientMass.stencilMass : V) + 1 ≤ Exp.exp (67 : V) - 1 := by
  have hn : CompactCoefficientMass.stencilMass + 2 ≤ 2^67 := by
    rw [CompactCoefficientMass.stencil_mass_exact]
    decide
  have hv : (CompactCoefficientMass.stencilMass : V) + 2 ≤ ((2^67 : ℕ) : V) := by
    exact_mod_cast hn
  rw [← cast_exp (V := V) 67] at hv
  have he : Exp.exp (67 : V) - 1 + 1 = Exp.exp 67 :=
    tsub_add_cancel_of_le (one_le_exp _)
  apply (add_le_add_iff_right 1).mp
  calc
    ((CompactCoefficientMass.stencilMass : V) + 1) + 1 =
        (CompactCoefficientMass.stencilMass : V) + 2 := by ring
    _ ≤ Exp.exp 67 := hv
    _ = (Exp.exp 67 - 1) + 1 := he.symm

/-- If every actual stencil source word is Boolean, its cyclic carry is zero
and every output digit is the exact raw column, without a carry term. -/
theorem stencil_zero_carry {n F b : V} {D X : Idx → V}
    (h : CarryInput 67 n F b D coeff X)
    (hbool : ∀ i, ∀ k < n, dig 67 (X i) k ≤ 1) :
    ∀ k < n, carry 67 n coeff X k = 0 ∧ dig 67 F k = raw 67 coeff X k := by
  apply boolean_zero_carry h hbool
  rw [coeff_mass]
  exact stencil_mass_room

#print axioms CompactStencilZeroCarry.coeff_mass
#print axioms CompactStencilZeroCarry.stencil_mass_room
#print axioms CompactStencilZeroCarry.stencil_zero_carry
end CompactStencilZeroCarry
