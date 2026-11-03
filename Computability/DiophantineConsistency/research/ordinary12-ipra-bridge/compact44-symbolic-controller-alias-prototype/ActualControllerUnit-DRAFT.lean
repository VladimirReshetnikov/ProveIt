import AliasControllerUnit

/-! Uncompiled bridge back to the actual symbolic parameterized kernel. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactSymbolicControllerActual
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPow
open DiophantineConsistency.ArithmeticConstructionUnitCompact44
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicKernelAliasExplicit
open CompactSymbolicControllerAlias
attribute [local irreducible] paramKernel rho

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem symbolic_gamma_unit (m e : V) :
    ∃ Γi, (Gamma (paramKernel rho : V) (power 581197 (m + 1)) (power 581197 e) * Γi) %
        (590069 * power 581197 (m + 1)) = 1 % (590069 * power 581197 (m + 1)) := by
  rw [← kernelAlias_eq]
  exact alias_gamma_unit m e

#print axioms symbolic_gamma_unit
end CompactSymbolicControllerActual
