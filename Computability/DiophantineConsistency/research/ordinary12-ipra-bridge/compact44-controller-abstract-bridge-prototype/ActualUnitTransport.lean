import AliasUnitDischarged

/-! Uncompiled explicit transport back to the actual symbolic kernel. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactActualUnitTransport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPow
open DiophantineConsistency.ArithmeticConstructionUnitCompact44
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicKernelAliasExplicit
open CompactAliasUnitDischarged
attribute [local irreducible] paramKernel rho

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem actual_unit (m e : V) :
    ∃ Γi, (Gamma (paramKernel rho : V) (power 581197 (m + 1)) (power 581197 e) * Γi) %
        (590069 * power 581197 (m + 1)) = 1 % (590069 * power 581197 (m + 1)) := by
  exact (congrArg (fun k : ℕ => ∃ Γi,
    (Gamma (k : V) (power 581197 (m + 1)) (power 581197 e) * Γi) %
      (590069 * power 581197 (m + 1)) = 1 % (590069 * power 581197 (m + 1)))
    kernelAlias_eq).mp (alias_unit m e)

#print axioms actual_unit
end CompactActualUnitTransport
