import CurrentMFRecipe
import Current14LiteralPortsMF

/-! Isolate the exact once-beta shift and the existing port-3 projection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.CurrentMFShift
open CurrentMFRecipe
attribute [local irreducible] rho maskDigits CurrentMasks2011.radix
  CurrentMasks2011.highPort CurrentMasks2011.beta CurrentWindowCarry2011.ports
  Current14LiteralPortsMF.omega

def shiftedValue : ℕ := Nat.ofDigits rho maskDigits + (rho^2011 - 1)

theorem shiftedValue_cast : (shiftedValue : ℤ) =
    (CurrentMasks2011.highPort : ℤ) + (CurrentMasks2011.beta : ℤ) := by
  unfold shiftedValue
  rw [highPort_eq, beta_eq]
  exact Nat.cast_add _ _

attribute [local irreducible] shiftedValue

theorem shiftedValue_eq_port : (shiftedValue : ℤ) = CurrentWindowCarry2011.ports 3 :=
  shiftedValue_cast.trans
    (Current14LiteralPortsMF.omega_eq.trans Current14LiteralPortsMF.all_ports.2.2.2.symm)

#print axioms shiftedValue_cast
#print axioms shiftedValue_eq_port
end DiophantineConsistency.CurrentMFShift
