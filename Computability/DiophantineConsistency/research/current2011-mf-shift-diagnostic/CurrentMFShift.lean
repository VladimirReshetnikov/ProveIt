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

theorem cast_sum_from {a b x y : ℕ} (h : a = x) (k : b = y) :
    ((a + b : ℕ) : ℤ) = (x : ℤ) + (y : ℤ) := by
  rw [h, k]
  exact Nat.cast_add _ _

theorem shiftedValue_cast : (shiftedValue : ℤ) =
    (CurrentMasks2011.highPort : ℤ) + (CurrentMasks2011.beta : ℤ) :=
  cast_sum_from highPort_eq beta_eq

attribute [local irreducible] shiftedValue

theorem shiftedValue_eq_port : (shiftedValue : ℤ) = CurrentWindowCarry2011.ports 3 :=
  shiftedValue_cast.trans
    (Current14LiteralPortsMF.omega_eq.trans Current14LiteralPortsMF.all_ports.2.2.2.symm)

#print axioms shiftedValue_cast
#print axioms shiftedValue_eq_port
end DiophantineConsistency.CurrentMFShift
