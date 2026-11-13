import CurrentMFRecipe
import Current14LiteralPortsMF

/-! Isolate substitution in naturals before addressing the port cast. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.CurrentMFNaturalSum
open CurrentMFRecipe
attribute [local irreducible] rho maskDigits CurrentMasks2011.radix
  CurrentMasks2011.highPort CurrentMasks2011.beta CurrentWindowCarry2011.ports

theorem natural_sum :
    Nat.ofDigits rho maskDigits + (rho ^ 2011 - 1) =
      CurrentMasks2011.highPort + CurrentMasks2011.beta :=
  congrArg₂ (fun x y : ℕ => x + y) highPort_eq beta_eq

#print axioms natural_sum
end DiophantineConsistency.CurrentMFNaturalSum
