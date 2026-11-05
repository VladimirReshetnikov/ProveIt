import Normalized106RationalSpecialization
import DiophantineConsistency.CurrentKernelData2011
import Mathlib.Tactic.NormNum

/-! Actual historical-provider current2011 ports, external evaluation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Normalized106RationalActual
open Normalized106Rational66 Normalized106RationalSpecialization
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

theorem actual_beta_ne : CurrentWindowCarry2011.ports 0 ≠ 0 := by
  change (CurrentMasks2011.beta : ℤ) ≠ 0
  have hr : 1 < CurrentMasks2011.radix := by
    unfold CurrentMasks2011.radix
    norm_num
  have hp : 1 < CurrentMasks2011.radix ^ 2011 := one_lt_pow₀ hr (by decide)
  have hn : 0 < CurrentMasks2011.beta := by
    unfold CurrentMasks2011.beta
    exact Nat.sub_pos_of_lt hp
  exact_mod_cast (ne_of_gt hn)

theorem actual_positive_zero_iff :
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      value66 (portsQ CurrentWindowCarry2011.ports) (inputQ v)
        ((CurrentWindowCarry2011.ports 3 : ℚ) / (CurrentWindowCarry2011.ports 0 : ℚ))
        ((CurrentWindowCarry2011.ports 2 : ℚ) - (CurrentWindowCarry2011.ports 3 : ℚ)) = 0) ↔
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      (ModelCarrierCurrent.expressionAt106 CurrentWindowCarry2011.ports).eval v = 0) :=
  positive_zero_iff CurrentWindowCarry2011.ports actual_beta_ne

#print axioms actual_beta_ne
#print axioms actual_positive_zero_iff

end DiophantineConsistency.Normalized106RationalActual
