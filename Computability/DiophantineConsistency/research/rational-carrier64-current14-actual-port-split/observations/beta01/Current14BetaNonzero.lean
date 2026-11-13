import DiophantineConsistency.CurrentKernelData2011
import Mathlib.Tactic.NormNum

/-! Nonzero fixed beta without expanding its large numeral. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.Current14BetaNonzero

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

#print axioms actual_beta_ne

end DiophantineConsistency.Current14BetaNonzero
