import DiophantineConsistency.CurrentClause2011
import CyclicFieldRefactor

/-! Check the four actual support exclusions in the clause and marker proofs. -/
namespace DiophantineConsistency.RefactorCyclicField

open CurrentMasks2011

variable {N : ℕ} [NeZero (N * 2011)]

theorem clause_bare_inputs_zero (c : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    c (b + 1005 - 18) = 0 ∧ c (b + 1005 - 2020) = 0 := by
  constructor
  · exact zero_outside_support (L := 2011) (by decide) lowSupport c hc b hb 1005 18
      (by norm_num [lowSupport_def])
  · exact zero_outside_support (L := 2011) (by decide) lowSupport c hc b hb 1005 2020
      (by norm_num [lowSupport_def])

theorem marker_bare_inputs_zero (c : ZMod (N * 2011) → ℕ)
    (hc : ∀ k, k.val % 2011 ∉ lowSupport → c k = 0)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    c (b + 1004 - 18) = 0 ∧ c (b + 1004 - 2020) = 0 := by
  constructor
  · exact zero_outside_support (L := 2011) (by decide) lowSupport c hc b hb 1004 18
      (by norm_num [lowSupport_def])
  · exact zero_outside_support (L := 2011) (by decide) lowSupport c hc b hb 1004 2020
      (by norm_num [lowSupport_def])

#print axioms clause_bare_inputs_zero
#print axioms marker_bare_inputs_zero

end DiophantineConsistency.RefactorCyclicField
