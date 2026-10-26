import DiophantineConsistency.DecimalMachine215

namespace DiophantineConsistency.DecimalMachine215Checks

open DecimalMachine215
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 1024

example : 10 ^ 714 ≤ seed ∧ seed < 10 ^ 715 := by decide +kernel
example : sigma 430 = 214 := by decide +kernel
example : tally 215 = 71 := by decide +kernel
example : action 0 = (true, true, 1) := by decide +kernel
example : (stateEquiv 1).val = 93 := stateEquiv_one
example : rawTarget 125 = -1 := by decide +kernel
example : target 125 = 215 := by decide +kernel
example : (rawTarget 125).toNat ≠ target 125 := by decide +kernel

#print axioms action_conjugacy
#print axioms blank_halts_iff_dense

end DiophantineConsistency.DecimalMachine215Checks
