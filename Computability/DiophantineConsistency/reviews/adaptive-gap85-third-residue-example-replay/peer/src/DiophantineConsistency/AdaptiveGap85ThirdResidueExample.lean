import DiophantineConsistency.AdaptiveGap85ThirdShift
set_option autoImplicit false
set_option maxRecDepth 100000
/-! Positive integer coordinate example; no literal zero is asserted. -/
namespace DiophantineConsistency.AdaptiveGap85ThirdResidueExample
open AdaptiveGap85ThirdShift
def ports : Fin 4 → ℤ := ![4,0,0,0]
def inputs : Fin 13 → ℤ := ![1,76,1,1,1,1,1,1,1,1,1,1,145]
theorem all_positive : ∀ i, 0<inputs i ∧ 0<(shift ports inputs 1) i := by decide
theorem coordinates :
    (shift ports inputs 1) 1=1 ∧ (shift ports inputs 1) 2=226 ∧
    (shift ports inputs 1) 5=1201 ∧ (shift ports inputs 1) 8=1351 ∧
    (shift ports inputs 1) 12=1 := by decide
theorem residue_escape : inputs 1%4=0 ∧ (shift ports inputs 1) 1%4=1 := by decide
end DiophantineConsistency.AdaptiveGap85ThirdResidueExample
