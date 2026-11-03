import DirectBFSSymbolicKernel

/-! Kernel-checked coefficient mass bounds for the direct-BFS table. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 20000000
namespace DirectBFSCoefficientMass

def selectorMass : Nat := (DirectBFSSymbolicKernel.rows.map CompactCoefficientMass.selector).sum
def copyMass : Nat := ((List.range 41).map (fun j => 2^(10+j))).sum
def coefficientMass : Nat := selectorMass+copyMass
def stencilMass : Nat := 2*coefficientMass+6

theorem values_in_range : DirectBFSSymbolicKernel.rows.all
    (fun t => decide (0<CompactCoefficientMass.value t ∧ CompactCoefficientMass.value t<2^41))=true := by decide

theorem selector_mass_exact : selectorMass=12777109108488111 := by decide
theorem copy_mass_exact : copyMass=2251799813684224 := by decide
theorem coefficient_mass_exact : coefficientMass=15028908922172335 := by
  rw [coefficientMass,selector_mass_exact,copy_mass_exact]
theorem stencil_mass_exact : stencilMass=30057817844344676 := by
  rw [stencilMass,coefficient_mass_exact]
theorem triple_stencil_below_half : 3*stencilMass+1<2^66 := by
  rw [stencil_mass_exact]
  decide
theorem predecessor_slack : 3*stencilMass+1+2^66<2^67 := by
  rw [stencil_mass_exact]
  decide
theorem heterogeneous_mass_slack : 3*stencilMass+(2^67-1)+1≤2*(2^67-1) := by
  rw [stencil_mass_exact]
  decide

#print axioms DirectBFSCoefficientMass.values_in_range
#print axioms DirectBFSCoefficientMass.selector_mass_exact
#print axioms DirectBFSCoefficientMass.triple_stencil_below_half
#print axioms DirectBFSCoefficientMass.heterogeneous_mass_slack
end DirectBFSCoefficientMass
