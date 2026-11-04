import DiophantineConsistency.Compact44.Compact943Data

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

/-! Exploratory finite coefficient-mass calculation for the retained table.
    This is not the all-model graph-to-carry application. -/
namespace CompactCoefficientMass

def value (t : Nat × Nat × Nat × Nat) : Nat :=
  t.1 + 2^8*t.2.1 + 2^17*t.2.2.1 + 2^25*t.2.2.2 + 127*2^34

def selector (t : Nat × Nat × Nat × Nat) : Nat := 1 + 2^10 * (2^41 - value t)

def selectorMass : Nat := (Compact943Data.rows.map selector).sum
def copyMass : Nat := ((List.range 41).map (fun j => 2^(10+j))).sum
def coefficientMass : Nat := selectorMass + copyMass
def stencilMass : Nat := 2*coefficientMass + 6

theorem values_in_range : Compact943Data.rows.all (fun t => decide (0 < value t ∧ value t < 2^41)) = true := by decide
theorem selector_mass_exact : selectorMass = 12734826094758831 := by decide
theorem copy_mass_exact : copyMass = 2251799813684224 := by decide
theorem coefficient_mass_exact : coefficientMass = 14986625908443055 := by
  rw [coefficientMass, selector_mass_exact, copy_mass_exact]
theorem stencil_mass_exact : stencilMass = 29973251816886116 := by
  rw [stencilMass, coefficient_mass_exact]
theorem triple_stencil_below_half : 3*stencilMass+1 < 2^66 := by
  rw [stencil_mass_exact]
  decide
theorem predecessor_slack : 3*stencilMass+1+2^66 < 2^67 := by
  rw [stencil_mass_exact]
  decide
theorem heterogeneous_mass_slack :
    3*stencilMass+(2^67-1)+1 ≤ 2*(2^67-1) := by
  rw [stencil_mass_exact]
  decide

end CompactCoefficientMass

#print axioms CompactCoefficientMass.values_in_range
#print axioms CompactCoefficientMass.selector_mass_exact
#print axioms CompactCoefficientMass.copy_mass_exact
#print axioms CompactCoefficientMass.coefficient_mass_exact
#print axioms CompactCoefficientMass.stencil_mass_exact
#print axioms CompactCoefficientMass.triple_stencil_below_half
#print axioms CompactCoefficientMass.predecessor_slack
#print axioms CompactCoefficientMass.heterogeneous_mass_slack
