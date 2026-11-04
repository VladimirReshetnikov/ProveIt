import DiophantineConsistency.Compact44.CompactSymbolicPorts

/-! Project a compact port vector without evaluating its entries. -/
set_option autoImplicit false
set_option Elab.async false
namespace CompactGenericPortProjections
open CompactSymbolicPorts
theorem at_zero (β K L H : ℕ) : ports β K L H 0=β := by rfl
theorem at_one (β K L H : ℕ) : ports β K L H 1=K := by rfl
theorem at_two (β K L H : ℕ) : ports β K L H 2=L := by rfl
theorem at_three (β K L H : ℕ) : ports β K L H 3=β+H := by rfl
#print axioms CompactGenericPortProjections.at_zero
#print axioms CompactGenericPortProjections.at_one
#print axioms CompactGenericPortProjections.at_two
#print axioms CompactGenericPortProjections.at_three
end CompactGenericPortProjections
