import PA194HXContracts
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194HXCoverageFirst

def blockCheck (base count : Nat) : Bool :=
  (List.range count).all (fun j => PA194HXContracts.checkAt (base+j))

theorem block0 : blockCheck 0 8 = true := by decide +kernel
theorem block8 : blockCheck 8 8 = true := by decide +kernel
theorem block16 : blockCheck 16 8 = true := by decide +kernel
theorem block24 : blockCheck 24 8 = true := by decide +kernel

#print axioms block0
#print axioms block8
#print axioms block16
#print axioms block24
end PA194HXCoverageFirst
