import DiophantineConsistency.Sign14PrefixDagShared00

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def shared05Bytes : List Char := fragment005
theorem shared05Bytes_eq : shared05Bytes = encode Sign14PrefixCode.shared05 := by
  unfold shared05Bytes
  simp only [fragment005_eq] <;> rfl

def shared06Bytes : List Char := fragment006
theorem shared06Bytes_eq : shared06Bytes = encode Sign14PrefixCode.shared06 := by
  unfold shared06Bytes
  simp only [fragment006_eq] <;> rfl

def shared07Bytes : List Char := fragment007
theorem shared07Bytes_eq : shared07Bytes = encode Sign14PrefixCode.shared07 := by
  unfold shared07Bytes
  simp only [fragment007_eq] <;> rfl

def shared08Bytes : List Char := fragment008
theorem shared08Bytes_eq : shared08Bytes = encode Sign14PrefixCode.shared08 := by
  unfold shared08Bytes
  simp only [fragment008_eq] <;> rfl

def shared09Bytes : List Char := fragment009
theorem shared09Bytes_eq : shared09Bytes = encode Sign14PrefixCode.shared09 := by
  unfold shared09Bytes
  simp only [fragment009_eq] <;> rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.shared05Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared06Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared07Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared08Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared09Bytes_eq
