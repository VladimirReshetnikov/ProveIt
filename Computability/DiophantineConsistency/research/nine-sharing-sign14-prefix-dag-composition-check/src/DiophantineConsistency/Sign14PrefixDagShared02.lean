import DiophantineConsistency.Sign14PrefixDagShared01

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def shared10Bytes : List Char := fragment010
theorem shared10Bytes_eq : shared10Bytes = encode Sign14PrefixCode.shared10 := by
  unfold shared10Bytes
  simp only [fragment010_eq] <;> rfl

def shared11Bytes : List Char := fragment011
theorem shared11Bytes_eq : shared11Bytes = encode Sign14PrefixCode.shared11 := by
  unfold shared11Bytes
  simp only [fragment011_eq] <;> rfl

def shared12Bytes : List Char := fragment012
theorem shared12Bytes_eq : shared12Bytes = encode Sign14PrefixCode.shared12 := by
  unfold shared12Bytes
  simp only [fragment012_eq] <;> rfl

def shared13Bytes : List Char := fragment013
theorem shared13Bytes_eq : shared13Bytes = encode Sign14PrefixCode.shared13 := by
  unfold shared13Bytes
  simp only [fragment013_eq] <;> rfl

def shared14Bytes : List Char := fragment014
theorem shared14Bytes_eq : shared14Bytes = encode Sign14PrefixCode.shared14 := by
  unfold shared14Bytes
  simp only [fragment014_eq] <;> rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.shared10Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared11Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared12Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared13Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared14Bytes_eq
