import DiophantineConsistency.Sign14PrefixDagFragments05

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def shared00Bytes : List Char := fragment000
theorem shared00Bytes_eq : shared00Bytes = encode Sign14PrefixCode.shared00 := by
  unfold shared00Bytes
  simp only [fragment000_eq] <;> rfl

def shared01Bytes : List Char := fragment001
theorem shared01Bytes_eq : shared01Bytes = encode Sign14PrefixCode.shared01 := by
  unfold shared01Bytes
  simp only [fragment001_eq] <;> rfl

def shared02Bytes : List Char := fragment002
theorem shared02Bytes_eq : shared02Bytes = encode Sign14PrefixCode.shared02 := by
  unfold shared02Bytes
  simp only [fragment002_eq] <;> rfl

def shared03Bytes : List Char := fragment003
theorem shared03Bytes_eq : shared03Bytes = encode Sign14PrefixCode.shared03 := by
  unfold shared03Bytes
  simp only [fragment003_eq] <;> rfl

def shared04Bytes : List Char := fragment004
theorem shared04Bytes_eq : shared04Bytes = encode Sign14PrefixCode.shared04 := by
  unfold shared04Bytes
  simp only [fragment004_eq] <;> rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.shared00Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared01Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared02Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared03Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared04Bytes_eq
