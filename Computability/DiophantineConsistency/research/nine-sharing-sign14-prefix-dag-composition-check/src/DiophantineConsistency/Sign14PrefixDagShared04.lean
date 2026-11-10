import DiophantineConsistency.Sign14PrefixDagShared03

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def shared20Bytes : List Char := ('*' :: (shared18Bytes ++ fragment018))
theorem shared20Bytes_eq : shared20Bytes = encode Sign14PrefixCode.shared20 := by
  unfold shared20Bytes
  simp only [shared18Bytes_eq, fragment018_eq] <;> rfl

def shared21Bytes : List Char := ('+' :: (shared20Bytes ++ fragment015))
theorem shared21Bytes_eq : shared21Bytes = encode Sign14PrefixCode.shared21 := by
  unfold shared21Bytes
  simp only [shared20Bytes_eq, fragment015_eq] <;> rfl

def shared22Bytes : List Char := ('+' :: (shared15Bytes ++ shared11Bytes))
theorem shared22Bytes_eq : shared22Bytes = encode Sign14PrefixCode.shared22 := by
  unfold shared22Bytes
  simp only [shared15Bytes_eq, shared11Bytes_eq] <;> rfl

def shared23Bytes : List Char := ('+' :: (shared18Bytes ++ shared13Bytes))
theorem shared23Bytes_eq : shared23Bytes = encode Sign14PrefixCode.shared23 := by
  unfold shared23Bytes
  simp only [shared18Bytes_eq, shared13Bytes_eq] <;> rfl

def shared24Bytes : List Char := ('*' :: (fragment019 ++ shared23Bytes))
theorem shared24Bytes_eq : shared24Bytes = encode Sign14PrefixCode.shared24 := by
  unfold shared24Bytes
  simp only [fragment019_eq, shared23Bytes_eq] <;> rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.shared20Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared21Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared22Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared23Bytes_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.shared24Bytes_eq
