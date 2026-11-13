import DiophantineConsistency.Sign14PrefixDagFragments04

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def fragment025 : List Char := (include_str "fragment025.prefix").toList
theorem fragment025_eq : fragment025 = encode (Code.one) := by rfl

def fragment026 : List Char := (include_str "fragment026.prefix").toList
theorem fragment026_eq : fragment026 = encode ((Code.add ((Code.mul ((Code.add (Code.port 1) ((Code.add (Code.var 9) (Code.one))))) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))) := by rfl

def fragment027 : List Char := (include_str "fragment027.prefix").toList
theorem fragment027_eq : fragment027 = encode ((Code.add ((Code.add ((Code.mul ((Code.add (Code.port 1) ((Code.add (Code.var 9) (Code.one))))) ((Code.add ((Code.add (Code.var 2) (Code.one))) ((Code.add (Code.var 3) (Code.one))))))) ((Code.add (Code.var 2) (Code.one))))) ((Code.mul ((Code.add (Code.var 4) (Code.one))) ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))))))) := by rfl

def fragment028 : List Char := (include_str "fragment028.prefix").toList
theorem fragment028_eq : fragment028 = encode ((Code.mul ((Code.add (Code.var 13) (Code.one))) ((Code.add (Code.var 13) (Code.one))))) := by rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment025_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment026_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment027_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment028_eq
