import DiophantineConsistency.Sign14PrefixCodeRow04

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def fragment000 : List Char := (include_str "fragment000.prefix").toList
theorem fragment000_eq : fragment000 = encode ((Code.mul ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))) (Code.port 3))) := by rfl

def fragment001 : List Char := (include_str "fragment001.prefix").toList
theorem fragment001_eq : fragment001 = encode ((Code.mul ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) ((Code.add (Code.var 2) (Code.one))))) := by rfl

def fragment002 : List Char := (include_str "fragment002.prefix").toList
theorem fragment002_eq : fragment002 = encode ((Code.mul (Code.var 9) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))) := by rfl

def fragment003 : List Char := (include_str "fragment003.prefix").toList
theorem fragment003_eq : fragment003 = encode ((Code.sub ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) ((Code.add (Code.var 2) (Code.one))))) := by rfl

def fragment004 : List Char := (include_str "fragment004.prefix").toList
theorem fragment004_eq : fragment004 = encode ((Code.add (Code.port 2) ((Code.mul ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))) (Code.port 3))))) := by rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment000_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment001_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment002_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment003_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment004_eq
