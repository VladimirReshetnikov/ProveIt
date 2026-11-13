import DiophantineConsistency.Sign14PrefixDagFragments03

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def fragment020 : List Char := (include_str "fragment020.prefix").toList
theorem fragment020_eq : fragment020 = encode (Code.three) := by rfl

def fragment021 : List Char := (include_str "fragment021.prefix").toList
theorem fragment021_eq : fragment021 = encode ((Code.add (Code.var 14) (Code.one))) := by rfl

def fragment022 : List Char := (include_str "fragment022.prefix").toList
theorem fragment022_eq : fragment022 = encode ((Code.mul ((Code.add (Code.var 5) (Code.one))) ((Code.add (Code.var 5) (Code.one))))) := by rfl

def fragment023 : List Char := (include_str "fragment023.prefix").toList
theorem fragment023_eq : fragment023 = encode (Code.two) := by rfl

def fragment024 : List Char := (include_str "fragment024.prefix").toList
theorem fragment024_eq : fragment024 = encode ((Code.add (Code.var 6) (Code.one))) := by rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment020_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment021_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment022_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment023_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment024_eq
