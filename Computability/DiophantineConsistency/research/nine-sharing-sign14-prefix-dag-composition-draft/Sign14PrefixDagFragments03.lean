import DiophantineConsistency.Sign14PrefixDagFragments02

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def fragment015 : List Char := (include_str "fragment015.prefix").toList
theorem fragment015_eq : fragment015 = encode ((Code.add ((Code.add (Code.var 11) (Code.one))) ((Code.add (Code.var 12) (Code.one))))) := by rfl

def fragment016 : List Char := (include_str "fragment016.prefix").toList
theorem fragment016_eq : fragment016 = encode ((Code.add (Code.var 11) (Code.one))) := by rfl

def fragment017 : List Char := (include_str "fragment017.prefix").toList
theorem fragment017_eq : fragment017 = encode ((Code.add (Code.var 7) (Code.one))) := by rfl

def fragment018 : List Char := (include_str "fragment018.prefix").toList
theorem fragment018_eq : fragment018 = encode ((Code.add (Code.var 10) (Code.one))) := by rfl

def fragment019 : List Char := (include_str "fragment019.prefix").toList
theorem fragment019_eq : fragment019 = encode (Code.four) := by rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment015_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment016_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment017_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment018_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment019_eq
