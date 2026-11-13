import DiophantineConsistency.Sign14PrefixDagFragments01

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def fragment010 : List Char := (include_str "fragment010.prefix").toList
theorem fragment010_eq : fragment010 = encode ((Code.add ((Code.mul ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))) ((Code.add (Code.var 3) (Code.one))))) := by rfl

def fragment011 : List Char := (include_str "fragment011.prefix").toList
theorem fragment011_eq : fragment011 = encode ((Code.mul ((Code.add ((Code.add (Code.var 2) (Code.one))) ((Code.add (Code.var 3) (Code.one))))) ((Code.mul ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))))) := by rfl

def fragment012 : List Char := (include_str "fragment012.prefix").toList
theorem fragment012_eq : fragment012 = encode ((Code.mul ((Code.mul ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))) := by rfl

def fragment013 : List Char := (include_str "fragment013.prefix").toList
theorem fragment013_eq : fragment013 = encode ((Code.mul ((Code.add (Code.var 8) (Code.one))) ((Code.mul ((Code.mul ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))))) := by rfl

def fragment014 : List Char := (include_str "fragment014.prefix").toList
theorem fragment014_eq : fragment014 = encode ((Code.sub ((Code.add ((Code.mul ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))) ((Code.add (Code.var 3) (Code.one))))) ((Code.mul ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) ((Code.add (Code.var 2) (Code.one))))))) := by rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment010_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment011_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment012_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment013_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment014_eq
