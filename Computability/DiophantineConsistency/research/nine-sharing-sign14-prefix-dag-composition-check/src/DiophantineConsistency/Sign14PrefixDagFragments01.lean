import DiophantineConsistency.Sign14PrefixDagFragments00

/-! SOURCE-ONLY staged included-fragment encoding candidates. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixDag
open Sign14PrefixReflection Sign14PrefixCode
def fragment005 : List Char := (include_str "fragment005.prefix").toList
theorem fragment005_eq : fragment005 = encode ((Code.mul ((Code.add (Code.var 9) (Code.one))) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))) := by rfl

def fragment006 : List Char := (include_str "fragment006.prefix").toList
theorem fragment006_eq : fragment006 = encode ((Code.mul ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))) := by rfl

def fragment007 : List Char := (include_str "fragment007.prefix").toList
theorem fragment007_eq : fragment007 = encode ((Code.add ((Code.mul (Code.var 9) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))) ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))))) := by rfl

def fragment008 : List Char := (include_str "fragment008.prefix").toList
theorem fragment008_eq : fragment008 = encode ((Code.mul ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))) ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))))) := by rfl

def fragment009 : List Char := (include_str "fragment009.prefix").toList
theorem fragment009_eq : fragment009 = encode ((Code.mul ((Code.add (Code.port 2) ((Code.mul ((Code.add ((Code.mul (Code.port 0) ((Code.add (Code.var 1) (Code.one))))) (Code.one))) (Code.port 3))))) ((Code.add (Code.var 1) (Code.one))))) := by rfl

end DiophantineConsistency.Sign14PrefixDag
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment005_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment006_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment007_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment008_eq
#print axioms DiophantineConsistency.Sign14PrefixDag.fragment009_eq
