import DiophantineConsistency.Norm38MacroMValue

/-! Candidate d24-to-d27 shared prefix path. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointA
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixEmbedding

theorem path24_27 : PrefixPath d24 d27 (fun i => i.castSucc.castSucc.castSucc) := by
  change PrefixPath d24 (Dag.snoc (Dag.snoc (Dag.snoc d24 _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.base d24) _) _) _)

theorem lookup24_27 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 24) :
    d27.values a i.castSucc.castSucc.castSucc = d24.values a i := by
  exact lookup path24_27 a i

#print axioms path24_27
#print axioms lookup24_27
end DiophantineConsistency.Norm38MacroCheckpointA
