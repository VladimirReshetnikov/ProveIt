import DiophantineConsistency.Norm38MacroUYValues

/-! Candidate d21-to-d27 shared prefix path. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointM
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixEmbedding

theorem path21_27 : PrefixPath d21 d27 (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  change PrefixPath d21 (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc d21 _) _) _) _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.base d21) _) _) _) _) _) _)

theorem lookup21_27 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 21) :
    d27.values a i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc = d21.values a i := by
  exact lookup path21_27 a i

#print axioms path21_27
#print axioms lookup21_27
end DiophantineConsistency.Norm38MacroCheckpointM
