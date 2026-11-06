import DiophantineConsistency.Norm38MacroUYInputs

/-! Candidate d20-to-d27 shared prefix path. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointUY
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixEmbedding

theorem path20_27 : PrefixPath d20 d27 (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  change PrefixPath d20 (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc d20 _) _) _) _) _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.base d20) _) _) _) _) _) _) _)

theorem lookup20_27 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 20) :
    d27.values a i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc = d20.values a i := by
  exact lookup path20_27 a i

#print axioms path20_27
#print axioms lookup20_27
end DiophantineConsistency.Norm38MacroCheckpointUY
