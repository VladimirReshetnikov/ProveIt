import DiophantineConsistency.Norm38MacroKValue

/-! Candidate shared P/K birth-to-d27 paths. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointA0
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixEmbedding

theorem path22_27 : PrefixPath d22 d27 (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  change PrefixPath d22 (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc d22 _) _) _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.base d22) _) _) _) _) _)

theorem lookup22_27 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 22) :
    d27.values a i.castSucc.castSucc.castSucc.castSucc.castSucc = d22.values a i := lookup path22_27 a i

theorem path23_27 : PrefixPath d23 d27 (fun i => i.castSucc.castSucc.castSucc.castSucc) := by
  change PrefixPath d23 (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc d23 _) _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.base d23) _) _) _) _)

theorem lookup23_27 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 23) :
    d27.values a i.castSucc.castSucc.castSucc.castSucc = d23.values a i := lookup path23_27 a i

#print axioms path22_27
#print axioms lookup22_27
#print axioms path23_27
#print axioms lookup23_27
end DiophantineConsistency.Norm38MacroCheckpointA0
