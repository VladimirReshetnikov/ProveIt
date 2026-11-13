import DiophantineConsistency.Norm38MacroPath18to20

/-! Candidate shared nine-snoc path in the concrete named recipe. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroPath18to27
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixEmbedding Norm38MacroPath18to20

theorem path18_27 : PrefixPath d18 d27 (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  change PrefixPath d18 (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc d20 _) _) _) _) _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step path18_20 _) _) _) _) _) _) _)

theorem lookup18_27 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 18) :
    d27.values a i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc = d18.values a i := by
  exact lookup path18_27 a i

#print axioms path18_27
#print axioms lookup18_27
end DiophantineConsistency.Norm38MacroPath18to27
