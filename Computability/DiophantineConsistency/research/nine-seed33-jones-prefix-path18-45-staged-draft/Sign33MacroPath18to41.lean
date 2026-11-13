import DiophantineConsistency.Sign33MacroPath18to34

/-! Candidate shared twenty-three-snoc path in the concrete named recipe. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroPath18to41
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixEmbedding Sign33MacroPath18to34

theorem path18_41 : PrefixPath d18 d41 (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  change PrefixPath d18 (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc d34 _) _) _) _) _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step path18_34 _) _) _) _) _) _) _)

theorem lookup18_41 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 18) :
    d41.values a i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc = d18.values a i := by
  exact lookup path18_41 a i

#print axioms path18_41
#print axioms lookup18_41
end DiophantineConsistency.Sign33MacroPath18to41
