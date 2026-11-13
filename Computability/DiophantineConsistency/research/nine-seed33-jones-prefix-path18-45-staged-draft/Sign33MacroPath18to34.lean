import DiophantineConsistency.Sign33MacroPath18to27

/-! Candidate shared sixteen-snoc path in the concrete named recipe. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroPath18to34
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixEmbedding Sign33MacroPath18to27

theorem path18_34 : PrefixPath d18 d34 (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  change PrefixPath d18 (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc d27 _) _) _) _) _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step path18_27 _) _) _) _) _) _) _)

theorem lookup18_34 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 18) :
    d34.values a i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc = d18.values a i := by
  exact lookup path18_34 a i

#print axioms path18_34
#print axioms lookup18_34
end DiophantineConsistency.Sign33MacroPath18to34
