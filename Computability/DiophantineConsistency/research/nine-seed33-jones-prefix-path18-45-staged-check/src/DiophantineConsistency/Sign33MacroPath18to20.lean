import DiophantineConsistency.Sign33MacroDependentOutput
import DiophantineConsistency.Sign33MacroPrefixEmbedding

/-! Candidate shared two-snoc path in the concrete named recipe. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroPath18to20
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixEmbedding

theorem path18_20 : PrefixPath d18 d20 (fun i => i.castSucc.castSucc) := by
  change PrefixPath d18 (Dag.snoc (Dag.snoc d18 _) _) _
  exact PrefixPath.step (PrefixPath.step (PrefixPath.base d18) _) _

theorem lookup18_20 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 18) :
    d20.values a i.castSucc.castSucc = d18.values a i := by
  exact lookup path18_20 a i

#print axioms path18_20
#print axioms lookup18_20
end DiophantineConsistency.Sign33MacroPath18to20
