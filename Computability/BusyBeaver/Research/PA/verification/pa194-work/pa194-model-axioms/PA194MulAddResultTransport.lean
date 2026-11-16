import PA194MulZeroExistence
import PA194FoundationFormulaCongruence
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulAddResultTransport
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def outputTransport {Γ : List Form} (E : FormulaEquality Γ) (x base a b : Nat)
    (hab : ND.Proof Γ (eq (.fvar a) (.fvar b)))
    (h : ND.Proof Γ (addResult (.fvar x) (.fvar base) (.fvar a))) :
    ND.Proof Γ (addResult (.fvar x) (.fvar base) (.fvar b)) := by
  let p : Ordinal.Formula 1 := addResult (.fvar x) (.fvar base) (.bvar 0)
  have h' : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar a]) p) := by
    simpa [p,addResult_rew,Rew.subst,Rew.q,Rew.func] using h
  have out := E.substituteOne p (.fvar a) (.fvar b) hab h'
  simpa [p,addResult_rew,Rew.subst,Rew.q,Rew.func] using out
#print axioms outputTransport
end PA194MulAddResultTransport
