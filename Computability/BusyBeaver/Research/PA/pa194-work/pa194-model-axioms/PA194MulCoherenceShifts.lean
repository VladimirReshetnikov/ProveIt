import PA194MulCoherenceUse
import PA194MulPredecessorFromPrefix
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulCoherence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulRecurrenceNew
attribute [local irreducible] addResult mulPrefix mulResult orderIso

def resultShift {Γ : List Form} (x base out : Nat)
    (h : ND.Proof Γ (mulResult (.fvar x) (.fvar base) (.fvar out))) :
    ND.Proof (ND.shifted Γ) (mulResult (.fvar (x+1)) (.fvar (base+1)) (.fvar (out+1))) := by
  convert ND.shiftProof h using 1
  simp [Semiformula.shift,mulResult_rew,Rew.shift,Rew.map]

def predecessorShift {Γ : List Form} (x base out : Nat)
    (h : ND.Proof Γ (predecessorResult (.fvar x) (.fvar base) (.fvar out))) :
    ND.Proof (ND.shifted Γ) (predecessorResult (.fvar (x+1)) (.fvar (base+1)) (.fvar (out+1))) := by
  convert ND.shiftProof h using 1 <;> (dsimp [predecessorResult] <;>
    simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Ordinal.domain_rew,mulResult_rew,addResult_rew,Rew.shift,Rew.q,Rew.func])
#print axioms resultShift
#print axioms predecessorShift
end PA194MulCoherence
