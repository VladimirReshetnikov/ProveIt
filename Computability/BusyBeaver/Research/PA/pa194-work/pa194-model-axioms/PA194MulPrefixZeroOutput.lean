import PA194MulOutputEndpoint
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def prefixZeroOutput {Γ : List Form} (E : FormulaEquality Γ) (x base e g out : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (hp : ND.Proof Γ (mulPrefix (.fvar x) (.fvar base) (.fvar e) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar out))) :
    ND.Proof Γ (eq (.fvar out) (.fvar e)) := by
  have domain := ND.andLeft hp
  have functional := ND.andLeft (ND.andRight hp)
  have zeroEdge := ND.andLeft (ND.andRight (ND.andRight (ND.andRight hp)))
  have cases := ND.mp (outputIntro g e e zeroEdge) (ND.andLeft (graphDomainAt x g e domain))
  have equality : ND.Proof Γ (eq (.fvar e) (.fvar x)) := by
    apply ND.orElim cases
    · exact ND.botElim (ND.contradiction (ND.assumption (by simp)) (ND.up (Ordinal.zeroNotMem x e hz) _))
    · exact ND.assumption (by simp)
  exact graphFunctionalAt g x out e functional he (edgeInputTransport E g e x e equality zeroEdge)
#print axioms prefixZeroOutput
end PA194MulRecurrenceNew
