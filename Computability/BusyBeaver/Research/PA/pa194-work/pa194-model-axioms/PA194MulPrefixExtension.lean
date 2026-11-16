import PA194MulRecurrenceFull
import PA194FoundationAdditionFrame
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def prefixExtension {Γ : List Form} (E : FormulaEquality Γ)
    (top u base z g c v h : Nat)
    (htop : ND.Proof Γ (Ordinal.domain (.fvar top)))
    (hu : ND.Proof Γ (Ordinal.domain (.fvar u)))
    (hv : ND.Proof Γ (Ordinal.domain (.fvar v)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hp : ND.Proof Γ (mulPrefix (.fvar top) (.fvar base) (.fvar z) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar top) (.fvar c)))
    (ha : ND.Proof Γ (addResult (.fvar c) (.fvar base) (.fvar v)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar u) (.fvar v))) :
    ND.Proof Γ (mulPrefix (.fvar u) (.fvar base) (.fvar z) (.fvar h)) := by
  have oldDomain := ND.andLeft hp
  have oldFunctional := ND.andLeft (ND.andRight hp)
  have oldRange := ND.andLeft (ND.andRight (ND.andRight hp))
  have oldZero := ND.andLeft (ND.andRight (ND.andRight (ND.andRight hp)))
  have oldRecurrence := ND.andRight (ND.andRight (ND.andRight (ND.andRight hp)))
  have hd := successorGraphDomain E top u v g h hs oldDomain hx
  have hf := successorFunctional E top u v g h htop hs oldDomain oldFunctional hx
  have hr := graphRangeExtension E g h u v oldRange hx hv
  have hz := exactPreservesEdge g h u v z z hx oldZero
  have hrec := extension E top u c v g h base ⟨hu,hs,he,hx,ha,oldRecurrence⟩
  exact ND.andIntro hd (ND.andIntro hf (ND.andIntro hr (ND.andIntro hz hrec)))
#print axioms prefixExtension
end PA194MulRecurrenceNew
