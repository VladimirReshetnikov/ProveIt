import PA194ForwardReflProof
import PA194OrderIsoZero
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ForwardZeroSucc
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

def zeroSuccFalse (a b : Nat) (E : FormulaEquality Γ)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar b))) : ND.Proof Γ ⊥ := by
  have he : ND.Proof Γ (eq (.fvar a) (.fvar a)) := E.reflexive (.fvar a)
  have hm : ND.Proof Γ (mem (.fvar b) (.fvar a)) :=
    ND.mp (ND.orRight he) (ND.andRight (Ordinal.successorAt a b a hs))
  exact ND.contradiction hm (Ordinal.zeroNotMem b a hz)

def zeroIsoSuccFalse (a b c : Nat) (E : FormulaEquality Γ)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar c) (.fvar b))) : ND.Proof Γ ⊥ :=
  zeroSuccFalse c b E (zeroFromIso a b hz hi) hs
#print axioms zeroSuccFalse
#print axioms zeroIsoSuccFalse
end PA194ForwardZeroSucc
