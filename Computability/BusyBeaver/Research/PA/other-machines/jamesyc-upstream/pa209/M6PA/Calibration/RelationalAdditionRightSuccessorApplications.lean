module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRightSuccessorSupplier
@[expose] public section

/-! Arbitrary-parameter specialization with the exact iso(v,s) orientation. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000

def additionRightSuccessorApply {Γ : List Form} (x b c r s v : Nat)
    (h : ND.Proof Γ addRightSuccessorStatement)
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hc : ND.Proof Γ (Ordinal.domain (.fvar c)))
    (hr : ND.Proof Γ (Ordinal.domain (.fvar r)))
    (hbc : ND.Proof Γ (Ordinal.successor (.fvar b) (.fvar c)))
    (hl : ND.Proof Γ (addResult (.fvar x) (.fvar b) (.fvar r)))
    (ht : ND.Proof Γ (addResult (.fvar x) (.fvar c) (.fvar s)))
    (hrv : ND.Proof Γ (Ordinal.successor (.fvar r) (.fvar v))) :
    ND.Proof Γ (orderIso (.fvar v) (.fvar s)) := by
  have hh : ND.Proof Γ (Ordinal.domain (.fvar x) 🡒 addRightSuccessor (.fvar x)) := by
    convert allElim _ (.fvar x) h using 1 <;>
      ((try simp only [addRightSuccessorStatement]) <;> addRightSuccessorSyntax)
  exact mp (andIntro hb (andIntro hc (andIntro hr (andIntro hbc (andIntro hl (andIntro ht hrv))))))
    (addRightSuccessorAt x b c r s v (mp hx hh))

#print axioms additionRightSuccessorApply
end M6.PA.RelationalSource.PairGraph
