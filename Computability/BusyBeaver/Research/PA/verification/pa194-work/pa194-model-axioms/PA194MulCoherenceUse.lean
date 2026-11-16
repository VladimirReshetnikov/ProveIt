import PA194MulCoherenceRules
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulCoherence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def use {Γ : List Form} (x y b c r s : Nat)
    (hcoh : ND.Proof Γ (coherence (.fvar x)))
    (hy : ND.Proof Γ (Ordinal.domain (.fvar y)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hc : ND.Proof Γ (Ordinal.domain (.fvar c)))
    (hxy : ND.Proof Γ (orderIso (.fvar x) (.fvar y)))
    (hbc : ND.Proof Γ (orderIso (.fvar b) (.fvar c)))
    (hr : ND.Proof Γ (mulResult (.fvar x) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (mulResult (.fvar y) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  have premiseProof : ND.Proof Γ (premise (.fvar x) (.fvar y) (.fvar b) (.fvar c) (.fvar r) (.fvar s)) :=
    ND.andIntro hy (ND.andIntro hb (ND.andIntro hc (ND.andIntro hxy (ND.andIntro hbc (ND.andIntro hr hs)))))
  exact ND.mp premiseProof (atIndices x y b c r s hcoh)
#print axioms use
end PA194MulCoherence
