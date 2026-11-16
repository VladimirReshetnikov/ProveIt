import PA194MulCoherenceSyntax
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulCoherence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194MulRecurrenceNew

def zeroPoint {Γ : List Form} (E : FormulaEquality Γ) (x y b c r s : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x))) :
    ND.Proof Γ (point (.fvar x) (.fvar y) (.fvar b) (.fvar c) (.fvar r) (.fvar s)) := by
  unfold point
  apply ND.impIntro
  let q : Form := premise (.fvar x) (.fvar y) (.fvar b) (.fvar c) (.fvar r) (.fvar s)
  have hq : ND.Proof (q::Γ) q := ND.assumption (by simp)
  have hh := ND.andRight (ND.andRight (ND.andRight hq))
  have iso := ND.andLeft hh
  have rest := ND.andRight (ND.andRight hh)
  have left := ND.andLeft rest
  have right := ND.andRight rest
  let inc : ∀ p, p ∈ Γ → p ∈ q::Γ := fun p hp => List.mem_cons_of_mem q hp
  exact zeroCoherence (E.weaken inc) x y b c r s (ND.up hz q) iso left right
#print axioms zeroPoint
end PA194MulCoherence
