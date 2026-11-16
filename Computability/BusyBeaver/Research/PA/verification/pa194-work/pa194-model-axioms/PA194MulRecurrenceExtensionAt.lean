import PA194MulRecurrenceAt
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def extensionAt {Γ : List Form} (E : FormulaEquality Γ)
    (top u c v g h base x y z : Nat)
    (hu : ND.Proof Γ (Ordinal.domain (.fvar u)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hend : ND.Proof Γ (edge (.fvar g) (.fvar top) (.fvar c)))
    (hext : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar u) (.fvar v)))
    (hadd : ND.Proof Γ (addResult (.fvar c) (.fvar base) (.fvar v)))
    (hrec : ND.Proof Γ (mulRecurrence (.fvar g) (.fvar base)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y)))
    (hzx : ND.Proof Γ (Ordinal.successor (.fvar z) (.fvar x))) :
    ND.Proof Γ (mulPrevious (.fvar h) (.fvar base) (.fvar z) (.fvar y)) := by
  have hc := ND.mp he (ND.andLeft (exactAt g h u v x y hext))
  apply ND.orElim hc
  · let q : Form := edge (.fvar g) (.fvar x) (.fvar y)
    have prev := recurrenceAt g base x y z (ND.up hrec q) (ND.assumption (by simp [q])) (ND.up hzx q)
    exact preservePrevious g h u v base z y (ND.up hext q) prev
  · let q : Form := eq (.fvar x) (.fvar u) ⋏ eq (.fvar y) (.fvar v)
    have hp : ND.Proof (q::Γ) q := ND.assumption (by simp)
    let inc : ∀ p, p ∈ Γ → p ∈ q::Γ := fun p hp => List.mem_cons_of_mem q hp
    exact newCase (E.weaken inc) top u c v g h base x y z (ND.up hu q) (ND.up hs q)
      (ND.up hend q) (ND.up hext q) (ND.up hadd q) (ND.andLeft hp) (ND.andRight hp) (ND.up hzx q)
#print axioms extensionAt
end PA194MulRecurrenceNew
