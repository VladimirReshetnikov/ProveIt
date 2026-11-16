module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationRecurrenceNew
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
set_option maxHeartbeats 600000
attribute [local irreducible] addResult addPrefix mulPrefix

def mulRecurrenceExtensionAt {Γ : List Form} (E : FormulaEquality Γ)
    (top u c v g h base x y z : Nat) (I : MulRecurrenceInputs Γ top u c v g h base)
    (he : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar z) (.fvar x))) :
    ND.Proof Γ (mulPrevious (.fvar h) (.fvar base) (.fvar z) (.fvar y)) := by
  have hc := mp he (andLeft (exactAt g h u v x y I.extension))
  apply orElim hc
  · let q : Form := edge (.fvar g) (.fvar x) (.fvar y)
    have prev := mulRecurrenceAt g base x y z (up I.recurrence q) (assumption (by simp [q])) (up hs q)
    exact mulPreservePrevious g h u v base z y (up I.extension q) prev
  · let q : Form := eq (.fvar x) (.fvar u) ⋏ eq (.fvar y) (.fvar v)
    have hp : ND.Proof (q::Γ) q := assumption (by simp)
    let inc : ∀ p, p ∈ Γ → p ∈ q::Γ := fun p hp => List.mem_cons_of_mem q hp
    exact mulNewRecurrenceCase (E.weaken inc) top u c v g h base x y z (I.weaken inc)
      (andLeft hp) (andRight hp) (up hs q)

#print axioms mulRecurrenceExtensionAt

end M6.PA.RelationalSource.PairGraph
