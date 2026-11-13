module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationCompactSyntax
public import M6PA.Calibration.RelationalMultiplicationRecurrenceAt
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
set_option maxHeartbeats 600000
attribute [local irreducible] addResult addPrefix mulPrefix

def mulRecurrenceExtension {Γ : List Form} (E : FormulaEquality Γ)
    (top u c v g h base : Nat) (I : MulRecurrenceInputs Γ top u c v g h base) :
    ND.Proof Γ (mulRecurrence (.fvar h) (.fvar base)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  have III := I.shift.shift.shift
  have result : ND.Proof (shifted (shifted (shifted Γ)))
      (sourceImply (edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 2))
        (mulPrevious (.fvar (h+1+1+1)) (.fvar (base+1+1+1)) (.fvar 0) (.fvar 1))) := by
    apply impIntro
    let q : Form := edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 2)
    have hp : ND.Proof (q::shifted (shifted (shifted Γ))) q := assumption (by simp)
    let inc := fun p (hp : p ∈ shifted (shifted (shifted Γ))) => List.mem_cons_of_mem q hp
    exact mulRecurrenceExtensionAt (E.shifted.shifted.shifted.weaken inc)
      (top+1+1+1) (u+1+1+1) (c+1+1+1) (v+1+1+1) (g+1+1+1) (h+1+1+1) (base+1+1+1) 2 1 0
      (III.weaken inc) (andLeft hp) (andRight hp)
  convert result using 1 ; mulCompactSyntax

#print axioms mulRecurrenceExtension

end M6.PA.RelationalSource.PairGraph
