module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphRestrictionInclusiveRules
public import M6PA.Calibration.RelationalGraphOperations
@[expose] public section

/-! Restriction preserves the functional and full ordinal-range trace clauses. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def restrictionFunctional {Γ : List Form} (top g h : Nat)
    (hr : ND.Proof Γ (graphRestriction (.fvar top) (.fvar g) (.fvar h)))
    (hf : ND.Proof Γ (graphFunctional (.fvar g))) :
    ND.Proof Γ (graphFunctional (.fvar h)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  have rr := graphRestrictionShift (top+1+1) (g+1+1) (h+1+1)
    (graphRestrictionShift (top+1) (g+1) (h+1) (graphRestrictionShift top g h hr))
  have ff : ND.Proof (shifted (shifted (shifted Γ))) (graphFunctional (.fvar (g+1+1+1))) := by
    convert shiftProof (shiftProof (shiftProof hf)) using 1 <;> inclusiveRestrictionSyntax
  let premise : Form := edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏
    edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 0)
  have hh : ND.Proof (premise :: shifted (shifted (shifted Γ))) premise := assumption (by simp)
  have left := andLeft (restrictionCases (top+1+1+1) (g+1+1+1) (h+1+1+1) 2 1
    (up rr premise) (andLeft hh))
  have right := andLeft (restrictionCases (top+1+1+1) (g+1+1+1) (h+1+1+1) 2 0
    (up rr premise) (andRight hh))
  have out := graphFunctionalAt (g+1+1+1) 2 1 0 (up ff premise) left right
  convert impIntro out using 1 <;> (dsimp [premise] <;> inclusiveRestrictionSyntax)

def restrictionRange {Γ : List Form} (top g h : Nat)
    (hr : ND.Proof Γ (graphRestriction (.fvar top) (.fvar g) (.fvar h)))
    (hg : ND.Proof Γ (graphRange (.fvar g))) :
    ND.Proof Γ (graphRange (.fvar h)) := by
  apply allIntro
  apply allIntro
  have rr := graphRestrictionShift (top+1) (g+1) (h+1) (graphRestrictionShift top g h hr)
  have gg : ND.Proof (shifted (shifted Γ)) (graphRange (.fvar (g+1+1))) := by
    convert shiftProof (shiftProof hg) using 1 <;> inclusiveRestrictionSyntax
  let premise : Form := edge (.fvar (h+1+1)) (.fvar 1) (.fvar 0)
  have hh : ND.Proof (premise :: shifted (shifted Γ)) premise := assumption (by simp)
  have old := andLeft (restrictionCases (top+1+1) (g+1+1) (h+1+1) 1 0 (up rr premise) hh)
  have out := graphRangeAt (g+1+1) 1 0 (up gg premise) old
  convert impIntro out using 1 <;> (dsimp [premise] <;> inclusiveRestrictionSyntax)

#print axioms restrictionFunctional
#print axioms restrictionRange
end M6.PA.RelationalSource.PairGraph
