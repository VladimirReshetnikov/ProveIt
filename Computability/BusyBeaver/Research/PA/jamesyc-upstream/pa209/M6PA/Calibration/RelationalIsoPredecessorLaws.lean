module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoPredecessorTyped
public import M6PA.Calibration.RelationalGraphFunctionalExtension
@[expose] public section

/-! Functionality, injectivity, and order are inherited by the actual strict cut. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def predecessorGraphFunctional {Γ : List Form} (g h p : Nat)
    (hold : ND.Proof Γ (graphFunctional (.fvar g)))
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar p) (.fvar g) (.fvar h))) :
    ND.Proof Γ (graphFunctional (.fvar h)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  let premise : Form := edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏
    edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 0)
  have hp : ND.Proof (premise::shifted (shifted (shifted (Γ)))) premise := assumption (by simp)
  have rr := up (strictRestrictionShift (p+1+1) (g+1+1) (h+1+1) (strictRestrictionShift (p+1) (g+1) (h+1) (strictRestrictionShift (p) (g) (h) hr))) premise
  have ee := andLeft (strictCutCases (p+1+1+1) (g+1+1+1) (h+1+1+1) 2 1 rr (andLeft hp))
  have ff := andLeft (strictCutCases (p+1+1+1) (g+1+1+1) (h+1+1+1) 2 0 rr (andRight hp))
  have old := up (graphFunctionalShift (g+1+1) (graphFunctionalShift (g+1) (graphFunctionalShift (g) hold))) premise
  have out := graphFunctionalAt (g+1+1+1) 2 1 0 old ee ff
  convert impIntro out using 1 <;> (dsimp [premise] <;> isoSyntax)

def predecessorGraphInjective {Γ : List Form} (g h p : Nat)
    (hold : ND.Proof Γ (graphInjective (.fvar g)))
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar p) (.fvar g) (.fvar h))) :
    ND.Proof Γ (graphInjective (.fvar h)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  let premise : Form := edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 0) ⋏
    edge (.fvar (h+1+1+1)) (.fvar 1) (.fvar 0)
  have hp : ND.Proof (premise::shifted (shifted (shifted (Γ)))) premise := assumption (by simp)
  have rr := up (strictRestrictionShift (p+1+1) (g+1+1) (h+1+1) (strictRestrictionShift (p+1) (g+1) (h+1) (strictRestrictionShift (p) (g) (h) hr))) premise
  have ee := andLeft (strictCutCases (p+1+1+1) (g+1+1+1) (h+1+1+1) 2 0 rr (andLeft hp))
  have ff := andLeft (strictCutCases (p+1+1+1) (g+1+1+1) (h+1+1+1) 1 0 rr (andRight hp))
  have old := up (orderInjectiveShift (g+1+1) (orderInjectiveShift (g+1) (orderInjectiveShift (g) hold))) premise
  have out := orderInjectiveAt (g+1+1+1) 2 1 0 old ee ff
  convert impIntro out using 1 <;> (dsimp [premise] <;> isoSyntax)

def predecessorGraphOrder {Γ : List Form} (g h p : Nat)
    (hold : ND.Proof Γ (graphOrder (.fvar g)))
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar p) (.fvar g) (.fvar h))) :
    ND.Proof Γ (graphOrder (.fvar h)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  apply allIntro
  let premise : Form := edge (.fvar (h+1+1+1+1)) (.fvar 3) (.fvar 1) ⋏
    edge (.fvar (h+1+1+1+1)) (.fvar 2) (.fvar 0)
  have hp : ND.Proof (premise::shifted (shifted (shifted (shifted (Γ))))) premise := assumption (by simp)
  have rr := up (strictRestrictionShift (p+1+1+1) (g+1+1+1) (h+1+1+1) (strictRestrictionShift (p+1+1) (g+1+1) (h+1+1) (strictRestrictionShift (p+1) (g+1) (h+1) (strictRestrictionShift (p) (g) (h) hr)))) premise
  have ee := andLeft (strictCutCases (p+1+1+1+1) (g+1+1+1+1) (h+1+1+1+1) 3 1 rr (andLeft hp))
  have ff := andLeft (strictCutCases (p+1+1+1+1) (g+1+1+1+1) (h+1+1+1+1) 2 0 rr (andRight hp))
  have old := up (orderOrderShift (g+1+1+1) (orderOrderShift (g+1+1) (orderOrderShift (g+1) (orderOrderShift (g) hold)))) premise
  have out := orderOrderAt (g+1+1+1+1) 3 2 1 0 old ee ff
  convert impIntro out using 1 <;> (dsimp [premise] <;> isoSyntax)

#print axioms predecessorGraphFunctional
#print axioms predecessorGraphInjective
#print axioms predecessorGraphOrder
end M6.PA.RelationalSource.PairGraph
