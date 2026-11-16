module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRestrictionInside
public import M6PA.Calibration.RelationalMultiplicationRecurrenceInputs
@[expose] public section

namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult addPrefix mulPrefix
set_option maxHeartbeats 600000

def mulRestrictPrevious {Γ : List Form} (t g h base x y : Nat)
    (hr : ND.Proof Γ (graphRestriction (.fvar t) (.fvar g) (.fvar h)))
    (hi : ND.Proof Γ (inclusiveDomain (.fvar t) (.fvar x)))
    (hp : ND.Proof Γ (mulPrevious (.fvar g) (.fvar base) (.fvar x) (.fvar y))) :
    ND.Proof Γ (mulPrevious (.fvar h) (.fvar base) (.fvar x) (.fvar y)) := by
  apply exsElim hp
  let σ : Ordinal.Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0) ⋏ addResult (.bvar 0) (.fvar base) (.fvar y)
  let C := σ.free :: shifted Γ
  have hc : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0) ⋏
      addResult (.fvar 0) (.fvar (base+1)) (.fvar (y+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 ; dsimp [σ]; mulCompactSyntax
  have ii : ND.Proof C (inclusiveDomain (.fvar (t+1)) (.fvar (x+1))) := by
    convert up (shiftProof hi) σ.free using 1 <;> inclusiveRestrictionSyntax
  have he := restrictionIntro (t+1) (g+1) (h+1) (x+1) 0
    (up (graphRestrictionShift t g h hr) σ.free) (andLeft hc) ii
  have out := mulPreviousIntro (h+1) (base+1) (x+1) (y+1) 0 he (andRight hc)
  convert out using 1 <;> (dsimp [C,σ] <;> mulCompactSyntax)

def mulRestrictionRecurrenceAt {Γ : List Form} (E : FormulaEquality Γ) (t g h base i y j : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hr : ND.Proof Γ (graphRestriction (.fvar t) (.fvar g) (.fvar h)))
    (hc : ND.Proof Γ (mulRecurrence (.fvar g) (.fvar base)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar i) (.fvar y)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar j) (.fvar i))) :
    ND.Proof Γ (mulPrevious (.fvar h) (.fvar base) (.fvar j) (.fvar y)) := by
  have old := restrictionCases t g h i y hr he
  exact mulRestrictPrevious t g h base j y hr
    (restrictionPredecessorInside E t i j ht (andRight old) hs)
    (mulRecurrenceAt g base i y j hc (andLeft old) hs)

def mulRestrictionRecurrence {Γ : List Form} (E : FormulaEquality Γ) (t g h base : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hr : ND.Proof Γ (graphRestriction (.fvar t) (.fvar g) (.fvar h)))
    (hc : ND.Proof Γ (mulRecurrence (.fvar g) (.fvar base))) :
    ND.Proof Γ (mulRecurrence (.fvar h) (.fvar base)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  have tt := domainShift (t+1+1) (domainShift (t+1) (domainShift t ht))
  have rr := graphRestrictionShift (t+1+1) (g+1+1) (h+1+1)
    (graphRestrictionShift (t+1) (g+1) (h+1) (graphRestrictionShift t g h hr))
  have cc := mulRecurrenceShift (g+1+1) (base+1+1) (mulRecurrenceShift (g+1) (base+1) (mulRecurrenceShift g base hc))
  have result : ND.Proof (shifted (shifted (shifted Γ)))
      (sourceImply (edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 2))
        (mulPrevious (.fvar (h+1+1+1)) (.fvar (base+1+1+1)) (.fvar 0) (.fvar 1))) := by
    apply impIntro
    let q : Form := edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏ Ordinal.successor (.fvar 0) (.fvar 2)
    have hp : ND.Proof (q::shifted (shifted (shifted Γ))) q := assumption (by simp)
    let inc := fun p (hp : p ∈ shifted (shifted (shifted Γ))) => List.mem_cons_of_mem q hp
    exact mulRestrictionRecurrenceAt (E.shifted.shifted.shifted.weaken inc)
      (t+1+1+1) (g+1+1+1) (h+1+1+1) (base+1+1+1) 2 1 0
      (up tt q) (up rr q) (up cc q) (andLeft hp) (andRight hp)
  convert result using 1 ; mulCompactSyntax

#print axioms mulRestrictPrevious
#print axioms mulRestrictionRecurrenceAt
#print axioms mulRestrictionRecurrence
end M6.PA.RelationalSource.PairGraph
